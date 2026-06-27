From Vcm Require Import Common.
From Vcm Require Import Graph.

(* ------------------------------------------------------------------------ *)
(* The Linear model, re-expressed with the commit-graph machinery.          *)
(*                                                                          *)
(* It is the Branching model specialised to a SINGLE global branch: instead *)
(* of every thread (and lock critical section) owning a branch of its own,  *)
(* they all synchronise against one shared commit chain.  The configuration *)
(* therefore carries a distinguished [global] commit -- the head of that    *)
(* single branch -- alongside the graph.                                    *)
(*                                                                          *)
(* Differences from Branching.v:                                            *)
(*   - [pull] is a fast-forward, not a [graph_merge]: a thread is always    *)
(*     *behind* the global head (an ancestor of it on the one chain), so    *)
(*     synchronising just moves its commit pointer to the head.  No new     *)
(*     commit is created.                                                    *)
(*   - [push] commits a thread's diff *onto the global head* (advancing it), *)
(*     rather than onto the thread's own commit.  This is where the         *)
(*     write-write conflict check lives: a thread may only commit if none of *)
(*     the variables it writes were written by a commit it has not yet seen. *)
(*   - locks no longer carry a commit: lock/unlock synchronise through the   *)
(*     global branch (lock = pull, unlock = push), so a lock is just         *)
(*     free / held.                                                          *)
(*   - reads (StepReadGlobal) observe the global head, not the thread's own  *)
(*     commit -- the linear model has a single total order of writes.        *)
(* ------------------------------------------------------------------------ *)

Definition thread := (thread_state * thread_exp * diff * commit)%type.

Instance inhab_thread : Inhab thread.
  forwards* Hexp: inhab_exp.
  destruct Hexp as [[e _]].
  constructor. exists* (state_new, te_exp e, (empty : diff), 0).
Qed.

Definition threads := map tid thread.

(* Locks carry no version: synchronisation goes through the global branch. *)
Definition locks := map lid lock_state.

(* The third component is the [global] commit: the head of the single branch. *)
Definition cfg : Type := threads * graph * commit * locks.

(* [commit]: flush thread [t]'s diff onto the global head [g], producing the
   fresh commit [g'] which becomes both [t]'s commit and the new global head;
   the diff is cleared. *)
Definition global_commit (t : tid) (g g' : commit) (T : threads) (G : graph)
    : threads * graph :=
  let '(st, e, d, _) := T[t] in
  (T[t := (st, e, empty_diff, g')],
   graph_commit G g g' d).

Definition push_thread (t t' : tid) (g g' : commit) (T : threads) (G : graph) :=
  let '(T', G') := global_commit t g g' T G in
  let '(ts, e, d, _) := T'[t'] in
  (T'[t' := (ts, e, d, g')], G').


(* A thread at commit [c] may commit (or fast-forward over) its diff [d]
   only if none of the variables it writes were written between [c] and the
   global head [g] -- i.e. by a commit it has not yet observed. *)
Definition lin_conflict_free (d : diff) (c g : commit) (G : graph) : Prop :=
  dom d \# change_set G c g.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G g L t e d c,
    binds T t (state_new, e, d, c) ->
    (* a starting thread fast-forwards to the global head (this is
    different from the paper where it keeps the commit it got from
    its spawning thread) *)
    step (T, G, g, L) (T[t := (state_running, e, d, g)], G, g, L)
| StepEnd : forall T T' G G' g g' L t r d c,
    binds T t (state_running, te_ret r, d, c) ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step (T, G, g, L) (T'[t := (state_terminated, te_ret r, empty, g')], G', g', L)
| StepReadLocal : forall T G g L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    binds d x v ->
    step (T, G, g, L) (T[t := (state_running, K (ret_val v), d, c)], G, g, L)
| StepReadGlobal : forall T G g L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notindom d ->
    (* a thread reads the latest value visible at its own commit *)
    is_latest_value G c x v ->
    step (T, G, g, L) (T[t := (state_running, K (ret_val v), d, c)], G, g, L)
| StepWrite : forall T G g L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    step (T, G, g, L) (T[t := (state_running, K void, d[x := v], c)], G, g, L)
| StepSpawn : forall T T' G G' g g' L t (t' : tid) e d c K e',
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    push_thread t t' g g' (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step (T, G, g, L) (T', G', g', L)
| StepJoin : forall T G g L t t' e d c c' K r,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    lin_conflict_free d c g G ->
    (* the joined thread has already pushed (at its StepEnd); just fast-forward *)
    step (T, G, g, L) (T[t := (state_running, K r, d, g)], G, g, L)
| StepLock : forall T G g L t e d c K l,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free \/ l \notindom L ->
    lin_conflict_free d c g G ->
    step (T, G, g, L) (T[t := (state_running, K void, d, g)], G, g, L[l := ls_held t])
| StepRelease : forall T T' G G' g g' L t e d c K l,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step (T, G, g, L) (T'[t := (state_running, K void, empty, g')], G', g', L[l := ls_free])
.

Hint Constructors step Linear.step : vcm.