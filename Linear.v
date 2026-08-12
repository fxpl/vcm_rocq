From Vcm Require Import Common.
From Vcm Require Import Graph.

(* ------------------------------------------------------------------------ *)
(* The Linear model: SharedMemory (see SharedMemory.v) re-expressed with a  *)
(* commit graph, using a SINGLE global branch shared by every thread, lock  *)
(* and volatile variable (a specialisation of Branching.v's per-owner       *)
(* branches down to one).                                                   *)
(*                                                                          *)
(* Memory is a graph of immutable commits, each holding a diff; the whole   *)
(* graph forms one chain, and its head is the global branch everyone        *)
(* synchronises against ([is_global_head] in Graph.v).                      *)
(*                                                                          *)
(*   - a thread stages its writes locally (in a diff) until it next         *)
(*     synchronises, and reads either its own staged value or the latest    *)
(*     value visible at its own commit;                                     *)
(*   - synchronising is a PULL, which here is just a fast-forward (a        *)
(*     thread is always *behind* the global head on the one chain, so no    *)
(*     merge is ever needed): the thread's commit pointer simply moves to   *)
(*     the head after checking for conflict;                                *)
(*   - a synchronising WRITE additionally PUSHES: it commits the thread's   *)
(*     staged diff *onto the global head* (advancing it), after pulling     *)
(*     and checking for conflict;                                           *)
(*   - locks carry no commit of their own here (unlike Branching): since    *)
(*     there is only one branch, lock/unlock synchronise through it         *)
(*     directly (lock = pull, unlock = push), so a lock is just free/held.  *)
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

Definition cfg : Type := threads * graph * locks.

(* [commit]: flush thread [t]'s diff onto the global head [g], producing the
   fresh commit [g'] which becomes both [t]'s commit and the new global head;
   the diff is cleared. *)
Definition global_commit (t : tid) (g g' : commit) (T : threads) (G : graph)
    : threads * graph :=
  let '(st, e, d, _) := T[t] in
  (T[t := (st, e, empty_diff, g')],
   graph_commit G g g' d).

(* A thread at commit [c] may commit (or fast-forward over) its diff [d]
   only if none of the variables it writes were written between [c] and the
   global head [g] -- i.e. by a commit it has not yet observed. *)
Definition lin_conflict_free (d : diff) (c g : commit) (G : graph) : Prop :=
  dom d \# change_set G c g.

(* Locks default to free: a never-acquired lock reads as [ls_free], the same
   as an explicitly-freed one (mirrors [SharedMemory.lock_read]). *)
Definition lock_read (L : locks) (l : lid) : lock_state :=
  read_default inhab_lock_state ls_free L l.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G L t e d c g,
    binds T t (state_new, e, d, c) ->
    (* the new thread starts at the current global head *)
    is_global_head G g ->
    step (T, G, L) (T[t := (state_running, e, d, g)], G, L)
| StepEnd : forall T T' G G' L t r d c g g',
    binds T t (state_running, te_ret r, d, c) ->
    is_global_head G g ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step (T, G, L) (T'[t := (state_terminated, te_ret r, empty, g')], G', L)
| StepReadLocal : forall T G L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    binds d x v ->
    step (T, G, L) (T[t := (state_running, K (ret_val v), d, c)], G, L)
| StepReadGlobal : forall T G L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    x \notindom d ->
    (* a thread reads the latest value visible at its own commit *)
    is_latest_value G c x v ->
    step (T, G, L) (T[t := (state_running, K (ret_val v), d, c)], G, L)
| StepReadVolatile : forall T G L t e d c K x v g,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    is_global_head G g ->
    (* reading a volatile is a *pull*: check conflict-freedom and fast-forward
       to the current global head [g] (a volatile is never left pending in
       [d] -- every write to one is immediately pushed, see
       [StepWriteVolatile] -- so there is no local case to consider), then
       read the latest value visible there. *)
    lin_conflict_free d c g G ->
    is_latest_value G g x v ->
    step (T, G, L) (T[t := (state_running, K (ret_val v), d, g)], G, L)
| StepWrite : forall T G L t e d c K x v,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \notin Volatiles ->
    step (T, G, L) (T[t := (state_running, K void, d[x := v], c)], G, L)
| StepWriteVolatile : forall T T' G G' L t e d c K x v g g',
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    is_global_head G g ->
    (* writing a volatile is a *pull, then push*: the current diff
       (with the write itself folded in, so a write-write race on [x]
       against the global head is caught too, not just a race on the
       rest of the diff) is checked for conflict-freedom against the
       current global head [g], then immediately committed onto it
       (flushing the whole diff, exactly like [StepEnd]/[StepRelease]
       already do), producing a fresh commit [g'] that becomes both
       the thread's commit and the new global head. *)
    lin_conflict_free d[x := v] c g G ->
    commit_fresh G g' ->
    global_commit t g g' (T[t := (state_running, te_exp e, d[x := v], c)]) G = (T', G') ->
    step (T, G, L) (T'[t := (state_running, K void, empty, g')], G', L)
| StepSpawn : forall T T' G G' L t (t' : tid) e d c K e' g g',
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    is_global_head G g ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    (* the spawned thread [t']'s commit is irrelevant (overwritten
       when it starts), so we just leave it at the fresh commit
       [g'] *)
    global_commit t g g' (T[t := (state_running, K t', d, c)][t' := (state_new, te_exp e', empty, g')]) G = (T', G') ->
    step (T, G, L) (T', G', L)
| StepJoin : forall T G L t t' e d c c' K r g,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    is_global_head G g ->
    lin_conflict_free d c g G ->
    (* the joined thread has already pushed (at its StepEnd); just fast-forward *)
    step (T, G, L) (T[t := (state_running, K r, d, g)], G, L)
| StepLock : forall T G L t e d c K l g,
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = ls_free ->
    is_global_head G g ->
    lin_conflict_free d c g G ->
    step (T, G, L) (T[t := (state_running, K void, d, g)], G, L[l := ls_held t])
| StepRelease : forall T T' G G' L t e d c K l g g',
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_unlock l) ->
    lock_read L l = ls_held t ->
    is_global_head G g ->
    lin_conflict_free d c g G ->
    commit_fresh G g' ->
    global_commit t g g' T G = (T', G') ->
    step (T, G, L) (T'[t := (state_running, K void, empty, g')], G', L[l := ls_free])
.

Hint Constructors step Linear.step : vcm.