From Vcm Require Import Common.
From Vcm Require Import Graph.

(* ------------------------------------------------------------------------ *)
(* The Branching model: SharedMemory (see SharedMemory.v) re-expressed with *)
(* a commit graph, so that each thread's view of memory is explicit.        *)
(*                                                                          *)
(* Instead of one global heap, memory is a graph of immutable commits, each *)
(* holding a diff (the variables it changed and their new values). Every    *)
(* thread, lock and volatile variable owns a branch: a pointer to the       *)
(* commit representing what it has last observed.                           *)
(*                                                                          *)
(*   - a thread stages its writes locally (in a diff) until it next         *)
(*     synchronises, and reads either its own staged value or the latest    *)
(*     value visible at its own commit;                                     *)
(*   - synchronising with a thread, lock or a volatile variable is a PULL,  *)
(*     PUSH, or for a volatile write both:                                  *)
(*       * pull merges the other party's branch into the thread's own       *)
(*         (a fresh commit with both as parents), so the thread now sees    *)
(*         everything the thread/lock/volatile has seen;                    *)
(*       * push commits the thread's staged diff (a fresh commit with the   *)
(*         thread's branch as parent) and hands that fresh commit to the    *)
(*         thread/lock/volatile as its new branch;                          *)
(*   - a commit may only be created when doing so is CONFLICT-FREE: no      *)
(*     variable it touches may have changed on a branch the thread has not  *)
(*     yet observed. This only needs checking on pulling; a push does not   *)
(*     affect another thread until it pulls.                                *)
(*                                                                          *)
(* Linear.v specialises this to a single shared branch instead of one per   *)
(* thread/lock/volatile.                                                    *)
(* ------------------------------------------------------------------------ *)

Definition thread := (thread_state * thread_exp * diff * commit)%type.

Instance inhab_thread : Inhab thread.
  forwards* Hexp: inhab_exp.
  destruct Hexp as [[e _]].
  constructor. exists* (state_new, te_exp e, (empty : diff), 0).
Qed.

Definition threads := map tid thread.

Definition locks := map lid (lock_state * commit).

Instance inhab_lock : Inhab (lock_state * commit).
  constructor. exists* (ls_free, 0).
Qed.

(* Every volatile variable carries a commit, just like a lock does -- the
   commit at which it was last read or written, so that a later access can
   [pull]/[push] against it exactly as [pull_lock]/[push_lock] already do for
   locks. *)
Definition volatiles := map var commit.

Definition cfg : Type := threads * graph * locks * volatiles.

(* Locks default to free at the root commit: a never-acquired lock reads as
   [(ls_free, root_commit)], the same as an explicitly-freed one whose
   critical section has no prior history to merge with (mirrors
   [SharedMemory.lock_read] / [Linear.lock_read]). *)
Definition lock_read (L : locks) (l : lid) : (lock_state * commit) :=
  read_default inhab_lock (ls_free, root_commit) L l.

(* A never-touched volatile defaults to [root_commit], mirroring [lock_read]. *)
Definition vc_read (V : volatiles) (x : var) : commit :=
  read_default _ root_commit V x.

(* TODO: change h_new to c_new *)
Definition do_commit (t : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(_, e, d, h) := T[t] in
  (T[t := (state_running, e, empty, h_new)],
   graph_commit G h h_new d)
.

Definition push_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(T', G') := do_commit t h_new T G in
  let '(ts, e, d, _) := T'[t'] in
  (T'[t' := (ts, e, d, h_new)], G').

Definition push_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph * locks :=
  let '(T', G') := do_commit t h_new T G in
  let '(ls, _) := L[l] in
  (T', G', L[l := (ls, h_new)]).

Definition do_merge (t : tid) (h h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(ts, e, d, h_t) := T[t] in
  (T[t := (ts, e, d, h_new)], graph_merge G h h_t h_new).

Definition pull_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
    let '(_, _, _, h') := T[t'] in
    do_merge t h' h_new T G.

Definition pull_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph :=
  let '(_, h) := lock_read L l in
  do_merge t h h_new T G.

(* Reading a volatile is a *pull*: merge its stored commit into the thread's
   own branch, exactly like [pull_lock]. *)
Definition pull_volatile (t : tid) (x : var) (h_new : commit)
    (T : threads) (G : graph) (V : volatiles)
    : threads * graph :=
  let h := vc_read V x in
  do_merge t h h_new T G.

(* Writing a volatile *pushes*: commit the thread's diff (folding in the new
   write) and record the fresh commit as [x]'s new stored commit, exactly
   like [push_lock]. *)
Definition push_volatile (t : tid) (x : var) (h_new : commit)
    (T : threads) (G : graph) (V : volatiles)
    : threads * graph * volatiles :=
  let '(T', G') := do_commit t h_new T G in
  (T', G', V[x := h_new]).

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G L V t e d h,
    binds T t (state_new, e, d, h) ->
    step (T, G, L, V) (T[t := (state_running, e, d, h)], G, L, V)
| StepEnd : forall T T' G G' L V t r d h h',
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh G h' ->
    do_commit t h' T G = (T', G') ->
    step (T, G, L, V) (T'[t := (state_terminated, te_ret r, empty, h')], G', L, V)
| StepReadLocal : forall T G L V t e d h K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    binds d x v ->
    step (T, G, L, V) (T[t := (state_running, K (ret_val v), d, h)], G, L, V)
| StepReadGlobal : forall T G L V t e d h K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read x) ->
    x \notin Volatiles ->
    x \notindom d ->
    is_latest_value G h x v ->
    step (T, G, L, V) (T[t := (state_running, K (ret_val v), d, h)], G, L, V)
| StepReadVolatile : forall T T' G G' L V t e d h h'' K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    conflict_free_merge d h (vc_read V x) G ->
    commit_fresh G h'' ->
    pull_volatile t x h'' T G V = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    (* the value visible after pulling in [x]'s stored commit *)
    is_latest_value G' h'' x v ->
    step (T, G, L, V) (T'[t := (state_running, K (ret_val v), d, h'')], G', L, V)
| StepWrite : forall T G L V t e d h K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write x v) ->
    x \notin Volatiles ->
    step (T, G, L, V) (T[t := (state_running, K void, d[x := v], h)], G, L, V)
| StepWriteVolatile : forall T T' T'' G G' G'' L V V' t e d h h' h'' K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    conflict_free_merge d[x := v] h (vc_read V x) G ->
    commit_fresh G h' ->
    pull_volatile t x h' T G V = (T', G') ->
    binds T' t (state_running, te_exp e, d, h') ->
    commit_fresh G' h'' ->
    push_volatile t x h'' (T'[t := (state_running, te_exp e, d[x := v], h')]) G' V = (T'', G'', V') ->
    step (T, G, L, V) (T''[t := (state_running, K void, empty, h'')], G'', L, V')
 | StepSpawn : forall T T' G G' L V t (t' : tid) e d h h' K e',
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    commit_fresh G h' ->
    push_thread t t' h' (T[t := (state_running, K t', d, h)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step (T, G, L, V) (T', G', L, V)
| StepJoin : forall T T' G G' L V t t' e d h h' h'' K r,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_thread t t' h'' T G = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L, V) (T'[t := (state_running, K r, d, h'')], G', L, V)
| StepLock : forall T T' G G' L V t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = (ls_free, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_lock t l h'' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L, V) (T'[t := (state_running, K void, d, h'')], G', L[l := (ls_held t, h')], V)
| StepRelease : forall T T' G G' (L L' : locks) V t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h') ->
    commit_fresh G h'' ->
    push_lock t l h'' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h'') ->
    step (T, G, L, V) (T'[t := (state_running, K void, empty, h'')], G', L'[l := (ls_free, h'')], V)
(* A failed conflict check does not stop the semantics: the thread receives the
   exception [ret_race] instead of the result of the operation, and keeps its
   staging area and commit. The commit graph, locks and volatiles do not
   change, and no operation takes place (the target thread is not consumed, the
   lock is not acquired, the volatile is neither read nor written). *)
| StepReadVolatileConflict : forall T G L V t e d h K x,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    ~ conflict_free_merge d h (vc_read V x) G ->
    step (T, G, L, V) (T[t := (state_running, K ret_race, d, h)], G, L, V)
| StepWriteVolatileConflict : forall T G L V t e d h K x v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    ~ conflict_free_merge d[x := v] h (vc_read V x) G ->
    step (T, G, L, V) (T[t := (state_running, K ret_race, d, h)], G, L, V)
| StepJoinConflict : forall T G L V t t' e d h h' K r,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    ~ conflict_free_merge d h h' G ->
    step (T, G, L, V) (T[t := (state_running, K ret_race, d, h)], G, L, V)
| StepLockConflict : forall T G L V t e d h h' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = (ls_free, h') ->
    ~ conflict_free_merge d h h' G ->
    step (T, G, L, V) (T[t := (state_running, K ret_race, d, h)], G, L, V)
.
