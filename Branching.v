From Vcm Require Import Common.
From Vcm Require Import Graph.

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

Definition cfg : Type := threads * graph * locks.

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
  let '(_, h) := L[l] in
  do_merge t h h_new T G.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G L t e d h,
    binds T t (state_new, e, d, h) ->
    step (T, G, L) (T[t := (state_running, e, d, h)], G, L)
| StepEnd : forall T T' G G' L t r d h h',
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh G h' ->
    do_commit t h' T G = (T', G') ->
    step (T, G, L) (T'[t := (state_terminated, te_ret r, empty, h')], G', L)
| StepReadLocal : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    binds d i v ->
    step (T, G, L) (T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L)
| StepReadGlobal : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    i \notindom d ->
    is_latest_value G h i v ->
    step (T, G, L) (T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L)
| StepWrite : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write i v) ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), d[i := v], h)], G, L)
 | StepSpawn : forall T T' G G' L t (t' : tid) e d h h' K e',
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    commit_fresh G h' ->
    push_thread t t' h' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step (T, G, L) (T', G', L)
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_thread t t' h'' T G = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K r), d, h'')], G', L)
| StepLock : forall T T' G G' L t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_lock t l h'' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K void), d, h'')], G', L[l := (ls_held t, h')])
| StepLockFresh : forall T G L t e d h K l,
    (* A never-acquired lock has no prior critical section to merge with. *)
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    l \notindom L ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), d, h)], G, L[l := (ls_held t, h)])
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h') ->
    commit_fresh G h'' ->
    push_lock t l h'' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K void), empty, h'')], G', L'[l := (ls_free, h'')])
.
