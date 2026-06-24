From Vcm Require Import Common.

Definition thread := (thread_state * thread_exp)%type.

Definition threads := (map tid thread).
Definition heap := map var val.
Definition locks := map lid lock_state.
Definition cfg := (threads * heap * locks)%type.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T H L t e,
    binds T t (state_new, e) ->
    step (T, H, L) (T[t := (state_running, e)], H, L)
| StepEnd : forall (T : threads) H L t r,
    binds T t (state_running, te_ret r) ->
    step (T, H, L) (T[t := (state_terminated, te_ret r)], H, L)
| StepRead : forall (T : threads) H L t e K x v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read x) ->
    binds H x v ->
    step (T, H, L) (T[t := (state_running, te_exp (K (ret_val v)))], H, L)
| StepWrite : forall (T : threads) (H : heap) L t e K x v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write x v) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H[x := v], L)
| StepSpawn : forall (T : threads) H L (t t' : tid) e K e',
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step (T, H, L) (T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')], H, L)
| StepJoin : forall (T : threads) H L t t' e K r,
    (* This means multiple threads can join the same thread *)
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step (T, H, L) (T[t := (state_running, te_exp (K r))], H, L)
| StepLock : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    (* a free lock, or one that has never been acquired (hence not in [L]) *)
    (binds L l ls_free \/ l \notindom L) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_held t])
| StepRelease : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_free])
.
