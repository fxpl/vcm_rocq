From Vcm Require Import Common.

(* ------------------------------------------------------------------------ *)
(* The SharedMemory model: sequentially consistent threads communicating    *)
(* through one global heap.                                                 *)
(*                                                                          *)
(* Every read sees the single most recently written value, and every write  *)
(* updates it immediately and globally -- there is no notion of a thread's  *)
(* own view of memory diverging from anyone else's. This is the reference   *)
(* semantics that the commit-graph models (Branching.v, Linear.v) are built *)
(* to be equivalent to under a conflict-freedom side condition; see         *)
(* BranchingEquiv.v / LinearEquiv.v.                                        *)
(*                                                                          *)
(* Locks are a plain free/held flag with no history attached ([lock_read]   *)
(* below); spawning, joining and returning behave as expected.              *)
(* ------------------------------------------------------------------------ *)

Definition thread := (thread_state * thread_exp)%type.

Definition threads := (map tid thread).
Definition heap := map var val.
Definition locks := map lid lock_state.
Definition cfg := (threads * heap * locks)%type.

(* Locks default to free: a never-acquired lock reads as [ls_free], the same
   as an explicitly-freed one. This makes [lock_read] a total read, unlike
   [Inhab]'s opaque [arbitrary], so it can be shown equal to [ls_free] when
   the lock is unbound ([read_default_notindom]). *)
Definition lock_read (L : locks) (l : lid) : lock_state :=
  read_default inhab_lock_state ls_free L l.

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
    step (T, H, L) (T[t := (state_running, K (ret_val v))], H, L)
| StepWrite : forall (T : threads) (H : heap) L t e K x v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write x v) ->
    step (T, H, L) (T[t := (state_running, K void)], H[x := v], L)
| StepSpawn : forall (T : threads) H L (t t' : tid) e K e',
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step (T, H, L) (T[t := (state_running, K t')][t' := (state_new, te_exp e')], H, L)
| StepJoin : forall (T : threads) H L t t' e K r,
    (* This means multiple threads can join the same thread *)
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step (T, H, L) (T[t := (state_running, K r)], H, L)
| StepLock : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    lock_read L l = ls_free ->
    step (T, H, L) (T[t := (state_running, K void)], H, L[l := ls_held t])
| StepRelease : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    lock_read L l = ls_held t ->
    step (T, H, L) (T[t := (state_running, K void)], H, L[l := ls_free])
.
