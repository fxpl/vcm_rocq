From Vcm Require Import Common.

(* Import FMap. *)

Definition thread := (thread_state * thread_exp)%type.

(* TODO: Somewhere along the line, rew_set stopped working for
updated threads (I think it used to work!?). Turning this from a
Definition into a Notation seemed to work, but I don't like it...
*)
Definition threads := (map tid thread).

(*
Instance threads_dom_inst : BagDom threads (set tid) := @LibMap.dom_inst tid thread.

Instance threads_union_inst : BagUnion threads := @union_inst tid thread.
*)

(* Needed for some reason (to let typeclass instantiation look
inside the definition?) *)
(*
Instance in_inst : BagIn tid (set tid).
  constructor. rapply (@in_impl tid).
Defined.
*)

(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Defined.
*)

(* Not sure why these are needed for fmap *)
(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Qed.

Instance threads_binds_inst : BagBinds tid thread threads.
  constructor. rapply (@binds_impl tid thread).
Qed.
*)
Definition heap := map loc val.

(*
Instance heap_binds_inst : BagBinds loc val heap.
  constructor. rapply (@binds_impl loc val).
Qed.
*)
Definition locks := map lid lock_state.

(*
Instance locks_binds_inst : BagBinds lid lock_state locks.
  constructor. rapply (@binds_impl lid lock_state).
Qed.
*)

Definition cfg := (threads * heap * locks)%type.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T H L t e,
    binds T t (state_new, e) ->
    step (T, H, L) (T[t := (state_running, e)], H, L)
| StepEnd : forall (T : threads) H L t r,
    binds T t (state_running, te_ret r) ->
    step (T, H, L) (T[t := (state_terminated, te_ret r)], H, L)
| StepRead : forall (T : threads) H L t e K i v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read i) ->
    binds H i v ->
    step (T, H, L) (T[t := (state_running, te_exp (K (ret_val v)))], H, L)
| StepWrite : forall (T : threads) (H : heap) L t e K i v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write i v) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H[i := v], L)
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
    binds L l ls_free ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_held t])
| StepRelease : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_free])
.

