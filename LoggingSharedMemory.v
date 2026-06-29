From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.

(* Import FMap. *)
Import SharedMemory.
Import Log.
Import LogFacts.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      (* Spawned and intited threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root <-> t2 \indom T)
      /\
      (* Spawned and inited threads that have not started are new *)
      (forall t2,
          ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~mem (event_start t2) log <-> exists e, binds T t2 (state_new, e))
      /\
      (* Ended threads are ended *)
      (forall t,
          mem (event_end t) log <-> exists e, binds T t ((state_terminated, e)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e, binds T t (state_running, e))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> binds L l (ls_held t))
      /\
      (* A lock is free exactly when its last touch is an unlock.  A never-touched
         lock is not in [L] at all (so neither this nor the locked clause binds it). *)
      (forall l,
          (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* The value of each variable is its latest write *)
      (forall x v,
          (exists t log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t x v) <-> binds H x v)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T H L t e log,
    binds T t (state_new, e) ->
    step ((T, H, L), log) ((T[t := (state_running, e)], H, L), log & event_start t)
| StepEnd : forall (T : threads) H L t r log,
    binds T t (state_running, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_terminated, te_ret r)], H, L), log & event_end t)
| StepRead : forall (T : threads) H L t e K x v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read x) ->
    binds H x v ->
    step ((T, H, L), log) ((T[t := (state_running, K (ret_val v))], H, L), log & event_read t x v)
| StepWrite : forall (T : threads) (H : heap) L t e K x v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write x v) ->
    step ((T, H, L), log) ((T[t := (state_running, K void)], H[x := v], L), log & event_write t x v)
| StepSpawn : forall (T : threads) H L t (t' : tid) e K e' log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step ((T, H, L), log) ((T[t := (state_running, K t')][t' := (state_new, te_exp e')], H, L), log & event_spawn t t')
| StepJoin : forall (T : threads) H L t t' e K r log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_running, K r)], H, L), log & event_join t t')
| StepLock : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    (binds L l ls_free \/ l \notindom L) ->
    step ((T, H, L), log) ((T[t := (state_running, K void)], H, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step ((T, H, L), log) ((T[t := (state_running, K void)], H, L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step SharedMemory.step : vcm.
