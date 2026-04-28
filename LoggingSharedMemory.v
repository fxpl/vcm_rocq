From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.

(* Import FMap. *)
Import SharedMemory.
Import Log.

(* TODO: Do we need something about reads? Is it enough to say
that a location exists as soon as it has been written to? *)
Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log) <-> exists e, binds T t2 (state_new, e))
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
      (* Unlocked locks are unlocked TODO: Could be empty if no lock yet *)
      (forall l,
          (log = nil \/ exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* The value of each location is its latest write *)
      (forall i v,
          (exists t log', LibList.filter (fun e => writes_location i e) log = log' & event_write t i v) <-> binds H i v)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T H L t e log,
    binds T t (state_new, e) ->
    step ((T, H, L), log) ((T[t := (state_running, e)], H, L), log & event_start t)
| StepEnd : forall (T : threads) H L t r log,
    binds T t (state_running, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_terminated, te_ret r)], H, L), log & event_end t)
| StepRead : forall (T : threads) H L t e K i v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read i) ->
    binds H i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)))], H, L), log & event_read t i v)
| StepWrite : forall (T : threads) (H : heap) L t e K i v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write i v) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H[i := v], L), log & event_write t i v)
| StepSpawn : forall (T : threads) H L t (t' : tid) e K e' log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')], H, L), log & event_spawn t t')
| StepJoin : forall (T : threads) H L t t' e K r log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K r))], H, L), log & event_join t t')
| StepLock : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H, L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step SharedMemory.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> SharedMemory.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepRead.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - destruct Hdesc as (_ & Hdstart & _).
    asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t) log /\ ~mem (event_start t) log).
    { apply* Hdstart. }
    splits.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn.
      exists t1'.
      rew_listx. rew_listx in Hmem'.
      branches; autos.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_list~.
      * intros contra. apply~ (Hustart l1 l2' t0).
        rew_listx. rew_listx in contra.
        branches; autos. inverts H0.
        false Hnmem. rew_listx~.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra.
      branches; autos.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      inverts* contra.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Heq <- Hneq.
      forwards* [(<- & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      rew_listx. splits*.
      simpl. intros ->.
      forwards~ Hmem': (Hstart l1 l2' (event_end t0) t0).
      false Hnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Defined.
*)

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    splits.
    + intros.
      replaces ((dom (update T t (pair state_running e)))) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set.
      splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T).
        { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + intros. splits.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. rew_listx in *. splits*. }
        exists e'.
        apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~ mem (event_start t2) log).
        { apply Hdstart. exists e'. forwards~: binds_update_neq_inv Hbinds. }
        exists. rew_listx. splits*.
    + intros. splits.
      * introv Hmem.
        rew_listx in Hmem. branches; [|congruence].
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'.
        apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t0 <> t).
        { introv ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ : binds_update_neq_inv Hbinds.
        rew_listx. left.
        apply* Hdend.
    + intros t0. splits.
      * introv (Hmem & Hnmem).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists e. apply binds_update_same.
        -- rew_listx in Hmem.
           branches; autos.
           rew_listx in Hnmem.
           asserts (e' & Hbinds) : (exists e, binds T t0 (state_running, e)).
           { apply~ Hdrunning. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           inverts Hbinds.
           rew_listx. splits~.
           intros contra. branches~.
           apply Hdend in H0 as (e' & Hbinds).
           forwards*: binds_inj.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
            asserts (Hmem & Hnmem): (mem (event_start t0) log /\
              ~ mem (event_end t0) log).
           { apply* Hdrunning. }
           rew_listx. splits*.
    + intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + intros l.
      rew_listx. cases_if~. rew_list.
      splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~.
        apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst. (* Step is not preserving wf_log (unlocked an already free lock) *) admit.
    + intros l. rew_listx. cases_if~. rew_list.
      apply Hdwrite.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

