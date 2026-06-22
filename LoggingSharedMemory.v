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
      (* Unlocked locks are unlocked or untouched *)
      (forall l,
          (* TODO: Shouldn't be log = nil, but filter ... = nil *)
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
  - (* StepEnd: log' = log & event_end t *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Unique spawns: new event is not a spawn *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + (* Unique starts: new event is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: new event is event_end t *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_list. exact Henmem.
      * intros contra. apply~ (Huend l1 l2' t0).
        rew_listx. rew_listx in contra.
        branches; autos. inverts H0. false Henmem. rew_listx*.
    + (* Spawn before start: new event is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: new event is not a join *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + (* Start before non-start: new event_end t has event_start t before it *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * rew_listx. splits.
        -- apply~ Hend.
        -- simpl. intros ->. apply Henmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepRead: log' = log & event_read t i v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Unique spawns: event_read is not a spawn *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + (* Unique starts: event_read is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: event_read is not an end *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Spawn before start: event_read is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: event_read is not a join *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + (* Start before non-start: thread t must have started before the new event *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepWrite: log' = log & event_write t i v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Unique spawns: event_write is not a spawn *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + (* Unique starts: event_write is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: event_write is not an end *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Spawn before start: event_write is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: event_write is not a join *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + (* Start before non-start: thread t must have started before the new event *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hwnmem. rew_listx*.
    + (* Lock filter unchanged: touches_lock l (event_write t i v) = False *)
      introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepSpawn: log' = log & event_spawn t t' *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hsnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    (* t' is fresh: it was not in dom T, so no spawn for t' exists in log *)
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem'). apply H6. apply* Hdspawned. }
    splits.
    + (* Unique spawns: event_spawn t t' is a spawn, but t' is fresh *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * intros (t1' & Hmem''). apply~ Huspawn. exists t1'.
        rew_listx. rew_listx in Hmem''.
        branches; autos. inverts H0.
        false Hnospawn. exists t1. rew_listx~.
    + (* Unique starts: event_spawn is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: event_spawn is not an end *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Spawn before start: event_spawn t t' is a start for t2 only if t2 = t';
         but event_start t' is not in log & event_spawn t t' *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: event_spawn is not a join *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + (* Start before non-start: thread t must have started before the new event *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hsnmem. rew_listx*.
    + (* Lock filter unchanged: touches_lock l (event_spawn t t') = False *)
      introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepJoin: log' = log & event_join t t' *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Htended: (mem (event_end t') log).
    { apply Hdend. eauto. }
    splits.
    + (* Unique spawns: event_join is not a spawn *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + (* Unique starts: event_join is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Unique ends: event_join is not an end *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + (* Spawn before start: event_join is not a start *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + (* Join after end: event_join t t' appended — need event_end t' in prefix *)
      introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * apply* Hjoin.
    + (* Start before non-start *)
      introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + (* No events after end for that thread *)
      introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hjnmem. rew_listx*.
    + (* Lock filter unchanged: touches_lock l (event_join t t') = False *)
      introv. rew_listx.
      cases_if~. rew_list~.
  - (* StepLock: log' = log & event_lock t l *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _ & Hdunlock & _).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hlfree: (log = nil \/ exists t'' log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_unlock t'' l).
    { apply* Hdunlock. }
    splits.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hlnmem. rew_listx*.
    + (* wf_lock_log: for l0 = l, filter grows by event_lock t l *)
      introv. rew_listx.
      cases_if as Heql.
      * unfold touches_lock in Heql. subst. rew_list.
        apply wf_lock_log_snoc_lock.
        { apply~ Hlock. }
        { destruct Hlfree as [Hnil | (t'' & log'' & Hfilt)].
          - left. subst. rew_listx~.
          - right. exists t'' log''. exact Hfilt. }
      * rew_list. apply~ Hlock.
  - (* StepRelease: log' = log & event_unlock t l *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply* Hdlock. }
    splits.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + (* wf_lock_log: for l0 = l, filter grows by event_unlock t l *)
      introv. rew_listx.
      cases_if as Heql.
      * unfold touches_lock in Heql. subst. rew_list.
        apply* wf_lock_log_snoc_unlock.
      * rew_list. apply~ Hlock.
Qed.
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
        branches~. subst.
        false.
        asserts (t1 & Hmem & _): (exists t1, mem (event_spawn t1 t) nil /\ ~mem (event_start t) nil).
        { apply* Hdstart. }
        exact (mem_nil_inv Hmem).
    + intros l. rew_listx. cases_if~. rew_list.
      apply Hdwrite.
  - (* StepEnd: log' = log & event_end t, T' = T[t := (terminated, ret r)] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    splits.
    + (* Spawned: dom T unchanged, event_end not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_terminated, te_ret r)])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [| congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_end not a spawn *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply* Hdrunning. }
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: t now terminated, log gains event_end t *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply* Hdrunning. }
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
        -- asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
           { apply~ Hdend. }
           asserts Hneq: (t0 <> t).
           { intros ->. false Henmem. apply* Hdend. }
           exists e'. apply~ binds_update_neq.
        -- inverts Heq. exists (te_ret r). apply binds_update_same.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           rew_listx*.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t transitions from running to terminated *)
      intros t0. splits.
      * introv (Hsmem & Henmem).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- false Henmem. rew_listx*.
        -- rew_listx in Hsmem. branches; [|congruence].
           asserts Henmem': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem & Henmem): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem Hmem).
              ** inverts Heq. exact (Hneq eq_refl).
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & Hne): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply* Hdrunning. }
        exact (mem_nil_inv Hmem).
    + (* Writes: H unchanged, filter unchanged *)
      intros i v. rew_listx. cases_if~. rew_list. apply Hdwrite.
  - (* StepRead: log' = log & event_read t i v, T' = T[t := running K(v)] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_read not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K (ret_val v)))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_read not a spawn *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: event_read not an end, T terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts Hneq: (t0 <> t).
        { intros ->. exact (Hrnmem Hmem). }
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t stays running (new exp), log gains event_read (not start/end) *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists (te_exp (K (ret_val v))). apply binds_update_same.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem0': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Hrnmem Hmem).
              ** congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** congruence.
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & Hne): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply* Hdrunning. }
        exact (mem_nil_inv Hmem).
    + (* Writes: H unchanged, event_read not a write *)
      intros i0 v0. rew_listx. cases_if~. rew_list. apply Hdwrite.
  - (* StepWrite: log' = log & event_write t i v, T' = T[t := running K(void)], H' = H[i := v] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_write not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K void))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_write not a spawn *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: event_write not an end, T terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts Hneq: (t0 <> t).
        { intros ->. exact (Hwnmem Hmem). }
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t stays running, log gains event_write (not start/end) *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists (te_exp (K void)). apply binds_update_same.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem0': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Hwnmem Hmem).
              ** congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** congruence.
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & Hne): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply* Hdrunning. }
        exact (mem_nil_inv Hmem).
    + (* Writes: H[i := v], filter gains event_write t i v *)
      intros i0 v0. rew_listx. cases_if as Hcase.
      * (* i0 = i: filter grows by event_write t i v *)
        unfold writes_location in Hcase. subst. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt as [_ Heq].
           inverts Heq. apply binds_update_same.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. subst.
           exists t (LibList.filter (fun e0 => writes_location i e0) log).
           rew_list~.
      * (* i0 ≠ i: filter unchanged *)
        unfold writes_location in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdwrite. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply* Hdwrite.
  - (* StepSpawn: log' = log & event_spawn t t', T' = T[t := ...][t' := (new, e')] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hsnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem'). apply H6. apply* Hdspawned. }
    asserts* Htin: (t \indom T).
    splits.
    + (* Spawned: t' newly spawned, t' added to dom T *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')])) with
               (union (dom (T[t := (state_running, te_exp (K t'))])) (single t'));
        [apply dom_update|].
      replaces (dom (T[t := (state_running, te_exp (K t'))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set.
      splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|inverts Heq; autos*].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst. exists t. rew_listx*.
    + (* New threads: event_spawn t t' added, t' has no start yet *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
        -- destruct (classic (t2 = t')) as [->|Hneq'].
           ++ false Hnospawn. exists t1. autos*.
           ++ destruct (classic (t2 = t)) as [->|Hneq].
              ** false Hnmem. rew_listx*.
              ** asserts (e0 & Hbinds): (exists e, binds T t2 (state_new, e)).
                 { apply Hdstart. exists t1. splits.
                   - autos*.
                   - intros contra. apply Hnmem. rew_listx*. }
                 exists e0. apply~ binds_update_neq. apply~ binds_update_neq.
        -- inverts Heq.
           exists. apply binds_update_same.
      * introv (e0 & Hbinds).
        destruct (classic (t2 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           exists t. split.
           ++ rew_listx*.
           ++ introv contra. rew_listx in contra. destruct contra as [contra|Heq].
              ** false Hnospawn.
                 asserts (l1 & l2 & ->): (exists l1 l2, log = l1 ++ event_start t' :: l2).
                 { apply~ mem_inv_middle. }
                 forwards* (t1 & Hmem): Hspawn.
                 exists t1. rew_listx*.
              ** congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t2 = t)) as [->|Hneq].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
              { apply Hdstart. exists e0. exact Hbinds2. }
              exists t1. splits.
              ** rew_listx*.
              ** introv contra. apply Hnmem. rew_listx in contra. destruct contra as [contra|Heq]; [exact contra|congruence].
    + (* Ended: event_spawn not an end, terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts (e0 & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- asserts* Hindom: (t' \indom T). false* H6.
        -- exists e0. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e0 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              rew_listx. left. apply* Hdend.
    + (* Running: t stays running, event_spawn not start/end *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        rew_listx in Hsmem0. destruct Hsmem0 as [Hsmem0|Heq]; [|congruence].
        asserts Henmem0': (~mem (event_end t0) log).
        { introv Hmem. apply Henmem0. rew_listx*. }
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- false Hnospawn.
           asserts (l1 & l2 & ->): (exists l1 l2, log = l1 ++ event_start t' :: l2).
           { apply~ mem_inv_middle. }
           forwards* (t1 & Hmem): Hspawn.
           exists t1. rew_listx*.
        (* -- false Hnospawn. apply Hdspawned. autos*. *)
        -- destruct (classic (t0 = t)) as [->|Hneq].
           ++ exists (te_exp (K t')). apply~ binds_update_neq. apply binds_update_same.
           ++ asserts (e0 & Hbinds): (exists e, binds T t0 (state_running, e)).
              { apply Hdrunning. split*. }
              exists e0. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e0 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq].
           ++ apply binds_update_same_inv in Hbinds1. inverts Hbinds1.
              split.
              ** rew_listx*.
              ** introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [exact (Hsnmem Hmem)|congruence].
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
              { apply Hdrunning. exists e0. exact Hbinds2. }
              split.
              ** rew_listx*.
              ** introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [exact (Henmem0 Hmem)|congruence].
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & Hne): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply* Hdrunning. }
        exact (mem_nil_inv Hmem).
    + (* Writes: H unchanged, event_spawn not a write *)
      intros i v. rew_listx. cases_if~. rew_list. apply Hdwrite.
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r)] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_join not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K r))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_join not a spawn *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: event_join not an end, terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts Hneq: (t0 <> t).
        { intros ->. exact (Hjnmem Hmem). }
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t stays running (new exp K r), log gains event_join (not start/end) *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists (te_exp (K r)). apply binds_update_same.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem0': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Hjnmem Hmem).
              ** congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** congruence.
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~. apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst.
        false.
        asserts (Hmem & Hne): (mem (event_start t) nil /\ ~mem (event_end t) nil).
        { apply* Hdrunning. }
        exact (mem_nil_inv Hmem).
    + (* Writes: H unchanged, event_join not a write *)
      intros i v. rew_listx. cases_if~. rew_list. apply Hdwrite.
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...], L' = L[l := ls_held t] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_lock not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K void))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_lock not a spawn *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: event_lock not an end, terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts Hneq: (t0 <> t).
        { intros ->. exact (Hlnmem Hmem). }
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t stays running (K void), log gains event_lock (not start/end) *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists (te_exp (K void)). apply binds_update_same.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem0': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Hlnmem Hmem).
              ** congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** congruence.
    + (* Locked: l now held by t; other locks unchanged *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_lock t l *)
        unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           apply binds_update_same.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. inverts Hbinds.
           exists (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdlock. exists log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdlock in Hbinds'. destruct Hbinds' as (log' & Hfilt).
           exists log'. exact Hfilt.
    + (* Unlocked: l no longer free; other locks unchanged *)
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_lock; l is now held → both sides false *)
        unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ apply~ binds_update_neq.
              apply Hdunlock. right. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           right. apply Hdunlock in Hbinds'.
           destruct Hbinds' as [Hnil | (t0 & log' & Hfilt)].
           ++ subst. false (mem_nil_inv Hsmem).
           ++ exists t0 log'. exact Hfilt.
    + (* Writes: H unchanged, event_lock not a write *)
      intros i v. rew_listx. cases_if~. rew_list. apply Hdwrite.
  - (* StepRelease: log' = log & event_unlock t l, T' = T[t := ...], L' = L[l := ls_free] *)
    destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_unlock not a spawn *)
      intros t2.
      replaces (dom (T[t := (state_running, te_exp (K void))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set. splits.
      * introv (t1 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T). { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + (* New threads: event_unlock not a spawn *)
      intros t2. splits.
      * introv (t1 & Hmem & Hnmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. splits.
          - autos*.
          - intros contra. apply Hnmem. rew_listx*. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log).
        { apply Hdstart. exists e'. exact Hbinds'. }
        exists. rew_listx. splits*.
    + (* Ended: event_unlock not an end, terminated threads unchanged *)
      intros t0. splits.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [|congruence].
        asserts Hneq: (t0 <> t).
        { intros ->. exact (Hlnmem Hmem). }
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply* Hdend.
    + (* Running: t stays running (K void), log gains event_unlock (not start/end) *)
      intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists (te_exp (K void)). apply binds_update_same.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem0': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Hlnmem Hmem).
              ** congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** congruence.
    + (* Locked: l now free; filter gains event_unlock; l is now free → both sides false *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_unlock t l; l is now free → both sides false *)
        unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdlock. exists log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdlock in Hbinds'. destruct Hbinds' as (log' & Hfilt).
           exists log'. exact Hfilt.
    + (* Unlocked: l now free; filter gains event_unlock t l → both sides true for l0 = l *)
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_unlock t l → both sides true *)
        unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ apply binds_update_same.
        -- introv Hbinds.
           right. exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv [Hnil | (t0 & log' & Hfilt)].
           ++ false (last_eq_nil_inv Hnil).
           ++ apply~ binds_update_neq.
              apply Hdunlock. right. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           right. apply Hdunlock in Hbinds'.
           destruct Hbinds' as [Hnil | (t0 & log' & Hfilt)].
           ++ subst. false (mem_nil_inv Hsmem).
           ++ exists t0 log'. exact Hfilt.
    + (* Writes: H unchanged, event_unlock not a write *)
      intros i v. rew_listx. cases_if~. rew_list. apply Hdwrite.
Qed.
