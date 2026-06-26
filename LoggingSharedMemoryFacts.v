From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingSharedMemory.

Import SharedMemory.
Import Log.
Import LogFacts.
Import LoggingSharedMemory.

Existing Instance inhab_val.
Existing Instance inhab_exp.

Definition init_cfg (e : exp) : cfg := (empty[t_root := (state_new, te_exp e)], empty, empty).

Example init_cfg_wf :
  forall e,
    describes nil (init_cfg e).
Proof.
  intros.
  unfolds init_cfg.
  splits; rew_list.
  - introv.
    splits.
    + introv Hsrc.
      destruct Hsrc as [(t1 & contra)| ->].
      * inverts contra.
      * rew_dom. rew_set. autos.
    + introv Hdom.
      rew_dom. rew_set in Hdom.
      branches.
      * forwards*: indom_empty_inv.
      * subst. right. rew_listx*.
  - introv.
    splits.
    + introv (Hsrc & Hnmem).
      destruct Hsrc as [(t1 & contra)| ->].
      * inverts contra.
      * exists. apply binds_update_same.
    + introv (e' & Hbinds).
      destruct (classic (t2 = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
        inverts Heq.
        splits*.
        introv contra.
        do 2 inverts contra as contra.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv Hmem.
      do 2 inverts Hmem as Hmem.
    + introv (e' & Hbinds).
      destruct (classic (t = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (Hmem & Hnmem).
      do 2 inverts Hmem as Hmem.
    + introv (e' & Hbinds).
      destruct (classic (t = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv contra.
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (t & log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv contra.
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (t & log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv contra.
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - intros contra. congruence.
Qed.

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
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: append [event_start t] *)
    lets (_ & Hdstart & _): Hdesc.
    asserts (Hsrc & Hnmem): (((exists t1, mem (event_spawn t1 t) log) \/ t = t_root) /\ ~mem (event_start t) log).
    { apply* Hdstart. }
    asserts Hrootnil: (t = t_root -> log = nil).
    { intros ->. destruct (classic (log = nil)) as [Hnil | Hne]; [exact Hnil|].
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      false Hnmem. apply Hdroot. exact Hne. }
    apply* wf_log_start_last.
  - (* StepEnd: append [event_end t] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_end_last.
  - (* StepRead: append [event_read t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_read_last.
  - (* StepWrite: append [event_write t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_write_last.
  - (* StepSpawn: append [event_spawn t t'], with [t'] fresh *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _ & _ & _ & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem'). apply H6. apply* Hdspawned. }
    asserts Htneq: (t' <> t_root).
    { intros ->. apply H6. apply* Hdspawned. }
    apply* wf_log_spawn_last.
  - (* StepJoin: append [event_join t t'], with [t'] ended *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Htended: (mem (event_end t') log).
    { apply Hdend. eauto. }
    apply* wf_log_join_last.
  - (* StepLock: append [event_lock t l] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & Hdunlock & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hlfree: (LibList.filter (fun e => touches_lock l e) log = nil \/
                     exists t'' log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_unlock t'' l).
    { match goal with Hpre : (binds _ l ls_free \/ l \notindom _) |- _ => destruct Hpre as [Hfree | Hnotin] end.
      - right. apply~ Hdunlock.
      - left. destruct (last_case (LibList.filter (fun e => touches_lock l e) log)) as [Hnil | (x & xs' & Heqf)].
        + exact Hnil.
        + exfalso. forwards [(t' & ->) | (t' & ->)]: filter_touches_lock_last_inv Heqf.
          * forwards Hb: (proj1 (Hdlock t' l)). { exists xs'. exact Heqf. }
            lets Hin: (indom_of_binds Hb). apply Hnotin. exact Hin.
          * forwards Hb: (proj1 (Hdunlock l)). { exists t' xs'. exact Heqf. }
            lets Hin: (indom_of_binds Hb). apply Hnotin. exact Hin. }
    apply* wf_log_snoc_lock.
  - (* StepRelease: append [event_unlock t l] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply* Hdlock. }
    apply* wf_log_unlock_last.
Qed.

(* ============================================================= *)
(* Reusable [describes]-conjunct preservation lemmas             *)
(* ------------------------------------------------------------- *)
(* Each [describes] conjunct relates a property of the log to a   *)
(* component of the configuration. A step appends one event and  *)
(* updates one part of the config, so for any given step most     *)
(* conjuncts are preserved "for free": the appended event is not  *)
(* of the kind the conjunct constrains, and the config component  *)
(* it mentions is untouched. The lemmas below capture exactly     *)
(* those generic cases, one per conjunct, for an in-place update  *)
(* of a single (already-present) thread. They leave each step     *)
(* with only its one or two genuinely interesting conjuncts.      *)
(* ============================================================= *)

(* Conjunct 1 (spawned/initialised threads are in [dom T]): an in-place update
   does not change [dom T], and a non-spawn event adds no spawn edge. *)
Lemma describes_spawned_inplace : forall (log : Log.log) e (T : threads) t v,
    t \indom T ->
    (forall a b, e <> event_spawn a b) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) <-> t2 \indom T) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) (log & e)) \/ t2 = t_root) <-> t2 \indom (T[t := v])).
Proof.
  introv Htin Hns Hd. intros t2.
  rew_dom. rew_set. splits.
  - introv Hsrc.
    rew_listx in Hsrc.
    destruct Hsrc as [(t1 & Hmem) | ->].
    + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
      * asserts Hin: (t2 \indom T). { applys Hd. left. exists* t1. }
        autos.
      * false (Hns _ _ (eq_sym Heq)).
    + asserts Hrmem: (t_root \indom T). { applys Hd. right. reflexivity. }
      auto.
  - intros Hin. destruct Hin as [Hin | ->].
    + apply Hd in Hin. destruct Hin as [(t1 & Hmem) | Hroot].
      * left. exists t1. rew_listx*.
      * right. exact Hroot.
    + apply Hd in Htin. destruct Htin as [(t1 & Hmem) | Hroot].
      * left. exists t1. rew_listx*.
      * right. exact Hroot.
Qed.

(* Conjunct 2 (unstarted threads are [state_new]): updating a thread to a
   non-[new] state, with a non-spawn non-start event, leaves the new threads. *)
Lemma describes_new_inplace : forall (log : Log.log) e (T : threads) t st e0,
    mem (event_start t) log ->
    st <> state_new ->
    (forall a b, e <> event_spawn a b) ->
    (forall a, e <> event_start a) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~ mem (event_start t2) log
                <-> exists e', binds T t2 (state_new, e')) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) (log & e)) \/ t2 = t_root) /\ ~ mem (event_start t2) (log & e)
                <-> exists e', binds (T[t := (st, e0)]) t2 (state_new, e')).
Proof.
  introv Hsmem Hstne Hns Hnst Hd. intros t2. splits.
  - introv (Hdisj & Hnmem).
    asserts Hneq: (t2 <> t).
    { intros ->. apply Hnmem. rew_listx. left. exact Hsmem. }
    asserts (e' & Hbinds): (exists e', binds T t2 (state_new, e')).
    { apply Hd. splits.
      - rew_listx in Hdisj.
        destruct Hdisj as [(t1 & Hmem) | ->].
        + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
          * left. exists* t1.
          * false (Hns _ _ (eq_sym Heq)).
        + right*.
      - intros Hc. apply Hnmem. rew_listx. left. exact Hc. }
    exists e'. apply~ binds_update_neq.
  - introv (e' & Hbinds).
    asserts Hneq: (t2 <> t).
    { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
    forwards~ Hbinds': binds_update_neq_inv Hbinds.
    asserts (Hdisj & Hnmem):
      (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~ mem (event_start t2) log).
    { apply Hd. exists* e'. }
    splits.
    + destruct Hdisj as [(t1 & Hmem) | Hmem].
      * left. exists t1. rew_listx*.
      * right. rew_listx*.
    + intros Hc. rew_listx in Hc. destruct Hc as [Hc | Heq].
      * exact (Hnmem Hc).
      * false (Hnst _ (eq_sym Heq)).
Qed.

(* Conjunct 3 (ended threads are [state_terminated]): updating an unfinished
   thread to a non-[terminated] state, with a non-end event, leaves them. *)
Lemma describes_ended_inplace : forall (log : Log.log) e (T : threads) t st e0,
    ~ mem (event_end t) log ->
    st <> state_terminated ->
    (forall a, e <> event_end a) ->
    (forall t0, mem (event_end t0) log <-> exists e', binds T t0 (state_terminated, e')) ->
    (forall t0, mem (event_end t0) (log & e) <-> exists e', binds (T[t := (st, e0)]) t0 (state_terminated, e')).
Proof.
  introv Hrnmem Hstne Hne Hd. intros t0. splits.
  - introv Hmem.
    rew_listx in Hmem. destruct Hmem as [Hmem | Heq]; [| false (Hne _ (eq_sym Heq))].
    asserts Hneq: (t0 <> t).
    { intros ->. exact (Hrnmem Hmem). }
    asserts (e' & Hbinds): (exists e', binds T t0 (state_terminated, e')).
    { apply~ Hd. }
    exists e'. apply~ binds_update_neq.
  - introv (e' & Hbinds).
    destruct (classic (t0 = t)) as [->|Hneq].
    + apply binds_update_same_inv in Hbinds. congruence.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      rew_listx. left. apply* Hd.
Qed.

(* Conjunct 4 (started, unfinished threads are [state_running]): re-updating a
   running thread (still running), with a non-start non-end event, leaves them. *)
Lemma describes_running_inplace : forall (log : Log.log) e (T : threads) t e0,
    mem (event_start t) log ->
    ~ mem (event_end t) log ->
    (forall a, e <> event_start a) ->
    (forall a, e <> event_end a) ->
    (forall t0, mem (event_start t0) log /\ ~ mem (event_end t0) log <-> exists e', binds T t0 (state_running, e')) ->
    (forall t0, mem (event_start t0) (log & e) /\ ~ mem (event_end t0) (log & e)
                <-> exists e', binds (T[t := (state_running, e0)]) t0 (state_running, e')).
Proof.
  introv Hsmem Hrnmem Hnst Hne Hd. intros t0. splits.
  - introv (Hsmem0 & Henmem0).
    destruct (classic (t0 = t)) as [->|Hneq].
    + exists e0. apply binds_update_same.
    + rew_listx in Hsmem0. destruct Hsmem0 as [Hsmem0 | Heq]; [| false (Hnst _ (eq_sym Heq))].
      asserts Henmem0': (~mem (event_end t0) log).
      { introv Hmem. apply Henmem0. rew_listx*. }
      asserts (e' & Hbinds): (exists e', binds T t0 (state_running, e')).
      { apply Hd. split*. }
      exists e'. apply~ binds_update_neq.
  - introv (e' & Hbinds).
    destruct (classic (t0 = t)) as [->|Hneq].
    + apply binds_update_same_inv in Hbinds. inverts Hbinds.
      split.
      * rew_listx. left. exact Hsmem.
      * introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
        -- exact (Hrnmem Hmem).
        -- false (Hne _ (eq_sym Heq)).
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
      { apply Hd. exists e'. exact Hbinds'. }
      split.
      * rew_listx. left. exact Hsmem0.
      * introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
        -- exact (Henmem0 Hmem).
        -- false (Hne _ (eq_sym Heq)).
Qed.

(* Conjunct 5 (held locks): an event touching no lock leaves the lock filters
   and [L] unchanged. *)
Lemma describes_locked_snoc : forall (log : Log.log) e (L : locks),
    (forall l, ~ touches_lock l e) ->
    (forall t l, (exists log', LibList.filter (fun e0 => touches_lock l e0) log = log' & event_lock t l)
                 <-> binds L l (ls_held t)) ->
    (forall t l, (exists log', LibList.filter (fun e0 => touches_lock l e0) (log & e) = log' & event_lock t l)
                 <-> binds L l (ls_held t)).
Proof.
  introv Hnt Hd. intros t l. rew_listx. cases_if as Hc.
  - false (Hnt l Hc).
  - rew_list. apply Hd.
Qed.

(* Conjunct 6 (free locks): likewise. *)
Lemma describes_free_snoc : forall (log : Log.log) e (L : locks),
    (forall l, ~ touches_lock l e) ->
    (forall l, (exists t log', LibList.filter (fun e0 => touches_lock l e0) log = log' & event_unlock t l)
               <-> binds L l ls_free) ->
    (forall l, (exists t log', LibList.filter (fun e0 => touches_lock l e0) (log & e) = log' & event_unlock t l)
               <-> binds L l ls_free).
Proof.
  introv Hnt Hd. intros l. rew_listx. cases_if as Hc.
  - false (Hnt l Hc).
  - rew_list. apply Hd.
Qed.

(* Conjunct 7 (latest writes): a non-write event leaves the write filters and
   [H] unchanged. *)
Lemma describes_writes_snoc : forall (log : Log.log) e (H : heap),
    (forall x, ~ writes_variable x e) ->
    (forall x v, (exists t log', LibList.filter (fun e0 => writes_variable x e0) log = log' & event_write t x v)
                 <-> binds H x v) ->
    (forall x v, (exists t log', LibList.filter (fun e0 => writes_variable x e0) (log & e) = log' & event_write t x v)
                 <-> binds H x v).
Proof.
  introv Hnw Hd. intros x v. rew_listx. cases_if as Hc.
  - false (Hnw x Hc).
  - rew_list. apply Hd.
Qed.

(* Conjunct 8 (the root start is present): once a running thread exists, the log
   is non-empty and already contains the root start, which survives the snoc. *)
Lemma describes_init_running : forall (log : Log.log) e t,
    mem (event_start t) log ->
    (log <> nil -> mem (event_start t_root) log) ->
    ((log & e) <> nil -> mem (event_start t_root) (log & e)).
Proof.
  introv Hmem Hd _. rew_listx. left. apply Hd.
  intro Heq. subst. forwards*: mem_nil_inv Hmem.
Qed.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _): Hwf.
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: append [event_start t]; thread t goes new -> running.
       Interesting conjuncts: 2 (t leaves the new set), 4 (t becomes running),
       8 (the start may be the root's). *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts* Htin: (t \indom T).
    asserts Hnew: (exists e', binds T t (state_new, e')). { eexists; eassumption. }
    asserts Hnend: (~ mem (event_end t) log).
    { intros Hc. apply Hdend in Hc as (e2 & Hb). destruct Hnew as (e3 & Hb3).
      forwards~ Hcontra: binds_inj Hb Hb3. }
    splits.
    + applys* describes_spawned_inplace.
    + intros. splits.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. splits.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | ->].
            + rew_listx in Hmem. branches; [| congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e'.
        apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmem):
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
            /\ ~ mem (event_start t2) log).
        { apply Hdstart. exists* e'. }
        splits.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros Hc. rew_listx in Hc. branches.
           ++ false*.
           ++ congruence.
    + applys* describes_ended_inplace.
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
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra | Heq].
              ** exact (Hnend contra).
              ** discriminate Heq.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
            asserts (Hmem & Hnmem): (mem (event_start t0) log /\
              ~ mem (event_end t0) log).
           { apply* Hdrunning. }
           rew_listx. splits*.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + applys* describes_writes_snoc.
    + introv _.
      rew_listx. destruct log; [|auto_star].
      right.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->]; auto.
      forwards*: mem_nil_inv contra.
  - (* StepEnd: append [event_end t]; thread t terminates.
       Interesting conjuncts: 3 (t becomes terminated), 4 (t leaves running). *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + intros t0. splits.
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
    + intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- false Henmem0. rew_listx*.
        -- rew_listx in Hsmem0. branches; [|congruence].
           asserts Henmem': (~mem (event_end t0) log).
           { introv Hmem. apply Henmem0. rew_listx*. }
           asserts (e' & Hbinds): (exists e, binds T t0 (state_running, e)).
           { apply Hdrunning. split*. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply Hdrunning. exists e'. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
              ** exact (Henmem0 Hmem).
              ** inverts Heq. exact (Hneq eq_refl).
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + applys* describes_writes_snoc.
    + applys* describes_init_running.
  - (* StepRead: append [event_read t x v]; thread t stays running.
       Every conjunct is generic. *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits; [ applys* describes_spawned_inplace | applys* describes_new_inplace | applys* describes_ended_inplace | applys* describes_running_inplace | applys* describes_locked_snoc | applys* describes_free_snoc | applys* describes_writes_snoc | applys* describes_init_running ].
  - (* StepWrite: append [event_write t x v]; thread t stays running, H gains x.
       Interesting conjunct: 7 (the heap). *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + intros y v0. rew_listx. cases_if as Hcase.
      * unfold writes_variable in Hcase. subst. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt as [_ Heq].
           inverts Heq. apply binds_update_same.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. subst.
           exists t (LibList.filter (fun e0 => writes_variable x e0) log).
           rew_list~.
      * unfold writes_variable in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdwrite. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply* Hdwrite.
    + applys* describes_init_running.
  - (* StepSpawn: append [event_spawn t t']; t stays running, fresh t' added as new.
       The genuinely interesting case: conjuncts 1,2,3,4 all see the new thread. *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hsnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem'). apply H6. apply* Hdspawned. }
    asserts* Htin: (t \indom T).
    splits.
    + intros t2.
      replaces (dom (T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')])) with
               (union (dom (T[t := (state_running, te_exp (K t'))])) (single t'));
        [apply dom_update|].
      replaces (dom (T[t := (state_running, te_exp (K t'))])) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set.
      splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem) | ->].
        -- rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
           ++ left. left. applys Hdspawned. left. exists* t1.
           ++ inverts Heq. autos*.
        -- left. left. applys* Hdspawned.
      * intros Hin. destruct Hin as [[Hin | ->] | ->].
        -- apply Hdspawned in Hin. branches.
           ++ unpack. left. exists. rew_listx*.
           ++ right. rew_listx*.
        -- apply Hdspawned in Htin. branches.
           ++ unpack. left. exists. rew_listx*.
           ++ right. rew_listx*.
        -- left. exists t. rew_listx*.
    + intros t2. splits.
      * introv (Hdisj & Hnmem).
        destruct (classic (t2 = t')) as [->|Hneq'].
        -- exists. apply binds_update_same.
        -- destruct (classic (t2 = t)) as [->|Hneq].
           ++ false Hnmem. rew_listx*.
           ++ asserts (e0 & Hbinds): (exists e, binds T t2 (state_new, e)).
              { apply Hdstart. splits.
                - rew_listx in Hdisj.
                  destruct Hdisj as [(t1 & Hmem) | ->].
                  + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
                    * left. exists* t1.
                    * congruence.
                  + right*.
                - intros Hc. apply Hnmem. rew_listx*. }
              exists e0. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e0 & Hbinds).
        destruct (classic (t2 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ left. exists t. rew_listx*.
           ++ introv contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              false H6.
              asserts (l1 & l2 & Heq2): (exists l1 l2, log = l1 ++ event_start t' :: l2).
              { apply~ mem_inv_middle. }
              forwards [(t1 & Hmem) | Hmem]: Hspawn Heq2.
              ** applys Hdspawned. left. exists t1. rewrite Heq2. rew_listx*.
              ** applys* Hdspawned.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t2 = t)) as [->|Hneq].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              asserts (Hdisj & Hnmem):
                (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
                  /\ ~mem (event_start t2) log).
              { apply Hdstart. exists e0. exact Hbinds2. }
              split.
              ** destruct Hdisj as [(t1 & Hmem) | Hmem].
                 --- left. exists t1. rew_listx*.
                 --- right. rew_listx*.
              ** introv contra. apply Hnmem. rew_listx in contra. destruct contra as [contra|Heq]; [exact contra|congruence].
    + intros t0. splits.
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
    + intros t0. splits.
      * introv (Hsmem0 & Henmem0).
        rew_listx in Hsmem0. destruct Hsmem0 as [Hsmem0|Heq]; [|congruence].
        asserts Henmem0': (~mem (event_end t0) log).
        { introv Hmem. apply Henmem0. rew_listx*. }
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- false H6.
           asserts (l1 & l2 & Heq2): (exists l1 l2, log = l1 ++ event_start t' :: l2).
           { apply~ mem_inv_middle. }
           forwards [(t1 & Hmem) | Hmem]: Hspawn Heq2.
           ++ applys Hdspawned. left. exists t1. rewrite Heq2. rew_listx*.
           ++ applys* Hdspawned.
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
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + applys* describes_writes_snoc.
    + applys* describes_init_running.
  - (* StepJoin: append [event_join t t']; thread t stays running.
       Every conjunct is generic. *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits; [ applys* describes_spawned_inplace | applys* describes_new_inplace | applys* describes_ended_inplace | applys* describes_running_inplace | applys* describes_locked_snoc | applys* describes_free_snoc | applys* describes_writes_snoc | applys* describes_init_running ].
  - (* StepLock: append [event_lock t l]; t stays running, L gains held l.
       Interesting conjuncts: 5 (held locks), 6 (free locks). *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + intros t0 l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           apply binds_update_same.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. inverts Hbinds.
           exists (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * unfold touches_lock in Hcase. rew_list. splits.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdlock. exists log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdlock in Hbinds'. destruct Hbinds' as (log' & Hfilt).
           exists log'. exact Hfilt.
    + intros l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * unfold touches_lock in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdunlock. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdunlock in Hbinds'. exact Hbinds'.
    + applys* describes_writes_snoc.
    + applys* describes_init_running.
  - (* StepRelease: append [event_unlock t l]; t stays running, L marks l free.
       Interesting conjuncts: 5 (held locks), 6 (free locks). *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & Hdroot): Hdesc.
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts* Htin: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + intros t0 l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * unfold touches_lock in Hcase. rew_list. splits.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdlock. exists log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdlock in Hbinds'. destruct Hbinds' as (log' & Hfilt).
           exists log'. exact Hfilt.
    + intros l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. splits.
        -- introv (t0 & log' & Hfilt). apply binds_update_same.
        -- introv Hbinds.
           exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * unfold touches_lock in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdunlock. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdunlock in Hbinds'. exact Hbinds'.
    + applys* describes_writes_snoc.
    + applys* describes_init_running.
Qed.
