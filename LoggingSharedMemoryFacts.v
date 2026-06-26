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
    { match goal with Hpre: (binds _ l ls_free \/ l \notindom _) |- _ => destruct Hpre as [Hfree | Hnotin] end.
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

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & Hinit).
  inversion Hstep; substs; clear Hstep.
  - lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    splits.
    + intros.
      rew_dom. rew_set.
      splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T).
           { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T).
           {
             apply* Hdspawned.
           }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack.
           left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack.
           left. exists. rew_listx*.
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
      apply Hdunlock.
    + intros l. rew_listx. cases_if~. rew_list.
      apply Hdwrite.
    + introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      right.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->]; auto.
      forwards*: mem_nil_inv contra.
  - (* StepEnd: log' = log & event_end t, T' = T[t := (terminated, ret r)] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    splits.
    + (* Spawned: dom T unchanged, event_end not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_end not a spawn *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply* Hdrunning. }
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* Writes: H unchanged, filter unchanged *)
      intros x v. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepRead: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_read not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_read not a spawn *)
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* Writes: H unchanged, event_read not a write *)
      intros y v0. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepWrite: log' = log & event_write t x v, T' = T[t := running K(void)], H' = H[x := v] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_write not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_write not a spawn *)
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* Writes: H[x := v], filter gains event_write t x v *)
      intros y v0. rew_listx. cases_if as Hcase.
      * (* y = x: filter grows by event_write t x v *)
        unfold writes_variable in Hcase. subst. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt as [_ Heq].
           inverts Heq. apply binds_update_same.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. subst.
           exists t (LibList.filter (fun e0 => writes_variable x e0) log).
           rew_list~.
      * (* y ≠ x: filter unchanged *)
        unfold writes_variable in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdwrite. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply* Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepSpawn: log' = log & event_spawn t t', T' = T[t := ...][t' := (new, e')] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
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
    + (* New threads: event_spawn t t' added, t' has no start yet *)
      intros t2. splits.
      * introv (Hdisj & Hnmem).
        destruct (classic (t2 = t')) as [->|Hneq'].
        -- (* the freshly spawned thread *)
           exists. apply binds_update_same.
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
    + (* Locked: L unchanged, filter unchanged *)
      intros t0 l. rew_listx. cases_if~. rew_list. apply Hdlock.
    + (* Unlocked: L unchanged, filter unchanged *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* Writes: H unchanged, event_spawn not a write *)
      intros x v. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r)] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_join not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_join not a spawn *)
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* Writes: H unchanged, event_join not a write *)
      intros x v. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...], L' = L[l := ls_held t] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_lock not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_lock not a spawn *)
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdunlock. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdunlock in Hbinds'. exact Hbinds'.
    + (* Writes: H unchanged, event_lock not a write *)
      intros x v. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
  - (* StepRelease: log' = log & event_unlock t l, T' = T[t := ...], L' = L[l := ls_free] *)
    lets (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite & _): Hdesc.
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits.
    + (* Spawned: dom T unchanged, event_unlock not a spawn *)
      intros.
      rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts* Hin: (t2 \indom T). { applys* Hdspawned. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           auto.
      * intros Hin. branches.
        -- apply Hdspawned in H0.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
        -- subst.
           asserts* Hdom: (t \indom T).
           apply Hdspawned in Hdom.
           branches; rew_listx*.
           unpack. left. exists. rew_listx*.
    + (* New threads: event_unlock not a spawn *)
      intros t2. splits.
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
        exists e'. apply~ binds_update_neq.
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
        -- introv (t0 & log' & Hfilt). apply binds_update_same.
        -- introv Hbinds.
           exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 ≠ l: filter unchanged, L unchanged *)
        unfold touches_lock in Hcase. rew_list. splits.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply Hdunlock. exists t0 log'. exact Hfilt.
        -- introv Hbinds.
           forwards Hbinds': binds_update_neq_inv Hbinds Hcase.
           apply Hdunlock in Hbinds'. exact Hbinds'.
    + (* Writes: H unchanged, event_unlock not a write *)
      intros x v. rew_listx. cases_if~. rew_list. apply Hdwrite.
    + (* Init event still present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      false.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->];
        [forwards*: mem_nil_inv contra|].
      asserts contra: (mem (event_start t_root) nil).
      { apply* Hdrunning. }
      forwards*: mem_nil_inv contra.
Qed.