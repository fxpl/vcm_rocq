From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingBranching.

Import Graph.
Import GraphFacts.
Import Branching.
Import Log.
Import LogFacts.
Import LoggingBranching.

Existing Instance inhab_val.
Existing Instance inhab_exp.

(* ===================== *)
(* Initial configuration *)
(* ===================== *)
Theorem init_log_describes_init_cfg :
  forall e,
    describes nil (init_cfg e).
Proof.
  intros.
  unfolds init_cfg.
  splits; rew_list.
  - introv.
    splits.
    + introv Hsrc.
      destruct Hsrc as [(t1 & contra)|Hmem].
      * inverts contra.
      * subst. rew_dom. rew_set. autos.
    + introv Hdom.
      rew_dom. rew_set in Hdom.
      branches.
      * forwards*: indom_empty_inv.
      * subst. right. rew_listx*.
  - introv.
    splits.
    + introv (Hsrc & Hnmem).
      destruct Hsrc as [(t1 & contra)|Hmem].
      * inverts contra.
      * subst. exists. apply binds_update_same.
    + introv (e' & d & c & Hbinds).
      destruct (classic (t2 = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
        inverts Heq.
        splits*.
        introv contra.
        inverts contra.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv Hmem. inverts Hmem.
    + introv (e' & c & Hbinds).
      destruct (classic (t = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (Hmem & Hnmem).
      inverts Hmem.
    + introv (e' & d & c & Hbinds).
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
    + introv (c & contra).
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (t & log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv (c & contra).
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - unfolds init_play_cfg. exists.
    splits.
    + constructors.
    + introv Hdom.
      rew_dom. rew_set in Hdom. branches.
      * forwards*: indom_empty_inv.
      * subst. exists.
        replace (empty[t_root:=empty][t_root]) with (empty_diff) by rewrite* read_update_same.
        replace (empty[t_root:=root_commit][t_root]) with (root_commit) by rewrite* read_update_same.
        apply binds_update_same.
    + introv contra.
      forwards*: indom_empty_inv.
    + reflexivity.
    + rew_dom. introv Hdom. rew_set in *.
      branches; auto_star.
      forwards*: indom_empty_inv.
    + rew_dom. introv Hdom. rew_set in *.
      branches; auto_star.
      forwards*: indom_empty_inv.
    + introv contra.
      forwards*: indom_empty_inv.
Qed.

Theorem init_cfg_wf :
  forall e,
    wf_cfg (init_cfg e).
Proof.
  introv. unfolds init_cfg, graph_root, empty_graph.
  splits.
  - apply init_graph_wf.
  - unfolds graph_indom. rew_dom. rew_set. auto.
  - unfolds graph_indom.
    introv Hbinds.
    asserts ->: (t = t_root).
    {
      destruct* (classic (t = t_root)).
      forwards~ Hbinds': binds_update_neq_inv Hbinds.
      forwards*: binds_empty_false. typeclass.
    }
    forwards~ Heq: binds_update_same_inv Hbinds.
    inverts Heq.
    rew_dom. rew_set. auto.
  - introv Hbinds.
    forwards*: binds_empty_false. typeclass.
  - introv Hbinds.
    forwards*: binds_empty_false. typeclass.
Qed.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Branching.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepReadLocal.
    + exists. applys* StepReadGlobal.
    + exists. applys* StepReadVolatile.
    + exists. applys* StepWriteVolatile.
    + exists. applys* StepSpawn.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_cfg :
  forall cfg cfg' log log',
    wf_cfg cfg ->
    step (cfg, log) (cfg', log') ->
    wf_cfg cfg'.
Proof.
  destruct cfg as (((T & G) & L) & V).
  introv (Hwf & HrootIndom & HdomT & HdomL & HdomVC) Hstep.
  inverts Hstep.
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - unfolds do_commit.
    replace (T[t]) with (state_running, te_ret r, d, c) in H8 by forwards*: read_of_binds.
    inverts H8.
    splits*.
    + apply* graph_commit_wf.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts~ Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts* Hdom': (graph_indom G c).
        auto_star.
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - unfolds pull_volatile, do_merge.
    replace (T[t]) with (state_running, te_exp e, d, c) in H12 by forwards*: read_of_binds T t.
    inverts H12.
    asserts Hvcindom: (graph_indom G (vc_read V x)).
    { unfold vc_read, read_default. case_if as Hcase.
      - applys HdomVC. applys* binds_of_indom_read.
      - auto_star. }
    splits.
    + apply* graph_merge_wf.
    + apply* graph_merge_indom.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
    + introv Hbinds. apply* graph_merge_indom.
    + introv Hbinds. apply* graph_merge_indom.
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - unfolds push_volatile, do_commit.
    rewrite read_update_same in H11.
    inverts H11.
    asserts Hvcindom: (graph_indom G (vc_read V x)).
    { unfold vc_read, read_default. case_if as Hcase.
      - applys HdomVC. applys* binds_of_indom_read.
      - auto_star. }
    asserts Hwf1: (wf_graph (graph_commit G c c' d[x:=v])).
    { apply* graph_commit_wf. }
    splits.
    { applys graph_merge_wf Hwf1 H10.
      { apply graph_commit_indom. exact Hvcindom. }
      { apply graph_commit_indom_same. } }
    { apply graph_merge_indom. apply graph_commit_indom. exact HrootIndom. }
    { introv Hbinds.
      destruct (classic (t = t0)).
      { subst. forwards~ Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply graph_merge_indom. apply graph_commit_indom_same. }
      { forwards~ Hbinds1: binds_update_neq_inv Hbinds.
        forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
        forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
        apply graph_merge_indom. apply graph_commit_indom. applys HdomT Hbinds3. } }
    { introv Hbinds. apply graph_merge_indom. apply graph_commit_indom. applys HdomL Hbinds. }
    { intros y cy Hbinds.
      destruct (classic (y = x)).
      { subst. forwards~ Heq: binds_update_same_inv Hbinds. inverts Heq.
        apply graph_merge_indom_same. }
      { forwards~ Hbinds': binds_update_neq_inv Hbinds.
        apply graph_merge_indom. apply graph_commit_indom. applys HdomVC Hbinds'. } }
  - unfolds push_thread, do_commit.
    asserts* Hneq: (t <> t').
    rewrite~ read_update_neq in H10.
    rewrite~ read_update_same in H10.
    rewrite~ read_update_neq in H10.
    rewrite~ read_update_same in H10.
    inverts H10. splits*.
    + apply* graph_commit_wf.
    + introv Hbinds.
      destruct (classic (t' = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        destruct (classic (t = t0)).
        -- subst.
           forwards~ Heq: binds_update_same_inv Hbinds'.
           inverts* Heq.
        -- forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
           forwards~ Hbinds''': binds_update_neq_inv Hbinds''.
           forwards* Hbinds'''': binds_update_neq_inv Hbinds'''.
  - unfolds pull_thread, do_merge.
    replace (T[t']) with (state_terminated, te_ret r, empty_diff, c') in H11 by forwards*: read_of_binds t'.
    replace (T[t]) with (state_running, te_exp e, d, c) in H11 by forwards*: read_of_binds T t.
    inverts H11. splits*.
    + apply* graph_merge_wf.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
  - unfolds pull_lock, do_merge.
    match goal with Hpre : lock_read L l0 = (ls_free, c') |- _ => rename Hpre into Hread end.
    asserts Hc'indom: (graph_indom G c').
    { asserts Hread': (lock_read L l0 = (ls_free, c')). { exact Hread. }
      unfold lock_read, read_default in Hread'.
      destruct (classic (l0 \indom L)) as [Hindom|Hnotin].
      - asserts Hb: (binds L l0 (ls_free, c')).
        { applys binds_of_indom_read Hindom. case_if* in Hread'. }
        applys HdomL Hb.
      - case_if* in Hread'. }
    rewrite Hread in H11.
    replace (T[t]) with (state_running, te_exp e, d, c) in H11 by forwards*: read_of_binds T t.
    inverts H11. splits.
    + apply* graph_merge_wf.
    + apply* graph_merge_indom.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
    + introv Hbinds.
      destruct (classic (l = l0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
      * forwards* Hbinds': binds_update_neq_inv Hbinds.
    + introv Hbinds. apply* graph_merge_indom.
  - unfolds push_lock, do_commit.
    replace (T[t]) with (state_running, te_exp e, d, c) in H10 by forwards*: read_of_binds T t.
    replace (L[l0]) with (ls_held t, c') in H10 by forwards*: read_of_binds l0.
    inverts H10. splits.
    + apply* graph_commit_wf.
    + apply* graph_commit_indom.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
    + introv Hbinds.
      destruct (classic (l = l0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
    + introv Hbinds. apply* graph_commit_indom.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Proof.
  introv Hwf Hdesc Hstep.
  lets (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot): Hwf.
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: append [event_start t] *)
    lets (_ & Hdstart & _): Hdesc.
    asserts (Hsrc & Hnmem): (((exists t1, mem (event_spawn t1 t) log) \/ t = t_root) /\ ~mem (event_start t) log).
    { apply* Hdstart. }
    asserts Hrootnil: (t = t_root -> log = nil).
    { intros ->. destruct (classic (log = nil)) as [Hnil | Hne]; [exact Hnil|].
      false Hnmem. applys wf_log_nonempty_init Hwf Hne. }
    apply* wf_log_start_last.
  - (* StepEnd: append [event_end t] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_end_last.
  - (* StepLocalRead: append [event_read t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_read_last.
  - (* StepGlobalRead: append [event_read t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_read_last.
  - (* StepReadVolatile: append [event_read t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_read_last.
  - (* StepWrite: append [event_write t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_write_last.
  - (* StepWriteVolatile: append [event_write t x v] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    apply* wf_log_write_last.
  - (* StepSpawn: append [event_spawn t t'], with [t'] fresh *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _ & _ & _ & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem'). apply H5. apply* Hdspawned. }
    asserts Htneq: (t' <> t_root).
    { intros ->. apply H5. apply* Hdspawned. }
    apply* wf_log_spawn_last.
  - (* StepJoin: append [event_join t t'], with [t'] ended *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Htended: (mem (event_end t') log).
    { apply Hdend. eauto. }
    apply* wf_log_join_last.
  - (* StepLock: append [event_lock t l] -- [lock_read] unifies the
       "already touched" and "never touched" (defaulting to
       [(ls_free, root_commit)]) cases into a single constructor. *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & Hdunlock & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hlfree: (LibList.filter (fun e => touches_lock l e) log = nil \/
                     exists t'' log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_unlock t'' l).
    { match goal with Hpre : lock_read L l = (ls_free, ?cc) |- _ => rename Hpre into Hread end.
      unfold lock_read, read_default in Hread.
      destruct (classic (l \indom L)) as [Hindom|Hnotin].
      - right. asserts Hb: (binds L l (ls_free, c')).
        { applys binds_of_indom_read Hindom. case_if* in Hread. }
        apply* Hdunlock.
      - left. destruct (last_case (LibList.filter (fun e => touches_lock l e) log)) as [Hnil | (x & xs' & Heqf)].
        + exact Hnil.
        + exfalso. forwards [(t' & ->) | (t' & ->)]: filter_touches_lock_last_inv Heqf.
          * asserts Hex: (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t' l).
            { exists xs'. exact Heqf. }
            destruct (proj1 (Hdlock t' l) Hex) as (cw & Hb).
            lets* Hin: (indom_of_binds Hb).
          * asserts Hex: (exists t'' log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t'' l).
            { exists t' xs'. exact Heqf. }
            destruct (proj1 (Hdunlock l) Hex) as (cw & Hb).
            lets* Hin: (indom_of_binds Hb). }
    apply* wf_log_snoc_lock.
  - (* StepRelease: append [event_unlock t l] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply* Hdlock. }
    apply* wf_log_unlock_last.
Qed.

Hint Resolve inhab_thread : vcm.

Lemma inhab_vlock : Inhab (lock_state * commit).
  constructor. exists (ls_free, 0). tauto.
Qed.

Hint Resolve inhab_vlock : vcm.

(* ============================================================= *)
(* Reusable [describes]-conjunct preservation lemmas             *)
(* ------------------------------------------------------------- *)
(* As in the SharedMemory development: most [describes] conjuncts *)
(* are preserved "for free" by a step -- the appended event is    *)
(* not of the kind the conjunct constrains, and the thread/lock   *)
(* map is updated only in place. The lemmas below capture those   *)
(* generic cases (conjuncts 1-6,8); the replay conjunct (7) is    *)
(* the genuinely interesting one and stays inline in each case.   *)
(* Threads here are 4-tuples [(state, expr, delta, commit)].      *)
(* ============================================================= *)

(* Conjunct 1: spawned/initialised threads are in [dom T]. *)
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

(* Conjunct 2: unstarted threads are [state_new]. *)
Lemma describes_new_inplace : forall (log : Log.log) e (T : threads) t st e0 d0 c0,
    mem (event_start t) log ->
    st <> state_new ->
    (forall a b, e <> event_spawn a b) ->
    (forall a, e <> event_start a) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~ mem (event_start t2) log
                <-> exists e' d c, binds T t2 (state_new, e', d, c)) ->
    (forall t2, ((exists t1, mem (event_spawn t1 t2) (log & e)) \/ t2 = t_root) /\ ~ mem (event_start t2) (log & e)
                <-> exists e' d c, binds (T[t := (st, e0, d0, c0)]) t2 (state_new, e', d, c)).
Proof.
  introv Hsmem Hstne Hns Hnst Hd. intros t2. splits.
  - introv (Hdisj & Hnmem).
    asserts Hneq: (t2 <> t).
    { intros ->. apply Hnmem. rew_listx. left. exact Hsmem. }
    asserts (e' & d' & c' & Hbinds): (exists e' d c, binds T t2 (state_new, e', d, c)).
    { apply Hd. splits.
      - rew_listx in Hdisj.
        destruct Hdisj as [(t1 & Hmem) | ->].
        + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
          * left. exists* t1.
          * false (Hns _ _ (eq_sym Heq)).
        + right*.
      - intros Hc. apply Hnmem. rew_listx. left. exact Hc. }
    exists e' d' c'. apply~ binds_update_neq.
  - introv (e' & d' & c' & Hbinds).
    asserts Hneq: (t2 <> t).
    { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
    forwards~ Hbinds': binds_update_neq_inv Hbinds.
    asserts (Hdisj & Hnmem):
      (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root) /\ ~ mem (event_start t2) log).
    { apply Hd. exists e' d' c'. exact Hbinds'. }
    splits.
    + destruct Hdisj as [(t1 & Hmem) | Hmem].
      * left. exists t1. rew_listx*.
      * right. rew_listx*.
    + intros Hc. rew_listx in Hc. destruct Hc as [Hc | Heq].
      * exact (Hnmem Hc).
      * false (Hnst _ (eq_sym Heq)).
Qed.

(* Conjunct 3: ended threads are [state_terminated] with empty staging. *)
Lemma describes_ended_inplace : forall (log : Log.log) e (T : threads) t st e0 d0 c0,
    ~ mem (event_end t) log ->
    st <> state_terminated ->
    (forall a, e <> event_end a) ->
    (forall t0, mem (event_end t0) log <-> exists e' c, binds T t0 (state_terminated, e', empty_diff, c)) ->
    (forall t0, mem (event_end t0) (log & e) <-> exists e' c, binds (T[t := (st, e0, d0, c0)]) t0 (state_terminated, e', empty_diff, c)).
Proof.
  introv Hrnmem Hstne Hne Hd. intros t0. splits.
  - introv Hmem.
    rew_listx in Hmem. destruct Hmem as [Hmem | Heq]; [| false (Hne _ (eq_sym Heq))].
    asserts Hneq: (t0 <> t).
    { intros ->. exact (Hrnmem Hmem). }
    asserts (e' & c' & Hbinds): (exists e' c, binds T t0 (state_terminated, e', empty_diff, c)).
    { apply~ Hd. }
    exists e' c'. apply~ binds_update_neq.
  - introv (e' & c' & Hbinds).
    destruct (classic (t0 = t)) as [->|Hneq].
    + apply binds_update_same_inv in Hbinds. congruence.
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      rew_listx. left. apply* Hd.
Qed.

(* Conjunct 4: started, unfinished threads are [state_running]. *)
Lemma describes_running_inplace : forall (log : Log.log) e (T : threads) t e0 d0 c0,
    mem (event_start t) log ->
    ~ mem (event_end t) log ->
    (forall a, e <> event_start a) ->
    (forall a, e <> event_end a) ->
    (forall t0, mem (event_start t0) log /\ ~ mem (event_end t0) log <-> exists e' d c, binds T t0 (state_running, e', d, c)) ->
    (forall t0, mem (event_start t0) (log & e) /\ ~ mem (event_end t0) (log & e)
                <-> exists e' d c, binds (T[t := (state_running, e0, d0, c0)]) t0 (state_running, e', d, c)).
Proof.
  introv Hsmem Hrnmem Hnst Hne Hd. intros t0. splits.
  - introv (Hsmem0 & Henmem0).
    destruct (classic (t0 = t)) as [->|Hneq].
    + do 3 eexists. apply binds_update_same.
    + rew_listx in Hsmem0. destruct Hsmem0 as [Hsmem0 | Heq]; [| false (Hnst _ (eq_sym Heq))].
      asserts Henmem0': (~mem (event_end t0) log).
      { introv Hmem. apply Henmem0. rew_listx*. }
      asserts (e' & d' & c' & Hbinds): (exists e' d c, binds T t0 (state_running, e', d, c)).
      { apply Hd. split*. }
      exists e' d' c'. apply~ binds_update_neq.
  - introv (e' & d' & c' & Hbinds).
    destruct (classic (t0 = t)) as [->|Hneq].
    + apply binds_update_same_inv in Hbinds. inverts Hbinds.
      split.
      * rew_listx. left. exact Hsmem.
      * introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
        -- exact (Hrnmem Hmem).
        -- false (Hne _ (eq_sym Heq)).
    + forwards~ Hbinds': binds_update_neq_inv Hbinds.
      asserts (Hsmem0 & Henmem0): (mem (event_start t0) log /\ ~mem (event_end t0) log).
      { apply Hd. exists e' d' c'. exact Hbinds'. }
      split.
      * rew_listx. left. exact Hsmem0.
      * introv Hmem. rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
        -- exact (Henmem0 Hmem).
        -- false (Hne _ (eq_sym Heq)).
Qed.

(* Conjunct 5: held locks. *)
Lemma describes_locked_snoc : forall (log : Log.log) e (L : locks),
    (forall l, ~ touches_lock l e) ->
    (forall t l, (exists log', LibList.filter (fun e0 => touches_lock l e0) log = log' & event_lock t l)
                 <-> exists c, binds L l (ls_held t, c)) ->
    (forall t l, (exists log', LibList.filter (fun e0 => touches_lock l e0) (log & e) = log' & event_lock t l)
                 <-> exists c, binds L l (ls_held t, c)).
Proof.
  introv Hnt Hd. intros t l. rew_listx. cases_if as Hc.
  - false (Hnt l Hc).
  - rew_list. apply Hd.
Qed.

(* Conjunct 6: free locks. *)
Lemma describes_free_snoc : forall (log : Log.log) e (L : locks),
    (forall l, ~ touches_lock l e) ->
    (forall l, (exists t log', LibList.filter (fun e0 => touches_lock l e0) log = log' & event_unlock t l)
               <-> exists h, binds L l (ls_free, h)) ->
    (forall l, (exists t log', LibList.filter (fun e0 => touches_lock l e0) (log & e) = log' & event_unlock t l)
               <-> exists h, binds L l (ls_free, h)).
Proof.
  introv Hnt Hd. intros l. rew_listx. cases_if as Hc.
  - false (Hnt l Hc).
  - rew_list. apply Hd.
Qed.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & _ & Hroot).
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: log' = log & event_start t, T' = T[t := running] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts* HtinX: (t \indom T).
    asserts HnewX: (exists e' d' c', binds T t (state_new, e', d', c')). { do 3 eexists; eassumption. }
    asserts Htnend: (~ mem (event_end t) log).
    { intros Hc. apply Hdend in Hc as (e2 & c2 & Hb). destruct HnewX as (e3 & d3 & c3 & Hb3).
      forwards~ Hcontra: binds_inj Hb Hb3. }
    splits.
    + applys* describes_spawned_inplace.
    + (* 2. New threads (interesting: t leaves the new set) *)
      intros t2. splits.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & c' & ts' & Hbinds): (exists e' d c', binds T t2 (state_new, e', d, c')).
        { apply (Hdnew t2). splits.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | ->].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e' c' ts'.
        apply~ binds_update_neq.
      * introv (e' & c' & ts' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmem):
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists*. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmem; assumption|congruence].
    + applys* describes_ended_inplace.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- asserts Hmem': (mem (event_start t0) log).
           { rew_listx in Hmem. destruct Hmem as [Hmem|Heq]; [assumption|congruence]. }
           asserts Hnend: (~mem (event_end t0) log).
           { intros contra. apply Hnmem. rew_listx*. }
           asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
           { apply (Hdrunning t0). split; assumption. }
           exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds.
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              asserts (e3 & h3 & Hbinds'): (exists e3 h3, binds T t (state_terminated, e3, empty_diff, h3)).
              { apply (Hdend t). exact contra. }
              destruct HnewX as (e' & d' & c' & Hbinds).
              forwards*: binds_inj Hbinds Hbinds'.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      exists D TC LC VC. eexists. splits*.
      * (* play_log (log & event_start t) ... = (D, TC, G, LC, VC): PlayStart is a no-op *)
        applys PlaySnoc Hplay. apply PlayStart.
      * (* Thread deltas: staging areas and commits unchanged by StepStart *)
        intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- (* t is now running; D[t] and TC[t] come from pre-step binds *)
           asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc. exists state_running e. apply binds_update_same.
        -- (* t0 ≠ t: unchanged *)
           forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        asserts*: (t \indom D).
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepEnd: log' = log & event_end t, T' = T'[t := terminated] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    unfolds do_commit. simpl in H5.
    asserts Ht: (T[t] = (state_running, te_ret r, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_ret r, d, c) in H5.
    inverts H5.
    asserts (HsmemX & HenmemX): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts* HtinX: (t \indom T).
    splits.
    + rewrite~ update_update. applys* describes_spawned_inplace.
    + rewrite~ update_update. applys* describes_new_inplace.
    + (* 3. Ended threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). exists (te_ret r) d c. assumption. }
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
        -- asserts Hneq: (t0 <> t).
           { intros ->. exact (Henmem Hmem). }
           asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
           { apply (Hdend t0). exact Hmem. }
           exists e2 h2. apply~ binds_update_neq. apply~ binds_update_neq.
        -- inverts Heq. exists (te_ret r) c'. apply binds_update_same.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. inverts Hbinds. rew_listx*.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds2.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hneq: (t0 <> t).
        { intros ->. apply Hnmem. rew_listx*. }
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        exists e2 d2 h2. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
           forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds2. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := c']) LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayEnd _ _ _ _ _ _ c c' d); auto.
        -- apply HdomTC in Htin. erewrite* binds_eq_indom_read.
        -- apply HdomD in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := c'][t] = c'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_terminated (te_ret r). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards~ Hin2: indom_update_inv Hin1.
           destruct Hin2 as [->|Hin2]. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin2.
           asserts Hd0: (D[t := empty][t0] = D[t0]). { rew_map*. }
           asserts Htc0: (TC[t := c'][t0] = TC[t0]). { rew_map*. }
           rewrite Hd0, Htc0.
           exists ts' e''. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        asserts*: (t \indom D).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
  - (* StepReadLocal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts* HtinX: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      exists D TC LC VC. eexists. splits*.
      * applys PlaySnoc Hplay. applys* PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (K (ret_val v)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        branches; auto_star.
  - (* StepReadGlobal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts* HtinX: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      exists D TC LC VC. eexists. splits*.
      * applys PlaySnoc Hplay. applys* PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (K (ret_val v)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepReadVolatile: log' = log & event_read t x v, T' = T[t := running K(v)] with pulled commit *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    unfolds pull_volatile, do_merge.
    replace (T[t]) with (state_running, te_exp e, d, c) in H9 by forwards*: read_of_binds T t.
    inverts H9.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts* HtinX: (t \indom T).
    splits.
    + rewrite~ update_update. applys* describes_spawned_inplace.
    + rewrite~ update_update. applys* describes_new_inplace.
    + rewrite~ update_update. applys* describes_ended_inplace.
    + rewrite~ update_update. applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      asserts Hvceq: (vc_read V x = vc_read VC x).
      { rewrite Hveq. reflexivity. }
      exists D (TC[t := c'']) LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        rewrite Hvceq.
        apply (PlayReadVolatile _ _ _ _ _ t x v c c''); auto.
        apply HdomTC in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htc_new: ((TC[t := c''])[t] = c''). { rew_map*. }
           rewrite Hd, Htc_new.
           exists state_running (K v). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards~ Hin2: indom_update_inv Hin1.
           destruct Hin2 as [->|Hin2]. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin2.
           asserts Htc0: ((TC[t := c''])[t0] = TC[t0]). { rew_map*. }
           rewrite Htc0.
           exists ts' e''. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
  - (* StepWrite: log' = log & event_write t x v, T' = T[t := running K(void)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts* HtinX: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds.  }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := d[x := v]]) TC LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayWrite _ _ _ _ _ _ _ _ d); auto.
        asserts* Hmem: (t \indom T).
        erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := d[x:=v]])[t] = d[x:=v]). { rew_map*. }
           rewrite Hd_new, Htc.
           exists state_running (K void). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin'.
           asserts Hd0: ((D[t := d[x:=v]])[t0] = D[t0]). { rew_map*. }
           rewrite Hd0.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
  - (* StepWriteVolatile: log' = log & event_write t x v, T' = T[t := running K(void)] via commit then merge *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    unfolds push_volatile, do_commit.
    rewrite~ read_update_same in H8.
    inverts H8.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts* HtinX: (t \indom T).
    splits.
    + repeat rewrite update_update; try typeclass. applys* describes_spawned_inplace.
    + repeat rewrite update_update; try typeclass. applys* describes_new_inplace.
    + repeat rewrite update_update; try typeclass. applys* describes_ended_inplace.
    + repeat rewrite update_update; try typeclass. applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      subst VC.
      exists (D[t := empty]) (TC[t := c']) LC (V[x := c'']). eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayWriteVolatile _ _ _ _ _ t x v d c c' c''); auto.
        -- apply HdomD in Htin. erewrite* binds_eq_indom_read.
        -- apply HdomTC in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := empty])[t] = empty). { rew_map*. }
           asserts Htc_new: ((TC[t := c'])[t] = c'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_running (K void). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards~ Hin2: indom_update_inv Hin1.
           destruct Hin2 as [->|Hin2]. { congruence. }
           forwards~ Hin3: indom_update_inv Hin2.
           destruct Hin3 as [->|Hin3]. { congruence. }
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin3.
           asserts Hd0: ((D[t := empty])[t0] = D[t0]). { rew_map*. }
           asserts Htc0: ((TC[t := c'])[t0] = TC[t0]). { rew_map*. }
           rewrite Hd0, Htc0.
           exists ts' e''. apply~ binds_update_neq. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        asserts*: (t \indom D).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem.
        asserts*: (t \indom TC).
        rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
  - (* StepSpawn: log' = log & event_spawn t t', T' = T'[t := ...][t' := new] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts* Hneq: (t' <> t).
    unfolds push_thread, do_commit. simpl in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    inverts H7.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      asserts Hdom: (dom (T[t:=(state_running, K t', d, c)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, K t', \{}, c')]
                      [t':=(state_new, te_exp e', \{}, c')]) =
                    (union (union (dom T) (single t')) (single t))).
                    { rewrite (dom_update t' (state_new, te_exp e', \{}, c')
                                             (T[t:=(state_running, K t', d, c)]
                                               [t':=(state_new, te_exp e', \{}, 0)]
                                               [t:=(state_running, K t', \{}, c')])).
                      rewrite dom_update, dom_update, dom_update.
                      rew_set. intros x. rew_set. splits*. }
      replace (dom (T[t:=(state_running, K t', d, c)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, K t', \{}, c')]
                      [t':=(state_new, te_exp e', \{}, c')])) with
               (union (union (dom T) (single t')) (single t)).
      rew_set.
      splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
           ++ asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t1. }
              autos.
           ++ inverts Heq. autos*.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
           autos.
      * intros Hin. destruct Hin as [[Hin | ->] | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- left. exists t. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)

      asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
      { intros (t1 & Hmem). apply H5. apply (Hdspawned t'). left. exists* t1. }
      asserts Hnostart: (~mem (event_start t') log).
      { intros Hmemst.
        asserts (l1 & l2 & Heq2): (exists l1 l2, log = l1 ++ event_start t' :: l2).
        { apply~ mem_inv_middle. }
        forwards [(t1 & Hmem) | Hmem]: Hspawn Heq2.
        - false Hnospawn. exists t1. rewrite Heq2. rew_listx*.
        - apply H5. apply* (Hdspawned t'). }
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        destruct (classic (t2 = t')) as [->|Hneq2].
        -- exists (te_exp e') (empty : diff) c'. apply binds_update_same.
        -- destruct (classic (t2 = t)) as [->|Hneq3].
           ++ false Hnmem. rew_listx*.
           ++ asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
              { apply (Hdnew t2). split.
                - rew_listx in Hdisj.
                  destruct Hdisj as [(t1 & Hmem) | ->].
                  + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
                    * left. exists* t1.
                    * congruence.
                  + right*.
                - intros Hc. apply Hnmem. rew_listx*. }
              exists e2 h2 ts2.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        destruct (classic (t2 = t')) as [->|Hneq2].
        -- split.
           ++ left. exists t. rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq].
              ** false Hnostart. exact contra.
              ** congruence.
        -- forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
           destruct (classic (t2 = t)) as [->|Hneq3].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              forwards Hbinds4: binds_update_neq_inv Hbinds3; auto.
              asserts (Hdisj & Hnmemst):
                (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
                  /\ ~mem (event_start t2) log).
              { apply (Hdnew t2). exists e2 h2 ts2. exact Hbinds4. }
              split.
              ** destruct Hdisj as [(t1 & Hmem) | Hmem].
                 --- left. exists t1. rew_listx*.
                 --- right. rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq].
                 --- exact (Hnmemst contra).
                 --- congruence.
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        asserts Hneq': (t0 <> t').
        { intros ->. false* H5. }
        exists e2 h2.
        apply~ binds_update_neq. apply~ binds_update_neq.
        apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq2].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              forwards Hbinds4: binds_update_neq_inv Hbinds3; auto.
              rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds4.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        asserts Hneq': (t0 <> t').
        { intros ->. false* H5. }
        destruct (classic (t0 = t)) as [->|Hneq2].
        -- exists (K t') (empty : diff) c'.
           apply~ binds_update_neq. apply binds_update_same.
        -- exists e2 d2 h2.
           apply~ binds_update_neq. apply~ binds_update_neq.
           apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
           destruct (classic (t0 = t)) as [->|Hneq2].
           ++ apply binds_update_same_inv in Hbinds1.
              asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
              { apply (Hdrunning t). eauto. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
           ++ forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              forwards Hbinds4: binds_update_neq_inv Hbinds3; auto.
              asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
              { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds4. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty][t' := empty]) (TC[t := c'][t' := c']) LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlaySpawn _ _ _ _ _ _ _ c c' d); auto.
        -- apply HdomTC in Htin. erewrite* binds_eq_indom_read.
        -- apply HdomD in Htin. erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- asserts Hd_t': ((D[t := empty][t' := empty])[t'] = empty).
           { rewrite read_update_same. auto. }
           asserts Htc_t': ((TC[t := c'][t' := c'])[t'] = c').
           { rewrite read_update_same. auto. }
           rewrite Hd_t', Htc_t'.
           exists state_new (te_exp e'). apply binds_update_same.
        -- destruct (classic (t0 = t)) as [->|Hneq2].
           ++ asserts Hd_t: ((D[t := empty][t' := empty])[t] = empty).
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              asserts Htc_t: ((TC[t := c'][t' := c'])[t] = c').
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              rewrite Hd_t, Htc_t.
              exists state_running (K t').
              apply~ binds_update_neq. apply binds_update_same.
           ++ forwards~ Hin1: indom_update_inv Hin.
              destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1.
              destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2.
              destruct Hin3 as [->|Hin3]. { congruence. }
              forwards~ Hin4: indom_update_inv Hin3.
              destruct Hin4 as [->|Hin4]. { congruence. }
              asserts Hd0: ((D[t := empty][t' := empty])[t0] = D[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              asserts Htc0: ((TC[t := c'][t' := c'])[t0] = TC[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              rewrite Hd0, Htc0.
              forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin4.
              exists ts' e''.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set. repeat (branches; auto).
      * introv Hmem.
        rew_dom.
        rew_set in Hmem.
        rew_set. repeat (branches; auto).
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts* Hneq: (t' <> t).
    unfolds pull_thread, do_merge.
    asserts Ht': (T[t'] = (state_terminated, te_ret r, empty, c')).
    { apply* read_of_binds. }
    rewrite Ht' in H8.
    asserts Ht: (T[t] = (state_running, te_exp e, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, c) in H8.
    inverts H8.
    apply binds_update_same_inv in H9. inverts H9.
    rewrite~ update_update.
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts* HtinX: (t \indom T).
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      asserts Htin': (t' \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards (ts_old' & e_old' & Hbinds_delta'): Hdelta t' Htin'.
      forwards* Heq: binds_inj H3 Hbinds_delta.
      forwards* Heq': binds_inj H5 Hbinds_delta'.
      exists D (TC[t := c'']) LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayJoin _ _ _ _ _ _ _ c c' c''); auto.
        -- inverts Heq.
           apply HdomTC in Htin.
           applys* binds_of_indom_read.
        -- inverts Heq'.
           applys* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- asserts Hd_t: (D[t] = d). { congruence. }
           asserts Htc_t: ((TC[t := c''])[t] = c''). { rewrite read_update_same. auto. }
           rewrite Hd_t, Htc_t.
           exists state_running (K r). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           asserts Htc0: ((TC[t := c''])[t0] = TC[t0]). { rewrite~ read_update_neq. }
           rewrite Htc0.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. branches; auto_star.
      * introv Hmem.
        rew_dom.
        rew_set in Hmem. rew_set.
        branches; auto_star.
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...], L' = L[l := held t] --
       [lock_read] unifies the "already touched"/"never touched" cases into one
       constructor; only the replay conjunct (7) genuinely branches on [l \indom L]. *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    match goal with Hpre : lock_read L l = (ls_free, c') |- _ => rename Hpre into Hread end.
    unfolds pull_lock, do_merge.
    rewrite Hread in H8.
    asserts Ht: (T[t] = (state_running, te_exp e, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, c) in H8.
    inverts H8.
    apply binds_update_same_inv in H9. inverts H9.
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts* HtinX: (t \indom T).
    splits.
    + rewrite~ update_update. applys* describes_spawned_inplace.
    + rewrite~ update_update. applys* describes_new_inplace.
    + rewrite~ update_update. applys* describes_ended_inplace.
    + rewrite~ update_update. applys* describes_running_inplace.
    + (* 5. Locked locks *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter grows by event_lock t l, l now held *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           exists c'. apply binds_update_same.
        -- intros (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds.
           inverts Hbinds.
           exists~ (LibList.filter (fun e => touches_lock l e) log).
      * (* l0 ≠ l: filter and L unchanged *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           forwards ((h2 & Hbinds) & Hbinds'): (Hdlock t0 l0). { exists log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdlock t0 l0). exists h2. exact Hbinds'.
    + (* 6. Unlocked locks *)
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: l now held, both sides false *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: filter and L unchanged *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           forwards (h2 & Hbinds): (proj1 (Hdunlock l0)). { exists t0 log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           forwards (t0 & log' & Hfilt): (proj2 (Hdunlock l0)). { exists h2. exact Hbinds'. }
           exists t0 log'. exact Hfilt.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj Hbinds_delta H3.
      asserts HLCeq: (lc_read LC l = c').
      { asserts Hread': (lock_read L l = (ls_free, c')). { exact Hread. }
        unfold lock_read, read_default in Hread'.
        destruct (classic (l \indom L)) as [Hindom|Hnotin].
        - asserts Hb: (binds L l (ls_free, c')).
          { applys binds_of_indom_read Hindom. case_if* in Hread'. }
          forwards (ls0 & Hbinds_l0): Hlocks Hindom.
          forwards~ Heql: binds_inj Hb Hbinds_l0.
        - case_if* in Hread'. inverts Hread'.
          asserts Hlcnotin: (l \notindom LC).
          { intro Hin. apply Hnotin. apply* HdomLC. }
          unfold lc_read. apply read_default_notindom. exact Hlcnotin. }
      rewrite~ update_update.
      exists D (TC[t := c'']) LC VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        rewrite <- HLCeq.
        apply (PlayLock _ _ _ _ _ _ _ c c''); auto.
        inverts Heq.
        apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- asserts~ Hd_t: (D[t] = d).
           rewrite read_update_same.
           rewrite Hd_t.
           exists state_running (K void). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           asserts Htc0: ((TC[t := c''])[t0] = TC[t0]). { rewrite~ read_update_neq. }
           rewrite Htc0.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- rewrite <- HLCeq. exists (ls_held t). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin1.
           exists ls0'. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. branches; auto_star.
      * introv Hmem. rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem. forwards Hin: HdomLC Hmem. rew_dom. rew_set. auto.
  - (* StepRelease: log' = log & event_unlock t l, T' = T[t := ...], L' = L'[l := free] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    unfolds push_lock, do_commit.
    asserts Ht: (T[t] = (state_running, te_exp e, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, c) in H7.
    asserts Hl: (L[l] = (ls_held t, c')).
    { apply* read_of_binds. }
    replace (L[l]) with (ls_held t, c') in H7.
    inverts H7.
    rewrite~ update_update.
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + (* 5. Locked locks *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter gains event_unlock; l now free → locked is false *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- intros (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 ≠ l: two layers of update, both at l ≠ l0 *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           forwards (h2 & Hbinds): (proj1 (Hdlock t0 l0)). { exists log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           apply (Hdlock t0 l0). exists h2. exact Hbinds2.
    + (* 6. Unlocked locks *)
      rewrite~ update_update.
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: filter gains event_unlock t l; l now free → unlocked is true *)
        unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (t0 & log' & Hfilt). exists c''. apply binds_update_same.
        -- intros (h2 & Hbinds).
           exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 ≠ l: two layers of update, both at l ≠ l0 *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           forwards (h2 & Hbinds): (proj1 (Hdunlock l0)). { exists t0 log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards (t0 & log' & Hfilt): (proj2 (Hdunlock l0)). { exists h2. exact Hbinds1. }
           exists t0 log'. exact Hfilt.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC).
      apply binds_update_same_inv in H8. inverts H8.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj  H3 Hbinds_delta.
      asserts Hlin: (l \indom L). { apply* indom_of_binds. }
      forwards (ls & Hbinds_l): Hlocks Hlin.
      forwards~ Heq': binds_inj H5 Hbinds_l.
      exists (D[t := empty]) (TC[t := c'']) (LC[l := c'']) VC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayUnlock _ _ _ _ _ _ _ c c'' d); auto.
        -- inverts Heq.
           apply* binds_of_indom_read.
        -- inverts Heq.
           apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- repeat rewrite read_update_same.
           exists state_running (K void). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           repeat rewrite~ read_update_neq.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- asserts Heql: (lc_read (LC[l := c'']) l = c'').
           { unfold lc_read. apply read_default_update_same. }
           rewrite Heql.
           exists (ls_free). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards~ Hin2: indom_update_inv Hin1.
           destruct~ Hin2 as [->|Hin2].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin2.
           asserts Heql: (lc_read (LC[l := c'']) l0 = lc_read LC l0).
           { unfold lc_read. apply read_default_update_neq. congruence. }
           rewrite Heql.
           exists ls0'. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        forwards Hmem1: indom_update_inv Hmem; [typeclass|].
        destruct Hmem1 as [->|Hmem1].
        -- apply indom_update_same; typeclass.
        -- apply* indom_update_of_indom. apply* indom_update_of_indom.
Qed.
