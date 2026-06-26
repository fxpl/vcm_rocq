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
    describes init_log (init_cfg e).
Proof.
  intros.
  unfolds init_log, init_cfg.
  splits; rew_list.
  - introv.
    splits.
    + introv Hsrc.
      destruct Hsrc as [(t1 & contra)|Hmem].
      * do 2 inverts contra as contra.
      * inverts Hmem as Hmem; [| inverts Hmem].
        rew_dom. rew_set. autos.
    + introv Hdom.
      rew_dom. rew_set in Hdom.
      branches.
      * forwards*: indom_empty_inv.
      * subst. right. rew_listx*.
  - introv.
    splits.
    + introv (Hsrc & Hnmem).
      destruct Hsrc as [(t1 & contra)|Hmem].
      * do 2 inverts contra as contra.
      * inverts Hmem as Hmem; [| inverts Hmem].
        exists. apply binds_update_same.
    + introv (e' & d & c & Hbinds).
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
      do 2 inverts Hmem as Hmem.
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
      rew_listx in Heq. cases_if.
      forwards*: nil_eq_last_inv.
    + introv (c & contra).
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - introv.
    splits.
    + introv (t & log' & Heq).
      rew_listx in Heq. cases_if.
      forwards*: nil_eq_last_inv.
    + introv (c & contra).
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - introv.
    exists.
    splits.
    + replaces (event_init t_root :: nil) with (nil & event_init t_root).
      { rew_list*. }
      repeat constructors.
      unfolds commit_fresh, empty_graph.
      intros contra. forwards*: indom_empty_inv.
    + introv Hdom.
      rew_dom. rew_set in Hdom. branches.
      * forwards*: indom_empty_inv.
      * subst.
        exists.
        replace (empty[t_root:=empty][t_root]) with (empty_diff) by rewrite* read_update_same.
        replace (empty[t_root:=root_commit][t_root]) with (root_commit) by rewrite* read_update_same.
        apply binds_update_same.
    + introv contra.
      forwards*: indom_empty_inv.
    + rew_dom. introv Hdom. rew_set in *.
      branches; auto_star.
      forwards*: indom_empty_inv.
    + rew_dom. introv Hdom. rew_set in *.
      branches; auto_star.
      forwards*: indom_empty_inv.
    + introv contra.
      forwards*: indom_empty_inv.
    + introv contra.
      forwards*: indom_empty_inv.
  - exists* t_root.
Qed.

Theorem init_cfg_wf :
  forall e,
    wf_cfg (init_cfg e).
Proof.
  introv. unfolds init_cfg, graph_root, empty_graph.
  splits.
  - apply init_graph_wf.
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
Qed.

Lemma get_uncommitted'_has_sync :
  forall log t acc,
    Exists is_sync_event log ->
    get_uncommitted' t log acc = get_uncommitted' t log nil.
Proof.
  introv Hex.
  gen acc.
  induction Hex; intros; simpls; cases_if~.
Qed.

Lemma get_uncommitted'_no_sync :
  forall log t acc,
    ~Exists is_sync_event log ->
    get_uncommitted' t log acc = acc ++ log.
Proof.
  intros log.
  induction log; introv Hnex; simpls; rew_list~.
  cases_if~.
  - false Hnex. constructors*.
  - rew_listx in Hnex. rew_logic in Hnex. unpack.
    rewrite~ IHlog. rew_list~.
Qed.

Lemma get_uncommited_inv :
  forall log t,
    exists log', log = log' ++ get_uncommitted t log.
Proof.
  intros log t.
  unfolds get_uncommitted.
  induction log; simpls.
  - exists* (@nil event).
  - unpack. destruct (classic (Exists is_sync_event log)).
    + rewrite~ get_uncommitted'_has_sync. exists (a :: log'). rew_list*.
    + cases_if.
      * rewrite~ get_uncommitted'_no_sync. exists (a :: nil). rew_list*.
      * rewrite~ get_uncommitted'_no_sync. exists (@nil event). rew_list*.
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
    + exists. applys* StepSpawn.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_cfg :
  forall cfg cfg' log log',
    wf_cfg cfg ->
    step (cfg, log) (cfg', log') ->
    wf_cfg cfg'.
Proof.
  destruct cfg as ((T & G) & L).
  introv (Hwf & HdomT & HdomL) Hstep.
  inverts Hstep.
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - unfolds do_commit.
    replace (T[t]) with (state_running, te_ret r, d, c) in H7 by forwards*: read_of_binds.
    inverts H7.
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
  - splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - unfolds push_thread, do_commit.
    asserts* Hneq: (t <> t').
    rewrite~ read_update_neq in H9.
    rewrite~ read_update_same in H9.
    rewrite~ read_update_neq in H9.
    rewrite~ read_update_same in H9.
    inverts H9. splits*.
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
    replace (T[t']) with (state_terminated, te_ret r, empty_diff, c') in H10 by forwards*: read_of_binds t'.
    replace (T[t]) with (state_running, te_exp e, d, c) in H10 by forwards*: read_of_binds T t.
    inverts H10. splits*.
    + apply* graph_merge_wf.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards* Hbinds'': binds_update_neq_inv Hbinds'.
  - unfolds pull_lock, do_merge.
    replace (L[l0]) with (ls_free, c') in H10 by forwards*: read_of_binds l0.
    replace (T[t]) with (state_running, te_exp e, d, c) in H10 by forwards*: read_of_binds T t.
    inverts H10. splits.
    + apply* graph_merge_wf.
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
      * forwards* Hbinds': binds_update_neq_inv Hbinds.
  - splits~.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards*: binds_update_neq_inv Hbinds.
    + introv Hbinds.
      destruct (classic (l = l0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts* Heq.
      * forwards* Hbinds': binds_update_neq_inv Hbinds.
  - unfolds push_lock, do_commit.
    replace (T[t]) with (state_running, te_exp e, d, c) in H9 by forwards*: read_of_binds T t.
    replace (L[l0]) with (ls_held t, c') in H9 by forwards*: read_of_binds l0.
    inverts H9. splits.
    + apply* graph_commit_wf.
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
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & Hinit & Hroot).
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: log' = log & event_start t *)
    destruct Hdesc as (_ & Hdstart & _).
    asserts (Hsrc & Hnmem): (((exists t1, mem (event_spawn t1 t) log) \/ mem (event_init t) log) /\ ~mem (event_start t) log).
    { apply* Hdstart. }
    splits 9.
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
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepEnd: log' = log & event_end t *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits 9.
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
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * rew_listx. splits.
        -- apply~ Hend.
        -- simpl. intros ->. apply Henmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepReadLocal: log' = log & event_read t x v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits 9.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    +introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepReadGlobal: log' = log & event_read t x v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits 9.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    +introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hrnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepWrite: log' = log & event_write t x v *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _).
    asserts (Hsmem & Hwnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    splits 9.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    +introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hwnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepSpawn: log' = log & event_spawn t t' *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _ & _ & _ & (t'' & Hinit')).
    asserts ->: (t'' = t_root).
    { apply mem_inv_middle in Hinit' as (l1 & l2 & Heq). applys* Hinit. }
    asserts Hrmem: (t_root \indom T).
    { apply* Hdspawned. }
    asserts (Hsmem & Hsnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
    { intros (t1 & Hmem').
      match goal with Hni : t' \notindom T |- _ => apply Hni end.
      apply (Hdspawned t'). left. exists t1. exact Hmem'. }
    splits 9.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * intros (t1' & Hmem''). apply~ Huspawn. exists t1'.
        rew_listx. rew_listx in Hmem''.
        branches; autos.
        match goal with H : event_spawn _ _ = event_spawn _ _ |- _ => inverts H end.
        false Hnospawn. exists t1. rew_listx~.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    +introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hsnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned: event_spawn t t' with t' fresh, t' <> t_root *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepJoin: log' = log & event_join t t' *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Htended: (mem (event_end t') log).
    { apply (Hdend t'). eauto. }
    splits 9.
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
      introv Heq <- Hneq Hneq'.
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
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepLock: log' = log & event_lock t l (free lock) *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & _ & Hdunlock & _).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Hwflog: (wf_log log). { splits 9; assumption. }
    applys wf_log_snoc_lock Hwflog Hsmem Hlnmem.
    right. apply (proj2 (Hdunlock l)).
    match goal with Hbf : binds L l (ls_free, ?hh) |- _ => exists hh; exact Hbf end.
  - (* StepLockFresh: log' = log & event_lock t l (never-acquired lock) *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & Hdunlock & _).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Hwflog: (wf_log log). { splits 9; assumption. }
    applys wf_log_snoc_lock Hwflog Hsmem Hlnmem.
    left. destruct (last_case (LibList.filter (fun e => touches_lock l e) log)) as [Hnil | (x & xs' & Heqf)].
    + exact Hnil.
    + exfalso. forwards [(t' & ->) | (t' & ->)]: filter_touches_lock_last_inv Heqf.
      * asserts Hex: (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t' l).
        { exists xs'. exact Heqf. }
        apply (Hdlock t' l) in Hex. destruct Hex as (hx & Hb).
        lets Hin: (indom_of_binds Hb).
        match goal with Hni : l \notindom L |- _ => apply Hni; exact Hin end.
      * asserts Hex: (exists t0 log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t0 l).
        { exists t' xs'. exact Heqf. }
        apply (Hdunlock l) in Hex. destruct Hex as (hx & Hb).
        lets Hin: (indom_of_binds Hb).
        match goal with Hni : l \notindom L |- _ => apply Hni; exact Hin end.
  - (* StepRelease: log' = log & event_unlock t l *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & _).
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply (Hdlock t l). eauto. }
    splits 9.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
      rew_listx. rew_listx in Hmem'. branches; autos.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Hustart l1 l2' t0).
      rew_listx. rew_listx in contra. branches; autos.
    +introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hspawn.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      apply* Hjoin.
    + introv Heq <- Hneq Hneq'.
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
    + (* init initialises root and is first *)
      introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      apply* Hinit.
    + (* root is never spawned *)
      introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
Qed.

Hint Resolve inhab_thread : vcm.

Lemma inhab_vlock : Inhab (lock_state * commit).
  constructor. exists (ls_free, 0). tauto.
Qed.

Hint Resolve inhab_vlock : vcm.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Hspawn & Hjoin & Hstart & Hend & Hlock & Hinit & Hroot).
  inversion Hstep; substs; clear Hstep.
  - (* StepStart: log' = log & event_start t, T' = T[t := running] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin. destruct Hin as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Hdom: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Hdom).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      intros t2. splits.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & c' & ts' & Hbinds): (exists e' d c', binds T t2 (state_new, e', d, c')).
        { apply (Hdnew t2). splits.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e' c' ts'. exact Hbinds'. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmem; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
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
              forwards*: binds_inj Hbinds'.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      exists D TC LC. eexists. splits*.
      * (* play_log (log & event_start t) ... = (D, TC, G, LC): PlayStart is a no-op *)
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepEnd: log' = log & event_end t, T' = T'[t := terminated] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    unfolds do_commit. simpl in H5.
    asserts Ht: (T[t] = (state_running, te_ret r, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_ret r, d, c) in H5.
    inverts H5.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t1. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Hdom: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Hdom).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). exists (te_ret r) d c. assumption. }
      intros t2. splits.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). splits.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2.
        apply~ binds_update_neq.
        apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
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
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds2. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := c']) LC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayEnd _ _ _ _ _ c c' d); auto.
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepReadLocal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Hdom: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Hdom).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      exists D TC LC. eexists. splits*.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepReadGlobal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Hdom: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Hdom).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      exists D TC LC. eexists. splits*.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepWrite: log' = log & event_write t x v, T' = T[t := running K(void)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Hdom: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Hdom).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds.  }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := d[x := v]]) TC LC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayWrite _ _ _ _ _ _ _ d).
        asserts* Hmem: (t \indom T).
        erewrite* binds_eq_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := d[x:=v]])[t] = d[x:=v]). { rew_map*. }
           rewrite Hd_new, Htc.
           exists state_running (te_exp (K void)). apply binds_update_same.
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepSpawn: log' = log & event_spawn t t', T' = T'[t := ...][t' := new] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    asserts* Hneq: (t' <> t).
    unfolds push_thread, do_commit. simpl in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    rewrite~ read_update_neq in H7. rewrite~ read_update_same in H7.
    inverts H7.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      asserts Hdom: (dom (T[t:=(state_running, te_exp (K t'), d, c)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, te_exp (K t'), \{}, c')]
                      [t':=(state_new, te_exp e', \{}, c')]) =
                    (union (union (dom T) (single t')) (single t))).
                    { rewrite (dom_update t' (state_new, te_exp e', \{}, c')
                                             (T[t:=(state_running, te_exp (K t'), d, c)]
                                               [t':=(state_new, te_exp e', \{}, 0)]
                                               [t:=(state_running, te_exp (K t'), \{}, c')])).
                      rewrite dom_update. rewrite dom_update. rewrite dom_update.
                      rew_set. intros x. rew_set. splits*. }
      replace (dom (T[t:=(state_running, te_exp (K t'), d, c)]
                      [t':=(state_new, te_exp e', \{}, 0)]
                      [t:=(state_running, te_exp (K t'), \{}, c')]
                      [t':=(state_new, te_exp e', \{}, c')])) with
               (union (union (dom T) (single t')) (single t)).
      rew_set.
      splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
           ++ asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t1. }
              autos.
           ++ inverts Heq. autos*.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
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
        - apply H5. apply (Hdspawned t'). right. rewrite Heq2. rew_listx*. }
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
                  destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
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
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t2 = t)) as [->|Hneq3].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
              asserts (Hdisj & Hnmemst):
                (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
                  /\ ~mem (event_start t2) log).
              { apply (Hdnew t2). exists e2 h2 ts2. exact Hbinds4. }
              split.
              ** destruct Hdisj as [(t1 & Hmem) | Hmem].
                 --- left. exists t1. rew_listx*.
                 --- right. rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq].
                 --- apply Hnmemst. exact contra.
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
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
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
        -- exists (te_exp (K t')) (empty : diff) c'.
           apply~ binds_update_neq. apply binds_update_same.
        -- exists e2 d2 h2.
           apply~ binds_update_neq. apply~ binds_update_neq.
           apply~ binds_update_neq. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t')) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
           destruct (classic (t0 = t)) as [->|Hneq2].
           ++ apply binds_update_same_inv in Hbinds1.
              asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
              { apply (Hdrunning t). eauto. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
           ++ forwards~ Hbinds2: binds_update_neq_inv Hbinds1.
              forwards~ Hbinds3: binds_update_neq_inv Hbinds2.
              forwards~ Hbinds4: binds_update_neq_inv Hbinds3.
              asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
              { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds4. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty][t' := empty]) (TC[t := c'][t' := c']) LC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlaySpawn _ _ _ _ _ _ c c' d); auto.
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
              exists state_running (te_exp (K t')).
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r)] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
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
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq2: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq2: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        apply binds_update_inv in Hbinds.
        cases_if.
        rew_listx. left. apply (Hdend t0). exists* e2 h2.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq'].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq'].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      asserts Htin': (t' \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards (ts_old' & e_old' & Hbinds_delta'): Hdelta t' Htin'.
      forwards* Heq: binds_inj H3 Hbinds_delta.
      forwards* Heq': binds_inj H5 Hbinds_delta'.
      exists D (TC[t := c'']) LC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayJoin _ _ _ _ _ _ c c' c''); auto.
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
           exists state_running (te_exp (K r)). apply binds_update_same.
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
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...], L' = L[l := held t] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    unfolds pull_lock, do_merge.
    asserts Hl: (L[l] = (ls_free, c')).
    { apply* read_of_binds. }
    replace (L[l]) with (ls_free, c') in H8.
    asserts Ht: (T[t] = (state_running, te_exp e, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, c) in H8.
    inverts H8.
    apply binds_update_same_inv in H9. inverts H9.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           auto.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. repeat apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists* e2 h2 ts2. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. repeat apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        rewrite~ update_update in Hbinds.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. repeat apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        rewrite~ update_update in Hbinds.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
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
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj Hbinds_delta H3.
      asserts Hlin: (l \indom L). { apply* indom_of_binds. }
      forwards (ls & Hbinds_l): Hlocks Hlin.
      forwards~ Heq': binds_inj Hbinds_l H5.
      rewrite~ update_update.
      exists D (TC[t := c'']) LC. eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayLock _ _ _ _ _ _ c c' c''); auto.
        -- inverts Heq.
           apply* binds_of_indom_read.
        -- inverts Heq'.
           apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- asserts~ Hd_t: (D[t] = d).
           rewrite read_update_same.
           rewrite Hd_t.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           asserts Htc0: ((TC[t := c''])[t0] = TC[t0]). { rewrite~ read_update_neq. }
           rewrite Htc0.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- forwards* HleqL: binds_inj Hbinds_l.
           asserts~ HLC_l: (LC[l] = c').
           rewrite HLC_l. exists (ls_held t). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin1.
           exists ls0'. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. branches; auto_star.
      * introv Hmem. rew_dom.
        rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem. rew_dom.
        rew_set in Hmem. branches; auto_star.
      * (* dom LC ⊆ dom L: LC unchanged, dom L grows by l *)
        introv Hmem. rew_dom. rew_set. left. applys~ HdomLC2 Hmem.
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepLockFresh: log' = log & event_lock t l, T' = T[t := K void, d, c], G unchanged *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    splits.
    + (* 1. Spawned dom *)
      intros t2. rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           auto.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           auto.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists* e2 h2 ts2. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Henmem contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
    + (* 5. Locked locks *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           exists c. apply binds_update_same.
        -- intros (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. inverts Hbinds.
           exists~ (LibList.filter (fun e => touches_lock l e) log).
      * unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           forwards ((h2 & Hbinds) & Hbinds'): (Hdlock t0 l0). { exists log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdlock t0 l0). exists h2. exact Hbinds'.
    + (* 6. Unlocked locks: l now held *)
      intros l0. rew_listx. cases_if as Hcase.
      * unfold touches_lock in Hcase. subst. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- introv (h2 & Hbinds).
           apply binds_update_same_inv in Hbinds. congruence.
      * unfold touches_lock in Hcase. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           forwards (h2 & Hbinds): (proj1 (Hdunlock l0)). { exists t0 log'. exact Hfilt. }
           exists h2. apply~ binds_update_neq.
        -- intros (h2 & Hbinds).
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           forwards (t0 & log' & Hfilt): (proj2 (Hdunlock l0)). { exists h2. exact Hbinds'. }
           exists t0 log'. exact Hfilt.
    + (* 7. Replay: PlayLockFresh records LC[l := TC[t]] *)
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      match goal with Hbt : binds T t (state_running, te_exp e, d, c) |- _ =>
        forwards~ Heq: binds_inj Hbinds_delta Hbt end.
      asserts Hlnc: (l \notindom LC).
      { match goal with Hnl : l \notindom L |- _ => intros Hin; apply Hnl; applys HdomLC2 Hin end. }
      asserts~ Hd_t: (D[t] = d).
      asserts~ Htc_t: (TC[t] = c).
      exists D TC (LC[l := TC[t]]). eexists. splits*.
      * applys PlaySnoc Hplay. apply PlayLockFresh; [ applys HdomTC Htin | exact Hlnc ].
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- rewrite Hd_t. rewrite Htc_t.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- rewrite read_update_same. rewrite Htc_t. exists (ls_held t). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           rewrite~ read_update_neq.
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin1.
           exists ls0'. apply~ binds_update_neq.
      * introv Hmem. rew_dom. rew_set in Hmem. branches; auto_star.
      * introv Hmem. rew_dom. rew_set in Hmem. branches; auto_star.
      * introv Hmem. rew_dom. rew_set in Hmem. rew_set. branches; auto_star.
      * introv Hmem. rew_dom. rew_set in Hmem. rew_set. branches; auto_star.
    + (* 8. Init event present *)
      exists t''. rew_listx*.
  - (* StepRelease: log' = log & event_unlock t l, T' = T[t := ...], L' = L'[l := free] *)
    destruct Hdesc as (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & (t'' & Hdinit)).
    unfolds push_lock, do_commit.
    asserts Ht: (T[t] = (state_running, te_exp e, d, c)).
    { apply* read_of_binds. }
    replace (T[t]) with (state_running, te_exp e, d, c) in H7.
    asserts Hl: (L[l] = (ls_held t, c')).
    { apply* read_of_binds. }
    replace (L[l]) with (ls_held t, c') in H7.
    inverts H7.
    rewrite~ update_update.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)|[Hmem | Heq]]; [| | congruence].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts ->: (t2 = t_root).
           { apply mem_inv_middle in Hmem as (l1 & l2 & Heq). applys* Hinit. }
           asserts Hrmem: (t_root \indom T). { apply (Hdspawned t_root). right. exact Hmem. }
           autos.
      * intros Hin.
        asserts Hin': (t2 \indom T \/ t2 = t). { rew_set in Hin. autos*. }
        clear Hin. destruct Hin' as [Hin | ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
    + (* 2. New threads *)
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | [Hmem | Heq]]; [| | congruence].
            + rew_listx in Hmem. branches; [|congruence].
              left. exists* t1.
            + right*.
          - intros Hc. false Hnmem. rew_listx*. }
        exists e2 h2 ts2. apply~ binds_update_neq.
      * introv (e2 & h2 & ts2 & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ Hbinds': binds_update_neq_inv Hbinds.
        asserts (Hdisj & Hnmemst):
          (((exists t1, mem (event_spawn t1 t2) log) \/ mem (event_init t2) log)
            /\ ~ mem (event_start t2) log).
        { apply (Hdnew t2). exists e2 h2 ts2. assumption. }
        split.
        -- destruct Hdisj as [(t1 & Hmem) | Hmem].
           ++ left. exists t1. rew_listx*.
           ++ right. rew_listx*.
        -- intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [apply Hnmemst; assumption|congruence].
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        exists e2 h2. apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds'.
    + (* 4. Running threads *)
      intros t0. split.
      * introv (Hmem & Hnmem).
        asserts Hmem': (mem (event_start t0) log).
        { rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [assumption|congruence]. }
        asserts Hnend: (~mem (event_end t0) log).
        { intros contra. apply Hnmem. rew_listx*. }
        asserts (e2 & d2 & h2 & Hbinds): (exists e2 d2 h2, binds T t0 (state_running, e2, d2, h2)).
        { apply (Hdrunning t0). split; assumption. }
        destruct (classic (t0 = t)) as [->|Hneq].
        -- do 3 eexists. apply binds_update_same.
        -- exists e2 d2 h2. apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
           { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds'. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
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
      destruct Hdplay as (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2).
      apply binds_update_same_inv in H8. inverts H8.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (ts_old & e_old & Hbinds_delta): Hdelta Htin.
      forwards~ Heq: binds_inj  H3 Hbinds_delta.
      asserts Hlin: (l \indom L). { apply* indom_of_binds. }
      forwards (ls & Hbinds_l): Hlocks Hlin.
      forwards~ Heq': binds_inj H5 Hbinds_l.
      exists (D[t := empty]) (TC[t := c'']) (LC[l := c'']). eexists. splits*.
      * applys PlaySnoc Hplay.
        apply (PlayUnlock _ _ _ _ _ _ c c'' d); auto.
        -- inverts Heq.
           apply* binds_of_indom_read.
        -- inverts Heq.
           apply* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq_t0].
        -- repeat rewrite read_update_same.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           repeat rewrite~ read_update_neq.
           forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin1.
           exists ts' e''. apply~ binds_update_neq.
      * intros l0 Hin.
        destruct (classic (l0 = l)) as [->|Hneq_l].
        -- rewrite read_update_same.
           exists (ls_free). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct~ Hin1 as [->|Hin1].
           forwards~ Hin2: indom_update_inv Hin1.
           destruct~ Hin2 as [->|Hin2].
           forwards (ls0' & Hbinds_l'): Hlocks l0 Hin2.
           rewrite~ read_update_neq.
           exists ls0'. apply~ binds_update_neq. apply~ binds_update_neq.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto.
      * introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto_star.
      * (* dom LC ⊆ dom L *)
        introv Hmem.
        rew_dom. rew_set in Hmem. rew_set.
        branches; auto_star.
    + (* 8. Init event present *)
      exists t''. rew_listx*.
Qed.
