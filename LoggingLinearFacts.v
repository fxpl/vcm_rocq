From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Linear.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingLinear.

Import Graph.
Import GraphFacts.
Import Linear.
Import Log.
Import LogFacts.
Import LoggingLinear.

Existing Instance inhab_val.
Existing Instance inhab_exp.

(* ===================== *)
(* Initial configuration *)
(* ===================== *)

Theorem init_cfg_wf :
  forall e,
    wf_cfg (init_cfg e).
Proof.
  introv. unfolds init_cfg, wf_cfg, total_order, graph_root, empty_graph, graph_indom.
  splits.
  - apply init_graph_wf.
  - (* total order: the only commit is [root_commit] *)
    introv Ha Hb.
    asserts ->: (a = root_commit).
    { rew_dom. rew_set in Ha. branches; [forwards*: indom_empty_inv | auto]. }
    asserts ->: (b = root_commit).
    { rew_dom. rew_set in Hb. branches; [forwards*: indom_empty_inv | auto]. }
    left. apply ancestor_refl.
  - (* the global head [root_commit] is in the graph *)
    rew_dom. rew_set. auto.
  - (* every commit is an ancestor of the global head *)
    introv Hc.
    asserts ->: (c = root_commit).
    { rew_dom. rew_set in Hc. branches; [forwards*: indom_empty_inv | auto]. }
    apply ancestor_refl.
  - (* every thread's commit is in the graph *)
    introv Hbinds.
    asserts ->: (t = t_root).
    { destruct* (classic (t = t_root)).
      forwards~ Hbinds': binds_update_neq_inv Hbinds.
      forwards*: binds_empty_false. typeclass. }
    forwards~ Heq: binds_update_same_inv Hbinds.
    inverts Heq.
    rew_dom. rew_set. auto.
Qed.

Theorem init_log_describes_init_cfg :
  forall e,
    describes nil (init_cfg e).
Proof.
  intros.
  unfolds init_cfg.
  splits; rew_list.
  - (* spawned/inited threads exist *)
    introv. splits.
    + introv Hsrc.
      destruct Hsrc as [(t1 & contra)| ->].
      * inverts contra.
      * rew_dom. rew_set. autos.
    + introv Hdom.
      rew_dom. rew_set in Hdom.
      branches.
      * forwards*: indom_empty_inv.
      * subst. right. rew_listx*.
  - (* new threads *)
    introv. splits.
    + introv (Hsrc & Hnmem).
      destruct Hsrc as [(t1 & contra)| ->].
      * inverts contra.
      * exists. apply binds_update_same.
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
  - (* ended threads *)
    introv. splits.
    + introv Hmem.
      inverts Hmem.
    + introv (e' & c & Hbinds).
      destruct (classic (t = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - (* running threads *)
    introv. splits.
    + introv (Hmem & Hnmem).
      inverts Hmem.
    + introv (e' & d & c & Hbinds).
      destruct (classic (t = t_root)).
      * subst.
        forwards* Heq: binds_update_same_inv Hbinds.
      * forwards* contra: binds_update_neq_inv Hbinds.
        forwards*: indom_of_binds; [typeclass|].
        forwards*: indom_empty_inv.
  - (* locked locks *)
    introv. splits.
    + introv (log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv contra.
      forwards*: indom_of_binds; [typeclass|].
      forwards*: indom_empty_inv.
  - (* free locks *)
    introv. splits.
    + introv (t & log' & Heq).
      rew_listx in Heq.
      forwards*: nil_eq_last_inv.
    + introv contra.
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
    + introv Hdom.
      rew_dom. rew_set in *. branches;
        [forwards*: indom_empty_inv| subst*].
    + rew_dom. introv Hdom. rew_set in *.
      branches; auto_star.
      forwards*: indom_empty_inv.
  - congruence.
Qed.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Linear.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + eexists. applys* StepReadLocal.
    + eexists. applys* StepReadGlobal.
    + eexists. applys* StepSpawn.
    + eexists. applys* StepJoin.
Qed.

Lemma graph_commit_indom_inv :
  forall G c c' c'' d,
    graph_indom (graph_commit G c' c'' d) c ->
    graph_indom G c \/ c = c''.
Proof.
  introv Hdom. unfolds graph_indom, graph_commit.
  destruct G as (C & P).
  rew_dom. rew_set in Hdom. auto.
Qed.

Lemma total_order_commit :
  forall G g g' d,
    total_order G ->
    (forall c, graph_indom G c -> ancestor G c g) ->
    commit_fresh G g' ->
    total_order (graph_commit G g g' d).
Proof.
  introv Htot Hmax Hfresh.
  destruct G as (C & P).
  introv Hdoma Hdomb.
  forwards Hdisja: graph_commit_indom_inv Hdoma.
  forwards Hdisjb: graph_commit_indom_inv Hdomb.
  destruct Hdisja as [Hdoma' | ->];
  destruct Hdisjb as [Hdomb' | ->].
  - forwards Hanc: Htot Hdoma' Hdomb'.
    branches; auto using ancestor_graph_commit.
  - forwards Hanc: Hmax Hdoma'.
    left. apply ancestor_trans with (c' := g);
      auto using ancestor_graph_commit, ancestor_graph_commit_edge.
  - forwards Hanc: Hmax Hdomb'.
    right. apply ancestor_trans with (c' := g);
      auto using ancestor_graph_commit, ancestor_graph_commit_edge.
  - right. apply ancestor_refl.
Qed.

Hint Resolve total_order_commit : vcm.

Lemma max_ancestor_commit :
  forall G g g' c d,
    (forall c, graph_indom G c -> ancestor G c g) ->
    commit_fresh G g' ->
    graph_indom (graph_commit G g g' d) c ->
    ancestor (graph_commit G g g' d) c g'.
Proof.
  introv Hmax Hfresh Hdom.
  forwards Hdomc: graph_commit_indom_inv Hdom.
  branches.
  - forwards~ Hanc: Hmax c.
    apply ancestor_trans with (c' := g);
      auto using ancestor_graph_commit, ancestor_graph_commit_edge.
  - subst. apply ancestor_refl.
Qed.

Hint Resolve max_ancestor_commit : vcm.

Theorem step_preserves_wf_cfg :
  forall cfg cfg' log log',
    wf_cfg cfg ->
    step (cfg, log) (cfg', log') ->
    wf_cfg cfg'.
Proof.
  destruct cfg as (((T & G) & g) & L).
  introv (Hwf & Htot & Hg & Hmax & HdomT) Hstep.
  inverts Hstep.
  - (* StepStart *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepEnd *)
    unfolds global_commit.
    replace (T[t]) with (state_running, te_ret r, d, c) in H9 by forwards*: read_of_binds.
    inverts H9.
    splits~.
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
  - (* StepLocalRead *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepGlobalRead *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepWrite *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepSpawn *)
    unfolds push_thread, global_commit.
    asserts* Hneq: (t <> t').
    rewrite~ read_update_neq in H11.
    rewrite~ read_update_same in H11.
    rewrite~ read_update_neq in H11.
    rewrite~ read_update_same in H11.
    inverts H11. splits~.
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
  - (* StepJoin *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    * subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
    * forwards* Hbinds': binds_update_neq_inv Hbinds.
  - (* StepLock *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
    + forwards* Hbinds': binds_update_neq_inv Hbinds.
  - (* StepUnlock *)
    unfolds global_commit.
    replace (T[t]) with (state_running, te_exp e, d, c) in H11 by forwards*: read_of_binds T.
    inverts H11.
    splits~.
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
    lets (_ & Hdstart & _): Hdesc.
    asserts (Hsrc & Hnmem): (((exists t1, mem (event_spawn t1 t) log) \/ t = t_root) /\ ~mem (event_start t) log).
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
        branches; autos.
        match goal with H : event_start _ = event_start _ |- _ => inverts H end.
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
    + introv Heq.
      forwards* [(Heq' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      inverts Heq'.
      destruct~ (classic (l1 = nil)).
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      forwards*: Hdroot.
    + introv Hmem'.
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
    + introv Heq <- Hneq.
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
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
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
    + introv. rew_listx.
      cases_if~. rew_list~.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
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
    + introv. rew_listx.
      cases_if~. rew_list~.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
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
      * simpl. intros ->. apply Hwnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepSpawn: log' = log & event_spawn t t' *)
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _ & _ & _ & _).
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
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
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
      * simpl. intros ->. apply Hsnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
      rew_listx in Hmem'. destruct Hmem' as [Hmem' | Heq]; [auto_star|inverts Heq].
      apply H5. apply* Hdspawned.
  - (* StepJoin: log' = log & event_join t t' *)
    destruct Hdesc as (_ & _ & Hdend & Hdrunning & _).
    asserts (Hsmem & Hjnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Htended: (mem (event_end t') log).
    { apply (Hdend t'). eauto. }
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
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_listx~.
      * apply* Hjoin.
    + introv Heq <- Hneq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. simpl. exact Hsmem.
      * apply~ Hstart.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      rew_listx. splits.
      * apply~ Hend.
      * simpl. intros ->. apply Hjnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
  - (* StepLock: log' = log & event_lock t l (free lock) *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & Hdunlock & _).
    asserts (Hsmem & Hlnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). eauto. }
    asserts Hwflog: (wf_log log). { splits 9; assumption. }
    applys wf_log_snoc_lock Hwflog Hsmem Hlnmem.
    branches.
    + right. apply* (proj2 (Hdunlock l)).
    + left.
      destruct~ (last_case (LibList.filter (fun e => touches_lock l e) log)) as [? | Hex].
      false. destruct Hex as (e' & Hex).
      asserts Htouch: (touches_lock l e').
      {
        unpack. forwards* [Htouches | Htouches]: filter_touches_lock_last_inv;
          unpack; subst; simpls*.
      }
      destruct e'; try (simpls; congruence).
      * simpls. subst. apply Hdlock in Hex.
        asserts* contra: (l0 \indom L).
        autos.
      * simpls. subst.
        asserts* Hex': (exists t l',
                           LibList.filter (fun e : event => touches_lock l0 e) log =
                             l' & event_unlock t l0).
        apply Hdunlock in Hex'.
        asserts* contra: (l0 \indom L).
        autos.
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
    + introv. rew_listx.
      cases_if as Heql.
      * unfold touches_lock in Heql. subst. rew_list.
        apply* wf_lock_log_snoc_unlock.
      * rew_list. apply~ Hlock.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Hmem'.
      rew_listx in Hmem'. branches; auto_star.
Qed.

(* Discharge the [Inhab] side-conditions of [indom_of_binds] / [binds_inj] etc.
   that the auto-find ([apply* ...]) idiom below leaves open.  Scoped after the
   init lemmas so it does not perturb their explicit [typeclass] handling. *)
Hint Extern 1 (Inhab _) => typeclass : vcm.

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
  - (* StepStart: log' = log & event_start t, T' = T[t := running c:=g] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
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
    + (* 7. Replay: PlayStart fast-forwards [t] to the global head [g] *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D (TC[t := g]). eexists. splits.
      * applys PlaySnoc Hplay. apply PlayStart.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running e. apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists st' e''.
           rewrite read_update_neq; [| auto].
           apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomD. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomD.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
           applys* indom_update_of_indom.
    + (* 8. Init event present *)
      introv _.
      lets (_ & _ & _ & _ & _ & _ & _ & Hdroot): Hdesc.
      rew_listx. destruct log; [|auto_star].
      right.
      asserts~ Hdom: (t \indom T).
      apply Hdspawned in Hdom.
      destruct Hdom as [(t1 & contra)| ->]; auto.
      forwards*: mem_nil_inv contra.
  - (* StepEnd: log' = log & event_end t, commit delta then terminate t *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    match goal with H : global_commit _ _ _ _ _ = _ |- _ =>
      unfold global_commit in H;
      replace (T[t]) with (state_running, te_ret r, d, c) in H by (forwards*: read_of_binds);
      inverts H
    end.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [| congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t1. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
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
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
        -- inverts Heq. exists (te_ret r) g'. apply binds_update_same.
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
    + (* 7. Replay: PlayEnd commits [t]'s delta onto the global head *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := g']). eexists. splits.
      * applys PlaySnoc Hplay. applys PlayEnd.
        -- lets HtinD: HdomD Htin. applys* binds_of_indom_read.
        -- assumption.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := g'][t] = g'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_terminated (te_ret r). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards~ Hin2: indom_update_inv Hin1.
           destruct Hin2 as [->|Hin2]. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin2.
           asserts Hd0: (D[t := empty][t0] = D[t0]). { rew_map*. }
           asserts Htc0: (TC[t := g'][t0] = TC[t0]). { rew_map*. }
           rewrite Hd0, Htc0.
           exists st' e''. apply~ binds_update_neq. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 \indom T).
           {
             forwards~ Ha: indom_update_inv Hin.
             destruct Ha as [->|Ha]. { congruence. }
             forwards~ Hb: indom_update_inv Ha.
           }
           asserts HinD: (t0 \indom D). { applys~ HdomD. }
           applys* indom_update_of_indom.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 \indom T).
           {
             forwards~ Ha: indom_update_inv Hin.
             destruct Ha as [->|Ha]. { congruence. }
             forwards~ Hb: indom_update_inv Ha.
           }
           asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
           applys* indom_update_of_indom.
    + (* 8. Init event present *)
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
  - (* StepReadLocal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
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
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 7. Replay: PlayRead is a no-op on the play state *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D TC. eexists. splits.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists st' e''. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomD. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomD.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomTC. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomTC.
    + (* 8. Init event present *)
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
  - (* StepReadGlobal: same resulting config/log as StepReadLocal *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
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
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 7. Replay: PlayRead is a no-op on the play state *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D TC. eexists. splits.
      * applys PlaySnoc Hplay. apply PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (te_exp (K (ret_val v))). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists st' e''. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomD. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomD.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomTC. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomTC.
    + (* 8. Init event present *)
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
  - (* StepWrite: log' = log & event_write t x v, T' = T[t := running K(void), d[x:=v]] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* (Hdspawned t_root). }
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
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 7. Replay: PlayWrite updates [t]'s delta at [x] *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := d[x := v]]) TC. eexists. splits.
      * applys PlaySnoc Hplay.
        apply (PlayWrite _ _ _ _ _ _ _ d).
        lets HtinD: HdomD Htin. applys* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := d[x:=v]])[t] = d[x:=v]). { rew_map*. }
           rewrite Hd_new, Htc.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           asserts Hd0: ((D[t := d[x:=v]])[t0] = D[t0]). { rew_map*. }
           rewrite Hd0.
           exists st' e''. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinD: (t0 \indom D). { applys~ HdomD. }
           applys* indom_update_of_indom.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomTC. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomTC.
    + (* 8. Init event present *)
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
  - (* StepSpawn *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    asserts* Hneq: (t <> t').
    match goal with Hpt : _ = (_, _) |- _ =>
      unfold push_thread, global_commit in Hpt;
      rewrite~ read_update_neq in Hpt;
      rewrite~ read_update_same in Hpt;
      rewrite~ read_update_neq in Hpt;
      rewrite~ read_update_same in Hpt;
      inverts Hpt
    end.
    asserts Hnotin: (t' \notindom T). { assumption. }
    splits.
    + (* 1. Spawned dom *)
      intros t2. rew_dom. rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t1 & Hmem)| ->].
        -- rew_listx in Hmem. destruct Hmem as [Hmem|Heq].
           ++ asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t1. }
              autos*.
           ++ inverts Heq. autos*.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
           autos*.
      * intros Hin.
        rew_set in Hin.
        destruct Hin as [[[[Hin| ->]| ->]| ->]| ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
        -- left. exists t. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
        -- left. exists t. rew_listx*.
    + (* 2. New threads *)
      asserts Hnospawn: (~exists t1, mem (event_spawn t1 t') log).
      { intros (t1 & Hmem). apply Hnotin. apply (Hdspawned t'). left. exists* t1. }
      asserts Hnostart: (~mem (event_start t') log).
      { intros Hmemst.
        asserts (l1 & l2 & Heq2): (exists l1 l2, log = l1 ++ event_start t' :: l2).
        { apply~ mem_inv_middle. }
        forwards [(t1 & Hmem) | Hmem]: Hspawn Heq2.
        - false Hnospawn. exists t1. rewrite Heq2. rew_listx*.
        - apply Hnotin. apply* (Hdspawned t'). }
      asserts (Hsmem & Henmem): (mem (event_start t) log /\ ~mem (event_end t) log).
      { apply (Hdrunning t). eauto. }
      intros t2. split.
      * introv (Hdisj & Hnmem).
        destruct (classic (t2 = t')) as [->|Hneq2].
        -- exists (te_exp e') (empty : diff) g'. apply binds_update_same.
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
        -- forwards~ Hbinds1: binds_update_neq_inv Hbinds.
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
                 --- apply Hnmemst. exact contra.
                 --- congruence.
    + (* 3. Ended threads *)
      intros t0. split.
      * introv Hmem.
        rew_listx in Hmem. destruct Hmem as [Hmem|Hmem]; [|congruence].
        asserts (e2 & h2 & Hbinds): (exists e2 h2, binds T t0 (state_terminated, e2, empty_diff, h2)).
        { apply (Hdend t0). exact Hmem. }
        asserts Hneq': (t0 <> t').
        { intros ->. false* Hnotin. }
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
        { intros ->. false* Hnotin. }
        destruct (classic (t0 = t)) as [->|Hneq2].
        -- exists (te_exp (K t')) (empty : diff) g'.
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
    + (* 5. Locked locks *)
      intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + (* 6. Unlocked locks *)
      intros l. rew_listx. cases_if~. rew_list. apply Hdunlock.
    + (* 7. Replay: PlaySpawn commits parent's delta; child starts at the new head *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty][t' := empty]) (TC[t := g'][t' := g']). eexists. splits.
      * applys PlaySnoc Hplay. applys PlaySpawn.
        -- lets HtinD: HdomD Htin. applys* binds_of_indom_read.
        -- assumption.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hq'].
        -- asserts Hd_t': ((D[t := empty][t' := empty])[t'] = empty).
           { rewrite read_update_same. auto. }
           asserts Htc_t': ((TC[t := g'][t' := g'])[t'] = g').
           { rewrite read_update_same. auto. }
           rewrite Hd_t', Htc_t'.
           exists state_new (te_exp e'). apply binds_update_same.
        -- destruct (classic (t0 = t)) as [->|Hq2].
           ++ asserts Hd_t: ((D[t := empty][t' := empty])[t] = empty).
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              asserts Htc_t: ((TC[t := g'][t' := g'])[t] = g').
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
              asserts Htc0: ((TC[t := g'][t' := g'])[t0] = TC[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              rewrite Hd0, Htc0.
              forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin4.
              exists ts' e''.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hq'].
        -- rew_dom. rew_set. right*.
        -- destruct (classic (t0 = t)) as [->|Hq2].
           ++ rew_dom. rew_set. left. right*.
           ++ forwards~ Hin1: indom_update_inv Hin. destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1. destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2. destruct Hin3 as [->|Hin3]. { congruence. }
              forwards~ Hin4: indom_update_inv Hin3. destruct Hin4 as [->|Hin4]. { congruence. }
              asserts HinD: (t0 \indom D). { applys~ HdomD. }
              rew_dom. rew_set. left. left. exact HinD.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hq'].
        -- rew_dom. rew_set. right*.
        -- destruct (classic (t0 = t)) as [->|Hq2].
           ++ rew_dom. rew_set. left. right*.
           ++ forwards~ Hin1: indom_update_inv Hin. destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1. destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2. destruct Hin3 as [->|Hin3]. { congruence. }
              forwards~ Hin4: indom_update_inv Hin3. destruct Hin4 as [->|Hin4]. { congruence. }
              asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
              rew_dom. rew_set. left. left. exact HinTC.
    + (* 8. Init event present *)
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
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r), c:=g] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
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
        asserts Hneq2: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 7. Replay: PlayJoin fast-forwards [t] to the global head [g] *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D (TC[t := g]). eexists. splits.
      * applys PlaySnoc Hplay. apply PlayJoin.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running (te_exp (K r)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists st' e''.
           rewrite read_update_neq; [| auto].
           apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomD. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomD.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
           applys* indom_update_of_indom.
    + (* 8. Init event present *)
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
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...,c:=g], L' = L[l := held t] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
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
        asserts Hneq2: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 5. Locked locks: the new lock event locks [l] held by [t] *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l *)
        unfold touches_lock in Hcase. subst l0. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. inverts Heq.
           apply binds_update_same.
        -- intros Hbinds.
           apply binds_update_same_inv in Hbinds. inverts Hbinds.
           exists~ (LibList.filter (fun e => touches_lock l e) log).
      * (* l0 <> l *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply (Hdlock t0 l0). exists log'. exact Hfilt.
        -- intros Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdlock t0 l0). exact Hbinds'.
    + (* 6. Unlocked locks *)
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: now held, both sides false *)
        unfold touches_lock in Hcase. subst l0. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- intros Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 <> l *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply (Hdunlock l0). exists t0 log'. exact Hfilt.
        -- intros Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdunlock l0). exact Hbinds'.
    + (* 7. Replay: PlayLock fast-forwards [t] to the global head [g] *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D (TC[t := g]). eexists. splits.
      * applys PlaySnoc Hplay. apply PlayLock.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin': indom_update_inv Hin.
           destruct Hin' as [->|Hin']. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin'.
           exists st' e''.
           rewrite read_update_neq; [| auto].
           apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- applys HdomD. apply* indom_of_binds.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           applys~ HdomD.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
           applys* indom_update_of_indom.
    + (* 8. Init event present *)
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
  - (* StepRelease: log' = log & event_unlock t l, commit delta, L' = L[l := free] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay & _): Hdesc.
    match goal with H : global_commit t g g' T G = _ |- _ =>
      unfold global_commit in H;
      replace (T[t]) with (state_running, te_exp e, d, c) in H by (forwards*: read_of_binds T);
      inverts H
    end.
    rewrite~ update_update.
    splits.
    + (* 1. Spawned dom *)
      intros t2.
      rew_dom.
      rew_set. splits.
      * introv Hsrc.
        rew_listx in Hsrc.
        destruct Hsrc as [(t3 & Hmem)| ->].
        -- rew_listx in Hmem. branches; [|congruence].
           asserts Hin: (t2 \indom T). { apply (Hdspawned t2). left. exists* t3. }
           autos.
        -- asserts Hrmem: (t_root \indom T). { apply* Hdspawned. }
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
        asserts Hneq2: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e2 & h2 & ts2 & Hbinds): (exists e2 h2 ts2, binds T t2 (state_new, e2, h2, ts2)).
        { apply (Hdnew t2). split.
          - rew_listx in Hdisj.
            destruct Hdisj as [(t1 & Hmem) | ->].
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
          (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
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
    + (* 5. Locked locks: [l] is released, so its last touch is an unlock *)
      intros t0 l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: last touch is event_unlock → not locked *)
        unfold touches_lock in Hcase. subst l0. rew_list. split.
        -- introv (log' & Hfilt).
           apply last_eq_last_inv in Hfilt. destruct Hfilt as [_ Heq]. congruence.
        -- intros Hbinds.
           apply binds_update_same_inv in Hbinds. congruence.
      * (* l0 <> l *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (log' & Hfilt).
           apply~ binds_update_neq.
           apply (Hdlock t0 l0). exists log'. exact Hfilt.
        -- intros Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdlock t0 l0). exact Hbinds'.
    + (* 6. Unlocked locks: [l] is now free *)
      intros l0. rew_listx. cases_if as Hcase.
      * (* l0 = l: last touch is event_unlock t l → free *)
        unfold touches_lock in Hcase. subst l0. rew_list. split.
        -- introv (t0 & log' & Hfilt). apply binds_update_same.
        -- intros Hbinds.
           exists t (LibList.filter (fun e => touches_lock l e) log). reflexivity.
      * (* l0 <> l *)
        unfold touches_lock in Hcase. rew_list. split.
        -- introv (t0 & log' & Hfilt).
           apply~ binds_update_neq.
           apply (Hdunlock l0). exists t0 log'. exact Hfilt.
        -- intros Hbinds.
           forwards~ Hbinds': binds_update_neq_inv Hbinds.
           apply (Hdunlock l0). exact Hbinds'.
    + (* 7. Replay: PlayUnlock commits [t]'s delta onto the global head *)
      destruct Hdplay as (D & TC & CH & Hplay & Hdelta & HdomD & HdomTC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := g']). eexists. splits.
      * applys PlaySnoc Hplay. applys PlayUnlock.
        -- lets HtinD: HdomD Htin. applys* binds_of_indom_read.
        -- assumption.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := g'][t] = g'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_running (te_exp (K void)). apply binds_update_same.
        -- forwards~ Hin1: indom_update_inv Hin.
           destruct Hin1 as [->|Hin1]. { congruence. }
           forwards (st' & e'' & Hbinds'): Hdelta t0 Hin1.
           asserts Hd0: (D[t := empty][t0] = D[t0]). { rew_map*. }
           asserts Htc0: (TC[t := g'][t0] = TC[t0]). { rew_map*. }
           rewrite Hd0, Htc0.
           exists st' e''. apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinD: (t0 \indom D). { applys~ HdomD. }
           applys* indom_update_of_indom.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply* indom_update_same.
        -- asserts Hor: (t0 = t \/ t0 \indom T). { applys* indom_update_inv. }
           destruct Hor as [->|Hor]. { congruence. }
           asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
           applys* indom_update_of_indom.
    + (* 8. Init event present *)
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
