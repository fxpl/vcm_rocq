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

(* Disjunctive inversion of a map update lookup, with no side conditions to
   discharge -- convenient for unwinding the nested updates [StepSpawn] builds. *)
Lemma binds_update_inv' :
  forall A B (M : map A B) i j v w,
    binds (M[i := v]) j w ->
    (j = i /\ w = v) \/ (j <> i /\ binds M j w).
Proof.
  introv Hb. destruct (classic (j = i)) as [-> | Hne].
  - left. split; [ reflexivity | applys binds_update_same_inv Hb ].
  - right. split; [ exact Hne | applys binds_update_neq_inv Hb Hne ].
Qed.

(* ===================== *)
(* Initial configuration *)
(* ===================== *)

Theorem init_cfg_wf :
  forall e,
    wf_cfg (init_cfg e).
Proof.
  introv. unfolds init_cfg, wf_cfg, total_order, graph_root, empty_graph, graph_indom, is_global_head.
  splits.
  - apply init_graph_wf.
  - (* total order: the only commit is [root_commit] *)
    introv Ha Hb.
    asserts ->: (a = root_commit).
    { rew_dom. rew_set in Ha. branches; [forwards*: indom_empty_inv | auto]. }
    asserts ->: (b = root_commit).
    { rew_dom. rew_set in Hb. branches; [forwards*: indom_empty_inv | auto]. }
    left. apply ancestor_refl.
  - (* the global head is [root_commit]: in the graph, and every commit's ancestor *)
    exists root_commit. unfolds graph_indom. split.
    + rew_dom. rew_set. auto.
    + introv Hc.
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
Qed.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Linear.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts Hstep.
    + eexists. applys* StepStart.
    + eexists. applys* StepEnd.
    + eexists. applys* StepReadLocal.
    + eexists. applys* StepReadGlobal.
    + eexists. applys* StepReadVolatile.
    + eexists. applys* StepWrite.
    + eexists. applys* StepWriteVolatile.
    + eexists. applys* StepSpawn.
    + eexists. applys* StepJoin.
    + eexists. applys* StepLock.
    + eexists. applys* StepRelease.
Qed.

Theorem step_preserves_wf_cfg :
  forall cfg cfg' log log',
    wf_cfg cfg ->
    step (cfg, log) (cfg', log') ->
    wf_cfg cfg'.
Proof.
  destruct cfg as ((T & G) & L).
  introv (Hwf & Htot & Hhex & HdomT) Hstep.
  inverts Hstep.
  - (* StepStart: graph unchanged -- [Hhex] carries over as-is; the started
       thread's new commit [g] is graph-indom via the step's own witness *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts Heq. applys (proj1 Hheadr).
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepEnd *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    unfolds global_commit.
    replace (T[t]) with (state_running, te_ret r, d, c) in Hgc by forwards*: read_of_binds.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hheadr Hfresh.
    splits.
    + applys graph_commit_wf Hwf Hfresh (proj1 Hheadr).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds.
        inverts~ Heq.
      * forwards~ Hbinds': binds_update_neq_inv Hbinds.
        forwards~ Hbinds'': binds_update_neq_inv Hbinds'.
        asserts* Hdom': (graph_indom G c).
        auto_star.
  - (* StepLocalRead: graph unchanged *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepGlobalRead: graph unchanged *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepReadVolatile: graph unchanged (the pull is a fast-forward) *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts Heq. applys (proj1 Hheadr).
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepWrite: graph unchanged *)
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts* Heq.
    + forwards*: binds_update_neq_inv Hbinds.
  - (* StepWriteVolatile *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    unfolds global_commit. rewrite~ read_update_same in Hgc. inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hheadr Hfresh.
    splits.
    + applys graph_commit_wf Hwf Hfresh (proj1 Hheadr).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds.
      destruct (classic (t = t0)).
      * subst.
        forwards~ Heq: binds_update_same_inv Hbinds;
        inverts Heq; applys graph_commit_indom_same.
      * forwards~ Hbinds1: binds_update_neq_inv Hbinds;
        forwards~ Hbinds2: binds_update_neq_inv Hbinds1;
        forwards~ Hbinds3: binds_update_neq_inv Hbinds2;
        applys graph_commit_indom; applys HdomT Hbinds3.
  - (* StepSpawn *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    unfolds global_commit.
    asserts* Hneq: (t <> t').
    rewrite~ read_update_neq in Hgc.
    rewrite~ read_update_same in Hgc.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hheadr Hfresh.
    splits.
    + applys graph_commit_wf Hwf Hfresh (proj1 Hheadr).
    + exact Htot'.
    + eexists. exact Hhead'.
    + introv Hbinds.
      forwards [(-> & Heq) | (Hne1 & Hbinds1)]: binds_update_inv' Hbinds.
      * (* the spawner [t], committed to [g'] *)
        inverts Heq. applys graph_commit_indom_same.
      * forwards [(-> & Heq) | (Hne2 & Hbinds2)]: binds_update_inv' Hbinds1.
        -- (* the spawned thread [t'], placeholder commit [g] *)
           inverts Heq. applys graph_commit_indom_same.
        -- forwards [(Heqtt & _) | (Hne3 & Hbinds3)]: binds_update_inv' Hbinds2.
           ++ congruence.
           ++ applys graph_commit_indom. applys HdomT Hbinds3.
  - (* StepJoin: graph unchanged *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    * subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts Heq. applys (proj1 Hheadr).
    * forwards* Hbinds': binds_update_neq_inv Hbinds.
  - (* StepLock: graph unchanged *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    splits~.
    introv Hbinds.
    destruct (classic (t = t0)).
    + subst.
      forwards~ Heq: binds_update_same_inv Hbinds.
      inverts Heq. applys (proj1 Hheadr).
    + forwards* Hbinds': binds_update_neq_inv Hbinds.
  - (* StepUnlock *)
    match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
    match goal with Hf : commit_fresh G _ |- _ => rename Hf into Hfresh end.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ => rename H into Hgc end.
    unfolds global_commit.
    replace (T[t]) with (state_running, te_exp e, d, c) in Hgc by forwards*: read_of_binds T.
    inverts Hgc.
    forwards (Htot' & Hhead'): is_global_head_commit Htot Hheadr Hfresh.
    splits.
    + applys graph_commit_wf Hwf Hfresh (proj1 Hheadr).
    + exact Htot'.
    + eexists. exact Hhead'.
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
    destruct Hdesc as (Hdspawned & _ & _ & Hdrunning & _ & _ & _).
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
  - (* StepLock: append [event_lock t l] *)
    destruct Hdesc as (_ & _ & _ & Hdrunning & Hdlock & Hdunlock & _).
    asserts (Hsmem & Hnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply* Hdrunning. }
    asserts Hlfree: (LibList.filter (fun e => touches_lock l e) log = nil \/
                     exists t'' log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_unlock t'' l).
    { match goal with Hpre : lock_read L l = ls_free |- _ => rename Hpre into Hread end.
      unfold lock_read, read_default in Hread.
      destruct (classic (l \indom L)) as [Hindom | Hnotin].
      - right. asserts Hfree: (binds L l ls_free).
        { applys binds_of_indom_read Hindom. case_if* in Hread. }
        apply~ Hdunlock.
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
    match goal with Hpre : lock_read L l = ls_held t |- _ => rename Hpre into Hread end.
    unfold lock_read, read_default in Hread.
    asserts Hindom: (l \indom L).
    { destruct (classic (l \indom L)) as [?|Hnotin]; auto.
      false. case_if* in Hread. }
    asserts Hbheld: (binds L l (ls_held t)).
    { applys binds_of_indom_read Hindom. case_if* in Hread. }
    asserts (log'' & Hlheld): (exists log'', LibList.filter (fun e => touches_lock l e) log = log'' & event_lock t l).
    { apply* Hdlock. }
    apply* wf_log_unlock_last.
Qed.

(* Discharge the [Inhab] side-conditions of [indom_of_binds] / [binds_inj] etc.
   that the auto-find ([apply* ...]) idiom below leaves open.  Scoped after the
   init lemmas so it does not perturb their explicit [typeclass] handling. *)
Hint Extern 1 (Inhab _) => typeclass : vcm.

(* The replayed graph is always well-formed and totally ordered, and the
   replayed head is always its maximum -- i.e. [is_global_head]. Proved
   directly off [play_event]/[play_log] (mirrors [play_event_preserves_inv] /
   [play_log_inv] / [play_log_graph_facts], which live in LinearEquivLemmas.v
   and so cannot be imported here, since that file itself imports this one).
   Needed to identify a step's own freshly-introduced [is_global_head]
   witness with the head that replaying the log up to that point produces,
   now that [g] is no longer tracked as data in [cfg]. *)
Lemma play_event_preserves_head_wf :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    wf_graph Gp -> total_order Gp -> is_global_head Gp gp ->
    wf_graph G /\ total_order G /\ is_global_head G g.
Proof.
  introv Hpe Hwf' Htot' Hhead'. inverts Hpe.
  - (* PlayRead *) splits*.
  - (* PlayReadVolatile: TC updated only, graph/head unchanged *) splits*.
  - (* PlayWrite *) splits*.
  - (* PlayWriteVolatile: graph_commit *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    forwards (Htot'' & Hhead''): is_global_head_commit Htot' Hhead' Hfresh.
    splits.
    + destruct Hhead' as (Hgdom' & _). applys graph_commit_wf Hwf' Hfresh Hgdom'.
    + exact Htot''.
    + exact Hhead''.
  - (* PlayStart *) splits*.
  - (* PlayEnd: graph_commit *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    forwards (Htot'' & Hhead''): is_global_head_commit Htot' Hhead' Hfresh.
    splits.
    + destruct Hhead' as (Hgdom' & _). applys graph_commit_wf Hwf' Hfresh Hgdom'.
    + exact Htot''.
    + exact Hhead''.
  - (* PlaySpawn: graph_commit *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    forwards (Htot'' & Hhead''): is_global_head_commit Htot' Hhead' Hfresh.
    splits.
    + destruct Hhead' as (Hgdom' & _). applys graph_commit_wf Hwf' Hfresh Hgdom'.
    + exact Htot''.
    + exact Hhead''.
  - (* PlayJoin *) splits*.
  - (* PlayLock *) splits*.
  - (* PlayUnlock: graph_commit *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    forwards (Htot'' & Hhead''): is_global_head_commit Htot' Hhead' Hfresh.
    splits.
    + destruct Hhead' as (Hgdom' & _). applys graph_commit_wf Hwf' Hfresh Hgdom'.
    + exact Htot''.
    + exact Hhead''.
Qed.

Lemma play_log_head_wf :
  forall log D TC G g CH,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    wf_graph G /\ total_order G /\ is_global_head G g.
Proof.
  introv Hplay. inductions Hplay.
  - (* PlayNil: [init_play_cfg]'s graph is [graph_root root_commit] *)
    unfolds init_play_cfg. splits.
    + apply init_graph_wf.
    + introv Ha Hb.
      unfolds graph_indom, graph_root.
      asserts ->: (a = root_commit).
      { rew_dom. rew_set in Ha. branches; [forwards*: indom_empty_inv | auto]. }
      asserts ->: (b = root_commit).
      { rew_dom. rew_set in Hb. branches; [forwards*: indom_empty_inv | auto]. }
      left. apply ancestor_refl.
    + unfolds is_global_head. split.
      * applys graph_root_indom_same.
      * introv Hc. unfolds graph_indom, graph_root.
        asserts ->: (c = root_commit).
        { rew_dom. rew_set in Hc. branches; [forwards*: indom_empty_inv | auto]. }
        apply ancestor_refl.
  - (* PlaySnoc *)
    forwards~ (Hwf' & Htot' & Hhead'): IHHplay.
    applys* play_event_preserves_head_wf H.
Qed.

(* ============================================================= *)
(* Reusable [describes]-conjunct preservation lemmas             *)
(* ------------------------------------------------------------- *)
(* As in the SharedMemory and Branching developments: most       *)
(* [describes] conjuncts are preserved "for free" by a step --    *)
(* the appended event is not of the kind the conjunct constrains, *)
(* and the thread/lock map is updated only in place. Conjuncts    *)
(* 1-6 and 8 are captured below; the replay conjunct (7) is the   *)
(* interesting one and stays inline. Threads are 4-tuples         *)
(* [(state, expr, diff, commit)]; Linear locks carry no commit.   *)
(* ============================================================= *)

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
  - (* StepStart: log' = log & event_start t, T' = T[t := running c:=g] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    asserts HnewX: (exists e' d' c', binds T t (state_new, e', d', c')). { do 3 eexists; eassumption. }
    asserts Htnend: (~ mem (event_end t) log).
    { intros Hc. apply Hdend in Hc as (e2 & c2 & Hb). destruct HnewX as (e3 & d3 & c3 & Hb3).
      forwards~ Hcontra: binds_inj Hb Hb3. }
    splits.
    + applys* describes_spawned_inplace.
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
    + (* 7. Replay: PlayStart fast-forwards [t] to the global head [g] --
         [g] is the step's own [is_global_head] witness; [is_global_head_unique]
         identifies it with the replayed head [g0] so the rest of the proof can
         refer to a single [g] as before. *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      exists D (TC[t := g]) g. eexists. splits.
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
  - (* StepEnd: log' = log & event_end t, commit delta then terminate t *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    match goal with H : global_commit _ _ _ _ _ = _ |- _ =>
      unfold global_commit in H;
      replace (T[t]) with (state_running, te_ret r, d, c) in H by (forwards*: read_of_binds);
      inverts H
    end.
    asserts (HsmemX & HenmemX): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
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
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayEnd commits [t]'s delta onto the global head *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := g']) g'. eexists. splits.
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
  - (* StepReadLocal: log' = log & event_read t x v, T' = T[t := running K(v)] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayRead is a no-op on the play state *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D TC g0. eexists. splits.
      * applys PlaySnoc Hplay. apply* PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (K (ret_val v)). apply binds_update_same.
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
  - (* StepReadGlobal: same resulting config/log as StepReadLocal *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayRead is a no-op on the play state *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      exists D TC g0. eexists. splits.
      * applys PlaySnoc Hplay. apply* PlayRead.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           asserts Htc: (TC[t] = c). { congruence. }
           rewrite Hd, Htc.
           exists state_running (K (ret_val v)). apply binds_update_same.
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
  - (* StepReadVolatile: log' = log & event_read t x v, T' = T[t := running K(v), c:=g] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayReadVolatile fast-forwards [t]'s commit to [g] *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      exists D (TC[t := g]) g. eexists. splits.
      * applys PlaySnoc Hplay. apply* PlayReadVolatile.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds_delta.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running (K (ret_val v)). apply binds_update_same.
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
  - (* StepWrite: log' = log & event_write t x v, T' = T[t := running K(void), d[x:=v]] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayWrite updates [t]'s delta at [x] *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := d[x := v]]) TC g0. eexists. splits.
      * applys PlaySnoc Hplay.
        apply (PlayWrite _ _ _ _ _ _ _ d).
        -- assumption.
        -- lets HtinD: HdomD Htin. applys* binds_of_indom_read.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: ((D[t := d[x:=v]])[t] = d[x:=v]). { rew_map*. }
           rewrite Hd_new, Htc.
           exists state_running (K void). apply binds_update_same.
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
  - (* StepWriteVolatile: log' = log & event_write t x v, T' = T[t := running K(void)],
       commit onto the global head (the write, folded into the diff, is what
       gets committed -- [t] stays [state_running], unlike [StepEnd]) *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    match goal with H : global_commit _ _ _ _ _ = (_, _) |- _ =>
      unfolds global_commit; rewrite~ read_update_same in H; inverts H end.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + rewrite~ update_update. rewrite~ update_update. applys* describes_spawned_inplace.
    + rewrite~ update_update. rewrite~ update_update. applys* describes_new_inplace.
    + rewrite~ update_update. rewrite~ update_update. applys* describes_ended_inplace.
    + rewrite~ update_update. rewrite~ update_update. applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayWriteVolatile commits [t]'s delta (write folded in) onto the global head *)
      rewrite~ update_update. rewrite~ update_update.
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      forwards (st_old & e_old & Hbinds_delta): Hdelta t HtinX.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := g']) g'. eexists. splits.
      * applys PlaySnoc Hplay. applys PlayWriteVolatile.
        -- assumption.
        -- lets HtinD: HdomD HtinX. applys* binds_of_indom_read.
        -- assumption.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := g'][t] = g'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_running (K void). apply binds_update_same.
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
  - (* StepSpawn *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts* Hneq: (t <> t').
    match goal with Hpt : _ = (_, _) |- _ =>
      unfold global_commit in Hpt;
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
        destruct Hin as [[[Hin| ->]| ->]| ->].
        -- forwards Hdisj: (proj2 (Hdspawned t2) Hin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
        -- left. exists t. rew_listx*.
        -- asserts Htin: (t \indom T). { applys* indom_of_binds. }
           forwards Hdisj: (proj2 (Hdspawned t) Htin).
           destruct Hdisj as [(t1 & Hmem) | Hmem]; [left; exists t1 | right]; rew_listx*.
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
        -- exists (te_exp e') empty_diff g'.
           apply~ binds_update_neq. apply binds_update_same.
        -- destruct (classic (t2 = t)) as [->|Hneq3].
           ++ false Hnmem. rew_listx*.
           ++ asserts (e2 & d2 & c2 & Hbinds): (exists e2 d2 c2, binds T t2 (state_new, e2, d2, c2)).
              { apply (Hdnew t2). split.
                - rew_listx in Hdisj.
                  destruct Hdisj as [(t1 & Hmem) | ->].
                  + rew_listx in Hmem. destruct Hmem as [Hmem | Heq].
                    * left. exists* t1.
                    * congruence.
                  + right*.
                - intros Hc. apply Hnmem. rew_listx*. }
              exists e2 d2 c2.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq.
      * introv (e2 & d2 & c2 & Hbinds).
        destruct (classic (t2 = t')) as [->|Hneq2].
        -- split.
           ++ left. exists t. rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq].
              ** false Hnostart. exact contra.
              ** congruence.
        -- destruct (classic (t2 = t)) as [->|Hneq3].
           ++ apply binds_update_same_inv in Hbinds. congruence.
           ++ forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
              forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              asserts (Hdisj & Hnmemst):
                (((exists t1, mem (event_spawn t1 t2) log) \/ t2 = t_root)
                  /\ ~mem (event_start t2) log).
              { apply (Hdnew t2). exists e2 d2 c2. exact Hbinds3. }
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
        apply~ binds_update_neq.
      * introv (e2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq2].
        -- apply binds_update_same_inv in Hbinds. congruence.
        -- forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
           destruct (classic (t0 = t')) as [->|Hneq'].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              rew_listx. left. apply (Hdend t0). exists e2 h2. exact Hbinds3.
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
        -- exists (K t') (empty : diff) g'.
           apply binds_update_same.
        -- exists e2 d2 h2.
           apply~ binds_update_neq. apply~ binds_update_neq.
           apply~ binds_update_neq.
      * introv (e2 & d2 & h2 & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq2].
        -- apply binds_update_same_inv in Hbinds.
           asserts (Hmem & Hnend): (mem (event_start t) log /\ ~mem (event_end t) log).
           { apply (Hdrunning t). eauto. }
           split.
           ++ rew_listx*.
           ++ intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
              exact (Hnend contra).
        -- forwards Hbinds1: binds_update_neq_inv Hbinds; auto.
           destruct (classic (t0 = t')) as [->|Hneq'].
           ++ apply binds_update_same_inv in Hbinds1. congruence.
           ++ forwards Hbinds2: binds_update_neq_inv Hbinds1; auto.
              forwards Hbinds3: binds_update_neq_inv Hbinds2; auto.
              asserts (Hmem & Hnend): (mem (event_start t0) log /\ ~mem (event_end t0) log).
              { apply (Hdrunning t0). exists e2 d2 h2. exact Hbinds3. }
              split.
              ** rew_listx*.
              ** intros contra. rew_listx in contra. destruct contra as [contra|Heq]; [|congruence].
                 exact (Hnend contra).
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlaySpawn commits parent's delta; child starts at the new head *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty][t' := empty]) (TC[t := g'][t' := g']) g'. eexists. splits.
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
           exists state_new (te_exp e').
           apply~ binds_update_neq. apply binds_update_same.
        -- destruct (classic (t0 = t)) as [->|Hq2].
           ++ asserts Hd_t: ((D[t := empty][t' := empty])[t] = empty).
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              asserts Htc_t: ((TC[t := g'][t' := g'])[t] = g').
              { rewrite~ read_update_neq. rewrite read_update_same. auto. }
              rewrite Hd_t, Htc_t.
              exists state_running (K t').
              apply binds_update_same.
           ++ forwards~ Hin1: indom_update_inv Hin.
              destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1.
              destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2.
              destruct Hin3 as [->|Hin3]. { congruence. }
              asserts Hd0: ((D[t := empty][t' := empty])[t0] = D[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              asserts Htc0: ((TC[t := g'][t' := g'])[t0] = TC[t0]).
              { rewrite~ read_update_neq. rewrite~ read_update_neq. }
              rewrite Hd0, Htc0.
              forwards (ts' & e'' & Hbinds'): Hdelta t0 Hin3.
              exists ts' e''.
              apply~ binds_update_neq. apply~ binds_update_neq.
              apply~ binds_update_neq.
      * intros t0 Hin.
        destruct (classic (t0 = t')) as [->|Hq'].
        -- rew_dom. rew_set. right*.
        -- destruct (classic (t0 = t)) as [->|Hq2].
           ++ rew_dom. rew_set. left. right*.
           ++ forwards~ Hin1: indom_update_inv Hin. destruct Hin1 as [->|Hin1]. { congruence. }
              forwards~ Hin2: indom_update_inv Hin1. destruct Hin2 as [->|Hin2]. { congruence. }
              forwards~ Hin3: indom_update_inv Hin2. destruct Hin3 as [->|Hin3]. { congruence. }
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
              asserts HinTC: (t0 \indom TC). { applys~ HdomTC. }
              rew_dom. rew_set. left. left. exact HinTC.
  - (* StepJoin: log' = log & event_join t t', T' = T[t := running K(r), c:=g] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
    + applys* describes_locked_snoc.
    + applys* describes_free_snoc.
    + (* 7. Replay: PlayJoin fast-forwards [t] to the global head [g] *)
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      exists D (TC[t := g]) g. eexists. splits.
      * applys PlaySnoc Hplay. apply PlayJoin.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running (K r). apply binds_update_same.
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
  - (* StepLock: log' = log & event_lock t l, T' = T[t := ...,c:=g], L' = L[l := held t] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
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
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      exists D (TC[t := g]) g. eexists. splits.
      * applys PlaySnoc Hplay. apply PlayLock.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Htin: (t \indom T). { apply* indom_of_binds. }
           forwards (st' & e'' & Hbinds'): Hdelta t Htin.
           forwards* Heq: binds_inj Hbinds'.
           asserts Hd: (D[t] = d). { congruence. }
           rewrite Hd. rewrite read_update_same.
           exists state_running (K void). apply binds_update_same.
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
  - (* StepRelease: log' = log & event_unlock t l, commit delta, L' = L[l := free] *)
    lets (Hdspawned & Hdnew & Hdend & Hdrunning & Hdlock & Hdunlock & Hdplay): Hdesc.
    match goal with H : global_commit t g g' T G = _ |- _ =>
      unfold global_commit in H;
      replace (T[t]) with (state_running, te_exp e, d, c) in H by (forwards*: read_of_binds T);
      inverts H
    end.
    rewrite~ update_update.
    asserts (Hsmem & Hrnmem): (mem (event_start t) log /\ ~mem (event_end t) log).
    { apply (Hdrunning t). do 3 eexists. eassumption. }
    asserts HtinX: (t \indom T). { apply* indom_of_binds. }
    splits.
    + applys* describes_spawned_inplace.
    + applys* describes_new_inplace.
    + applys* describes_ended_inplace.
    + applys* describes_running_inplace.
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
      destruct Hdplay as (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC).
      match goal with Hh : is_global_head G _ |- _ => rename Hh into Hheadr end.
      forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
      forwards Heqg0: is_global_head_unique HwfG Hhead0 Hheadr. subst g0.
      asserts Htin: (t \indom T). { apply* indom_of_binds. }
      forwards (st_old & e_old & Hbinds_delta): Hdelta t Htin.
      forwards* Heq: binds_inj Hbinds_delta.
      asserts Hd: (D[t] = d). { congruence. }
      asserts Htc: (TC[t] = c). { congruence. }
      exists (D[t := empty]) (TC[t := g']) g'. eexists. splits.
      * applys PlaySnoc Hplay. applys PlayUnlock.
        -- lets HtinD: HdomD Htin. applys* binds_of_indom_read.
        -- assumption.
      * intros t0 Hin.
        destruct (classic (t0 = t)) as [->|Hneq].
        -- asserts Hd_new: (D[t := empty][t] = empty). { rew_map*. }
           asserts Htc_new: (TC[t := g'][t] = g'). { rew_map*. }
           rewrite Hd_new, Htc_new.
           exists state_running (K void). apply binds_update_same.
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
Qed.
