From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingBranching.
From Vcm Require Import LoggingBranchingFacts.

Import Graph.
Import GraphFacts.
Import Branching.
Import Log.
Import LogFacts.
Import LoggingBranching.
Import LoggingBranchingFacts.

Existing Instance inhab_val.
Existing Instance inhab_exp.

(* =========================== *)
(* Lemmas used for equivalence *)
(* =========================== *)

(* A value in a thread's delta corresponds to a write event by that thread with
   no later commit event by that thread: the write is genuinely uncommitted.
   This is the play-log analogue of "the delta is the uncommitted suffix",
   stated with the correct [is_commit_event] (flush) boundary. *)
Lemma delta_is_uncommitted_write :
  forall log D TC G LC VC CH t x v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists m,
      LibList.Nth m log (event_write t x v) /\
      (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
Proof.
  introv Hplay Hdom Hbinds.
  inductions Hplay.
  - (* PlayNil: D = empty *)
    rew_dom. rew_set in Hdom.
    branches;
      [forwards*: indom_empty_inv|].
    subst.
    rewrite read_update_same in Hbinds.
    forwards* Heq: binds_empty_false Hbinds. typeclass.
  - (* PlaySnoc *)
    inverts H.
    + (* PlayRead *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayReadVolatile: D unchanged, never a commit event *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayWrite (event_write t0 x0 v0) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        destruct (classic (x = x0)) as [Hei | Hnei].
        { (* same variable: the new event is the witness *)
          subst x. forwards ->: binds_update_same_inv Hbinds.
          match goal with |- exists m, LibList.Nth m (?lg & _) _ /\ _ => exists (length lg) end.
          split.
          - applys* Nth_app_r'.
          - introv Hle HN Hg.
            forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
            + forwards Hib: Nth_inbound HN'. exfalso. nat_math.
            + subst ep. simpl. auto. }
        { (* different variable: carry the older write forward *)
          forwards Hbd: binds_update_neq_inv Hbinds Hnei.
          lets Hin: (indom_of_binds H12).
          asserts Hb': (binds (D'[t0]) x v). { forwards: read_of_binds H12. subst*. }
          forwards* (wm & wHN & wHns): IHHplay.
          exists wm. split;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros _; simpl; auto ]. } }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns): IHHplay.
        exists wm. split;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros _; simpl; auto ]. }
    + (* PlayWriteVolatile (event_write t0 x0 v0): flushes D[t0], and IS a
         commit event -- but only for thread [t0], so this only matters when
         [t = t0], which is excluded here since [D[t0]] is flushed to empty. *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns): IHHplay.
        exists wm. split;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence ]. }
    + (* PlayStart *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayEnd (event_end t0): flushes D[t0] *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns): IHHplay.
        exists wm. split;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence ]. }
    + (* PlaySpawn (event_spawn t1 t2): flushes D[t1] and D[t2] *)
      destruct (classic (t = t2)) as [Het2 | Hneq2].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        destruct (classic (t = t1)) as [Het1 | Hneq1].
        { subst t. rewrite read_update_same in Hbinds.
          lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
        { rewrite~ read_update_neq in Hbinds.
          asserts Hin: (t \indom D').
          { lets [Hc2 | Hd2]: (indom_update_inv Hdom). congruence.
            lets [Hc1 | Hd1]: (indom_update_inv Hd2). congruence. exact Hd1. }
          forwards* (wm & wHN & wHns): IHHplay.
          exists wm. split;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence ]. } }
    + (* PlayJoin: merge, D unchanged *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayLock: merge, D unchanged *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayUnlock (event_unlock t0 l): flushes D[t0] *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns): IHHplay.
        exists wm. split;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence ]. }
Qed.

Lemma conflict_free_last_local_write :
  forall log D TC G LC VC CH t x v,
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t x v.
Proof.
  introv Hcf Hplay Hdom Hdelta.
  hint conflict_free_last_inv.
  inductions Hplay.
  - (* PlayNil: D = empty *)
    rew_dom. rew_set in Hdom.
    branches;
      [forwards*: indom_empty_inv|].
    subst.
    rewrite read_update_same in Hdelta.
    forwards* Heq: binds_empty_false Hdelta. typeclass.
  - inverts H.
    + (* PlayRead*)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayReadVolatile *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayWrite *)
      destruct (classic (t = t0)).
      * subst. rewrite read_update_same in Hdelta.
        destruct (classic (x = x0)).
        -- subst.
           forwards ->: binds_update_same_inv Hdelta.
           exists. rew_listx*. cases_if*.
        -- forwards~ Hdelta': binds_update_neq_inv Hdelta.
           asserts Hbinds: (binds D'[t0] x v).
           {
             forwards : read_of_binds H12.
             subst*.
           }
           forwards* (log' & Hfilter): IHHplay.
           exists log'.
           rew_listx. cases_if. rew_list*.
      * rewrite~ read_update_neq in Hdelta.
        asserts Hdom': (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (log' & Hfilter): IHHplay.
        exists log'.
        rew_listx. cases_if as Hwrites.
        -- simpl in Hwrites. subst. false.
           forwards (m0 & HN0 & Hns0): delta_is_uncommitted_write Hplay Hdom' Hdelta.
           forwards Hlt0: Nth_inbound HN0.
           asserts HN0f:
             (LibList.Nth m0 (log & event_write t0 x0 v0) (event_write t x0 v)).
           { applys* Nth_app_l. }
           asserts Hnth:
             (LibList.Nth (length log) (log & event_write t0 x0 v0) (event_write t0 x0 v0)).
           { applys* Nth_app_r'. }
           asserts Hacc: (accesses_variable x0 (event_write t0 x0 v0)). { reflexivity. }
           forwards Hhb: Hcf HN0f Hnth Hacc Hlt0.
           asserts Hns0f:
             (forall p ep, m0 <= p ->
                LibList.Nth p (log & event_write t0 x0 v0) ep ->
                get_thread ep = t -> ~ is_commit_event ep).
           { applys no_commit_event_snoc Hns0. intros _; simpl; auto. }
           asserts Hem: (get_thread (event_write t x0 v) = t). { reflexivity. }
           forwards Hgt0: hb_preserves_thread Hhb HN0f Hem Hns0f Hnth.
           simpl in Hgt0. congruence.
        -- rew_list*.
    + (* PlayWriteVolatile: flushes D[t0] to empty, so [t = t0] is impossible
         given [binds D[t] x v]; the cross-thread case is otherwise the same
         conflict-freedom argument as [PlayWrite]. *)
      asserts Hneq: (t <> t0).
      { intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hdelta.
      asserts Hdom': (t \indom D').
      { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if as Hwrites.
      -- simpl in Hwrites. subst. false.
         forwards (m0 & HN0 & Hns0): delta_is_uncommitted_write Hplay Hdom' Hdelta.
         forwards Hlt0: Nth_inbound HN0.
         asserts HN0f:
           (LibList.Nth m0 (log & event_write t0 x0 v0) (event_write t x0 v)).
         { applys* Nth_app_l. }
         asserts Hnth:
           (LibList.Nth (length log) (log & event_write t0 x0 v0) (event_write t0 x0 v0)).
         { applys* Nth_app_r'. }
         asserts Hacc: (accesses_variable x0 (event_write t0 x0 v0)). { reflexivity. }
         forwards Hhb: Hcf HN0f Hnth Hacc Hlt0.
         asserts Hns0f:
           (forall p ep, m0 <= p ->
              LibList.Nth p (log & event_write t0 x0 v0) ep ->
              get_thread ep = t -> ~ is_commit_event ep).
         { applys no_commit_event_snoc Hns0. intros Hgt; simpl in Hgt; congruence. }
         asserts Hem: (get_thread (event_write t x0 v) = t). { reflexivity. }
         forwards Hgt0: hb_preserves_thread Hhb HN0f Hem Hns0f Hnth.
         simpl in Hgt0. congruence.
      -- rew_list*.
    + (* PlayStart *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayEnd *)
      asserts Hneq: (t <> t0).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlaySpawn *)
      asserts Hneq2: (t <> t2).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      asserts Hneq1: (t <> t1).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. repeat (branches; [|congruence]).
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayJoin *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayLock*)
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
    + (* PlayUnlock*)
      asserts Hneq: (t <> t0).
      {
        intros contra.
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta).
        forwards*: indom_empty_inv.
      }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'.
      rew_listx. cases_if. rew_list*.
Qed.

(* The commit history is parallel to the log. *)
Lemma play_log_CH_length :
  forall log s0 sf CH,
    play_log log s0 sf CH ->
    length CH = length log.
Proof.
  introv Hplay. induction Hplay; rew_list*.
Qed.

(* A single play step only grows the graph: existing ancestry is preserved. *)
Lemma play_event_graph_extends :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' x y,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    ancestor G' x y ->
    ancestor G'' x y.
Proof.
  introv Hpe Hanc.
  inverts Hpe; auto using ancestor_graph_commit, ancestor_graph_merge.
Qed.

(* [is_latest_value_graph_commit_mono], [is_latest_value_graph_merge_mono],
   [is_latest_value_graph_commit_fresh_writer], and
   [is_latest_value_graph_merge_fresh] are generic graph facts, with no
   Branching/logging specifics, and live in GraphFacts.v. *)

(* After any play step, each thread's commit pointer advances to a descendant
   (in the new graph) -- except a freshly spawned thread, hence the side-condition. *)
Lemma play_event_TC_advance :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' t,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    (forall t1 t2, E = event_spawn t1 t2 -> t <> t2) ->
    ancestor G'' (TC'[t]) (TC''[t]).
Proof.
  introv Hpe Hspawn.
  destruct E as [t1 t2 | t1 t2 | t0 x v | t0 x v | t0 ll | t0 ll | t0 | t0];
    inverts Hpe as Hb Hf Hbd; try apply ancestor_refl.
  - (* spawn t1 t2 *)
    forwards Hnt2: Hspawn (eq_refl : event_spawn t1 t2 = event_spawn t1 t2).
    destruct (classic (t = t1)) as [Heqt | Hnt1].
    + subst t. rewrite read_update_neq by congruence. rewrite read_update_same.
      forwards Hrd: read_of_binds Hb. rewrite <- Hrd. apply ancestor_graph_commit_edge.
    + rewrite read_update_neq by congruence. rewrite read_update_neq by congruence.
      apply ancestor_refl.
  - (* join t1 t2 *)
    destruct (classic (t = t1)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hb. rewrite <- Hrd. apply ancestor_graph_merge_edge_l.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
  - (* read t0 x v, volatile: a pull (merge) *)
    destruct (classic (t = t0)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hf. rewrite <- Hrd. apply ancestor_graph_merge_edge_l.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
  - (* write t0 x v, volatile: a pull then push (merge then commit) *)
    destruct (classic (t = t0)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hbd. rewrite <- Hrd.
      applys ancestor_trans.
      * apply ancestor_graph_commit. apply ancestor_graph_merge_edge_l.
      * apply ancestor_graph_commit_edge.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
  - (* lock t0 ll *)
    destruct (classic (t = t0)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hb. rewrite <- Hrd. apply ancestor_graph_merge_edge_l.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
  - (* unlock t0 ll *)
    destruct (classic (t = t0)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hb. rewrite <- Hrd. apply ancestor_graph_commit_edge.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
  - (* end t0 *)
    destruct (classic (t = t0)) as [Heqt | Hne].
    + subst t. rewrite read_update_same.
      forwards Hrd: read_of_binds Hb. rewrite <- Hrd. apply ancestor_graph_commit_edge.
    + rewrite read_update_neq by congruence. apply ancestor_refl.
Qed.

(* The commit pointer recorded for an event is an ancestor of the thread's final
   commit (pointers only advance). *)
Lemma CH_ancestor_TC :
  forall log s0 D TC G LC VC CH m em t cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log em -> get_thread em = t ->
    LibList.Nth m CH cm ->
    ancestor G cm (TC[t]).
Proof.
  introv Hwf Hplay. gen m em t cm.
  inductions Hplay; introv HNlog Hgt HNch.
  - inverts HNlog.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* prefix event *)
      forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hanc: IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0 Hgt HN0ch.
      apply ancestor_trans with (c' := TC'[t]).
      * eapply play_event_graph_extends; eassumption.
      * eapply play_event_TC_advance; [ eassumption |].
        -- introv Heq. subst E.
           forwards Hne: spawned_thread_no_prior_event Hwf HN0.
           congruence.
    + (* last event = E *)
      subst em.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      subst cm. rewrite Hgt. apply ancestor_refl.
Qed.

(* Same thread: commit pointers only move forward along the log, so an earlier
   event's commit is an ancestor of a later one's. *)
Lemma CH_thread_monotone :
  forall log s0 D TC G LC VC CH m n em en t cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log em -> get_thread em = t ->
    LibList.Nth n log en -> get_thread en = t ->
    m <= n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. gen m n em en t cm cn.
  inductions Hplay; introv HNlogm Hgtm HNlogn Hgtn Hle HNchm HNchn.
  - inverts HNlogm.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + (* n < length log: both in prefix *)
      forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & HemE)]: Nth_last_inv HNlogm.
      2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm.
      2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn.
      2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC'))
            HNm0 Hgtm HNn0 Hgtn Hle HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* n = length log: en = E *)
      subst en.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      subst cn.
      destruct (classic (m = length log)) as [Hmis | Hmne].
      * (* m = n: cm = cn *)
        subst m.
        forwards [HNchm0 | (_ & Hcmeq)]: Nth_last_inv HNchm.
        { forwards Hib: Nth_inbound HNchm0. nat_math. }
        subst cm. rewrite Hgtn. apply ancestor_refl.
      * (* m < n: apply CH_ancestor_TC on the full play *)
        rewrite Hgtn.
        forwards Hfull: (>> PlaySnoc Hplay H).
        forwards Hfin: (>> CH_ancestor_TC Hwf Hfull HNlogm Hgtm HNchm).
        exact Hfin.
Qed.

(* A single play step leaves thread [t]'s commit pointer untouched whenever the
   event is neither [t] acting nor a spawn of [t]. *)
Lemma play_event_TC_preserved :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' t c,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    binds TC' t c ->
    get_thread E <> t ->
    (forall t1, E <> event_spawn t1 t) ->
    binds TC'' t c.
Proof.
  introv Hpe Hb Hgt Hsp.
  inverts Hpe; simpls; try assumption.
  - (* PlayReadVolatile *) applys binds_update_neq; [ congruence | assumption ].
  - (* PlayWriteVolatile *) applys binds_update_neq; [ congruence | assumption ].
  - (* PlayEnd *) applys binds_update_neq; [ congruence | assumption ].
  - (* PlaySpawn *)
    applys binds_update_neq.
    { intro Heq. subst. eapply Hsp; reflexivity. }
    applys binds_update_neq; [ congruence | assumption ].
  - (* PlayJoin *) applys binds_update_neq; [ congruence | assumption ].
  - (* PlayLock *) applys binds_update_neq; [ congruence | assumption ].
  - (* PlayUnlock *) applys binds_update_neq; [ congruence | assumption ].
Qed.

(* After [t2] ends, its commit pointer is frozen at the commit recorded for the
   end event: it equals [t2]'s pointer in any later state. *)
Lemma ended_thread_pointer :
  forall log s0 D TC G LC VC CH m t2 cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_end t2) ->
    LibList.Nth m CH cm ->
    binds TC t2 cm.
Proof.
  introv Hwf Hplay. gen m t2 cm.
  inductions Hplay; introv HNlog HNch.
  - inverts HNlog.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* end is in the prefix; the appended event leaves [t2]'s pointer alone *)
      forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & _)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hbpre: (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0 HN0ch).
      forwards (Hgt & Hns): event_after_end_snoc Hwf HN0.
      applys play_event_TC_preserved H Hbpre Hgt Hns.
    + (* end is the last (appended) event *)
      subst E.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      inverts H. simpls.
      rewrite read_update_same in Hcmeq. subst cm. applys binds_update_same.
Qed.

(* Symmetric fact for a freshly spawned thread, before it starts: its pointer is
   the commit recorded for the spawn event. *)
Lemma spawned_thread_pointer :
  forall log s0 D TC G LC VC CH m t1 t2 cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_spawn t1 t2) ->
    ~ LibList.mem (event_start t2) log ->
    LibList.Nth m CH cm ->
    binds TC t2 cm.
Proof.
  introv Hwf Hplay. gen m t1 t2 cm.
  inductions Hplay; introv HNlog Hnst HNch.
  - inverts HNlog.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* spawn is in the prefix *)
      forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & _)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      asserts Hnst0: (~ LibList.mem (event_start t2) log).
      { intro Hm. apply Hnst. rewrite mem_last_eq. left. exact Hm. }
      forwards Hbpre: (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0 Hnst0 HN0ch).
      forwards (Hgt & Hns): event_after_spawn_snoc Hwf HN0 Hnst.
      applys play_event_TC_preserved H Hbpre Hgt Hns.
    + (* spawn is the last (appended) event *)
      subst E.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      inverts H. simpls.
      destruct (classic (t1 = t2)) as [Ht12 | Ht12].
      * rewrite Ht12 in Hcmeq. rewrite read_update_same in Hcmeq.
        subst cm. applys binds_update_same.
      * rewrite read_update_neq in Hcmeq; [ | auto ].
        rewrite read_update_same in Hcmeq. subst cm. applys binds_update_same.
Qed.

(* A single play step leaves [lc_read LC l] untouched whenever the event is not
   an unlock of [l] (only [PlayUnlock] writes the lock map; [PlayLock] only
   reads [lc_read LC l], it never updates [LC]). *)
Lemma play_event_LC_preserved :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' l,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    (forall t3, E <> event_unlock t3 l) ->
    lc_read LC'' l = lc_read LC' l.
Proof.
  introv Hpe Hne. inverts Hpe; try reflexivity.
  - (* PlayUnlock t l0: LC'' = LC'[l0 := c']; l0 <> l from Hne *)
    unfold lc_read. apply read_default_update_neq.
    intro Heq. subst. eapply Hne; reflexivity.
Qed.

(* A single play step leaves [vc_read VC x] untouched whenever the event is
   not a write of [x] (only [PlayWriteVolatile] writes the volatile map;
   [PlayReadVolatile] only reads [vc_read VC x], it never updates [VC]). *)
Lemma play_event_VC_preserved :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' x,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    (forall t3 v3, E <> event_write t3 x v3) ->
    vc_read VC'' x = vc_read VC' x.
Proof.
  introv Hpe Hne. inverts Hpe; try reflexivity.
  - (* PlayWriteVolatile t0 x0 v0: VC'' = VC'[x0 := c'']; x0 <> x from Hne *)
    unfold vc_read. apply read_default_update_neq.
    intro Heq. subst. eapply Hne; reflexivity.
Qed.

(* Held-lock invariant: if the [l]-filter of the log ends in [event_lock t l]
   (so [t] currently holds [l]), then [l]'s stored commit is an ancestor of [t]'s
   current commit. Acquiring [l] merged [LC[l]] into [t], and [LC[l]] is unchanged
   until [t] releases. *)
Lemma held_dominates :
  forall log s0 D TC G LC VC CH l t pre,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.filter (fun e => touches_lock l e) log = pre & event_lock t l ->
    ancestor G (lc_read LC l) (TC[t]).
Proof.
  introv Hwf Hplay. gen l t pre.
  inductions Hplay; introv Hfilter.
  - rew_listx in Hfilter. false. applys nil_eq_last_inv Hfilter.
  - forwards Hwf0: wf_log_last_inv Hwf.
    rew_listx in Hfilter.
    cases_if as Ht.
    + (* E touches l: the appended event must be the acquiring lock itself *)
      rew_list in Hfilter.
      forwards (Hpre_eq & HEeq): last_eq_last_inv Hfilter.
      subst E.
      inverts H as Hb1 Hfr.
      (* PlayLock: merged [lc_read LC' l] into [t] *)
      rewrite read_update_same. apply ancestor_graph_merge_edge_r.
    + (* E does not touch l: LC[l] and the held relation are preserved *)
      rew_list in Hfilter.
      asserts Hmemfilt:
        (mem (event_lock t l) (LibList.filter (fun e => touches_lock l e) log)).
      { rewrite Hfilter, mem_last_eq. right. reflexivity. }
      forwards (Hmemf & _): mem_filter_inv Hmemfilt.
      forwards (klock & Hklock): mem_Nth Hmemf.
      forwards Hanccl:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) Hfilter).
      asserts HLCeq: (lc_read LC l = lc_read LC' l).
      { applys play_event_LC_preserved H.
        intros t3 Heq. apply Ht. rewrite Heq. reflexivity. }
      rewrite HLCeq.
      apply ancestor_trans with (c' := TC'[t]).
      -- eapply play_event_graph_extends; eassumption.
      -- applys play_event_TC_advance. eassumption.
         introv Heqsp. rewrite Heqsp in Hwf.
         forwards Hng: spawned_thread_no_prior_event Hwf Hklock.
         cbn [get_thread] in Hng. exact Hng.
Qed.

(* Lock semantics: just before [t] unlocks [l], the lock holds some commit [cl]
   that is an ancestor of [t]'s current commit. *)
Lemma unlock_holder_dominates :
  forall log s0 D TC G LC VC CH t l c,
    wf_log (log & event_unlock t l) ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    binds TC t c ->
    ancestor G (lc_read LC l) c.
Proof.
  introv Hwf Hplay Hbc.
  forwards (pre & Hpre): unlock_prev_lock Hwf.
  forwards Hwf0: wf_log_last_inv Hwf.
  forwards Hanc: (>> held_dominates Hwf0 Hplay Hpre).
  forwards Hrd: read_of_binds Hbc.
  rewrite <- Hrd. exact Hanc.
Qed.

(* The lock chain: every unlock-of-[l] commit is an ancestor of [l]'s current
   stored commit. [LC[l]] only advances to descendants -- each unlock deposits a
   child of the holder's commit, which (holder fact) already dominates the
   previous [LC[l]]. *)
Lemma unlock_ancestor_LC :
  forall log s0 D TC G LC VC CH m t1 l cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth m CH cm ->
    ancestor G cm (lc_read LC l).
Proof.
  introv Hwf Hplay. gen m t1 l cm.
  inductions Hplay; introv HNlog HNch.
  - inverts HNlog.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* unlock m is in the prefix *)
      forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & _)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0 HN0ch).
      destruct (classic (exists t3, E = event_unlock t3 l)) as [(t3 & HE) | Hne].
      * (* same lock: chain through the holder's commit *)
        subst E.
        inverts H as Hbc Hfresh Hbd.
        forwards Hdom: (>> unlock_holder_dominates Hwf Hplay Hbc).
        asserts HLCeq: (lc_read LC'[l:=c'] l = c').
        { unfold lc_read. apply read_default_update_same. }
        rewrite HLCeq.
        apply ancestor_trans with (c' := c).
        -- apply ancestor_graph_commit.
           apply ancestor_trans with (c' := lc_read LC' l).
           ++ exact Hanc.
           ++ exact Hdom.
        -- apply ancestor_graph_commit_edge.
      * (* different lock (or non-unlock event): LC[l] preserved *)
        asserts HLCeq: (lc_read LC l = lc_read LC' l).
        { applys play_event_LC_preserved H.
          intros t3 Heq. apply Hne. exists t3. exact Heq. }
        rewrite HLCeq.
        eapply play_event_graph_extends; eassumption.
    + (* unlock m is the last (appended) event *)
      subst E.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      inverts H as Hbc Hfresh Hbd.
      cbn [get_thread] in Hcmeq.
      rewrite read_update_same in Hcmeq. subst cm.
      asserts HLCeq: (lc_read LC'[l:=c'] l = c').
      { unfold lc_read. apply read_default_update_same. }
      rewrite HLCeq.
      apply ancestor_refl.
Qed.

(* The volatile chain, simpler than the lock chain above since there is no
   "currently held" state to dominate through: every write-of-[x] commit is an
   ancestor of the current [vc_read VC x], by chaining directly through each
   subsequent write's own pull (merge) of the previous [vc_read VC x]. *)
Lemma write_ancestor_VC :
  forall log s0 D TC G LC VC CH m t1 x v cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    LibList.Nth m log (event_write t1 x v) ->
    LibList.Nth m CH cm ->
    ancestor G cm (vc_read VC x).
Proof.
  introv Hwf Hplay Hxvol. gen m t1 v cm.
  inductions Hplay; introv HNlog HNch.
  - inverts HNlog.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* write m is in the prefix *)
      forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & _)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) Hxvol HN0 HN0ch).
      destruct (classic (exists t3 v3, E = event_write t3 x v3)) as [(t3 & v3 & HE) | Hne].
      * (* another write to x: [inverts] splits into [PlayWrite] (impossible,
           since [x] IS volatile here) and [PlayWriteVolatile] (the real
           case), chaining through the intermediate [vc_read VC' x] *)
        subst E.
        inverts H as Hxvol' Hbd Hbc Hfresh Hfresh2.
        -- false.
        -- asserts HVeq: (vc_read VC'[x:=c''] x = c'').
           { unfold vc_read. apply read_default_update_same. }
           rewrite HVeq.
           apply ancestor_trans with (c' := vc_read VC' x).
           ++ apply ancestor_graph_commit. apply ancestor_graph_merge. exact Hanc.
           ++ apply ancestor_trans with (c' := c').
              ** apply ancestor_graph_commit. apply ancestor_graph_merge_edge_r.
              ** apply ancestor_graph_commit_edge.
      * (* different event: [vc_read VC x] preserved, graph only grows *)
        asserts HVeq: (vc_read VC x = vc_read VC' x).
        { applys play_event_VC_preserved H.
          intros t3 v3 Heq. apply Hne. exists t3 v3. exact Heq. }
        rewrite HVeq.
        eapply play_event_graph_extends; eassumption.
    + (* write m is the last (appended) event *)
      subst E.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      inverts H as Hxvol' Hbd Hbc Hfresh Hfresh2.
      -- false.
      -- cbn [get_thread] in Hcmeq.
         rewrite read_update_same in Hcmeq. subst cm.
         asserts HVeq: (vc_read VC'[x:=c''] x = c'').
         { unfold vc_read. apply read_default_update_same. }
         rewrite HVeq.
         apply ancestor_refl.
Qed.

(* The three synchronisation edges: each mirrors the graph_merge / graph_commit
   performed by the corresponding play_event, so the source's commit is an
   ancestor of the target's. *)
Lemma hb_lock_pointer_ancestor :
  forall log s0 D TC G LC VC CH m n t1 t2 l cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth n log (event_lock t2 l) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. gen m n t1 t2 l cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + (* lock is in the prefix: induction hypothesis *)
      forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC'))
            HNm0 HNn0 Hlt HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* lock is the last (appended) event: it merges [l]'s stored commit *)
      subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards Hanc_cm: (>> unlock_ancestor_LC Hwf0 Hplay HNm0 HNchm0).
      forwards Hanc_lift: play_event_graph_extends H Hanc_cm.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H as Hbc1 Hfresh.
      (* PlayLock: merges [lc_read LC l] into [t2] ([LC] is unchanged) *)
      cbn [get_thread] in Hcneq.
      rewrite read_update_same in Hcneq. subst cn.
      apply ancestor_trans with (c' := lc_read LC l).
      -- exact Hanc_lift.
      -- apply ancestor_graph_merge_edge_r.
Qed.

Lemma hb_spawn_pointer_ancestor :
  forall log s0 D TC G LC VC CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_spawn t1 t2) ->
    LibList.Nth n log (event_start t2) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. gen m n t1 t2 cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + (* start is in the prefix: induction hypothesis *)
      forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC'))
            HNm0 HNn0 Hlt HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* start is the last (appended) event: spawn's commit = start's commit *)
      subst E.
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hns0: start_not_in_prefix Hwf.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards Hbm: (>> spawned_thread_pointer Hwf0 Hplay HNm0 Hns0 HNchm0).
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H. cbn [get_thread] in Hcneq.
      forwards Hrd: read_of_binds Hbm.
      assert (cm = cn) as Hcc by (rewrite <- Hrd; exact Hcneq).
      rewrite Hcc. apply ancestor_refl.
Qed.

Lemma hb_join_pointer_ancestor :
  forall log s0 D TC G LC VC CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_end t2) ->
    LibList.Nth n log (event_join t1 t2) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. gen m n t1 t2 cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + (* join is in the prefix: induction hypothesis *)
      forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC'))
            HNm0 HNn0 Hlt HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* join is the last (appended) event: it merges [t2]'s (frozen) commit *)
      subst E.
      forwards Hwf0: wf_log_last_inv Hwf.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards Hbm: (>> ended_thread_pointer Hwf0 Hplay HNm0 HNchm0).
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H as Hb1 Hb2 Hfresh. cbn [get_thread] in Hcneq.
      rewrite read_update_same in Hcneq.
      subst cn.
      assert (cm = c2) as Heqc. { applys binds_inj Hbm Hb2. typeclass. }
      rewrite Heqc. apply ancestor_graph_merge_edge_r.
Qed.

(* Volatile synchronisation: a write of a volatile [x] is an ancestor of every
   later read of [x], mirroring [hb_lock_pointer_ancestor] but through
   [write_ancestor_VC] (there is no "currently held" state, so every prior
   write chains directly through [vc_read VC x], not just the last one). *)
Lemma hb_volatile_pointer_ancestor :
  forall log s0 D TC G LC VC CH m n t1 t2 x v v' cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    LibList.Nth m log (event_write t1 x v) ->
    LibList.Nth n log (event_read t2 x v') ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay Hxvol. gen m n t1 t2 v v' cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + (* read is in the prefix: induction hypothesis *)
      forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hanc:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) Hxvol
            HNm0 HNn0 Hlt HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* read is the last (appended) event: it merges [x]'s stored commit *)
      subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards Hanc_cm: (>> write_ancestor_VC Hwf0 Hplay Hxvol HNm0 HNchm0).
      forwards Hanc_lift: play_event_graph_extends H Hanc_cm.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H as Hxvol' Hbc Hfresh.
      -- (* PlayRead: impossible, since [x] IS volatile here *) false.
      -- (* PlayReadVolatile: merges [vc_read VC x] into [t2] ([VC] unchanged) *)
         cbn [get_thread] in Hcneq.
         rewrite read_update_same in Hcneq. subst cn.
         apply ancestor_trans with (c' := vc_read VC x).
         ++ exact Hanc_lift.
         ++ apply ancestor_graph_merge_edge_r.
Qed.

(* happens-before implies commit-pointer ancestry. Every hb edge is one
   of the four cases above; transitivity composes them. *)
Lemma hb_pointer_ancestor :
  forall log s0 D TC G LC VC CH m n cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    hb log m n ->
    LibList.Nth m CH cm ->
    LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay Hhb. gen cm cn.
  induction Hhb as
    [ m n e1 e2 HN1 HN2 Heq Hlt
    | n m t1 t2 l HNu HNl Hlt
    | m n t1 t2 HNs HNst Hlt
    | m n t1 t2 HNe HNj Hlt
    | m n t1 t2 x v v' Hxvol HNw HNr Hlt
    | m n k Hmk IHmk Hkn IHkn ];
    introv HNchm HNchn.
  - (* HbPo *)
    asserts Hle: (m <= n). { nat_math. }
    applys* (>> CH_thread_monotone Hwf Hplay HN1 HN2 Hle HNchm HNchn).
  - (* HbLock *)
    applys (>> hb_lock_pointer_ancestor Hwf Hplay HNu HNl Hlt HNchm HNchn).
  - (* HbSpawn *)
    applys (>> hb_spawn_pointer_ancestor Hwf Hplay HNs HNst Hlt HNchm HNchn).
  - (* HbJoin *)
    applys (>> hb_join_pointer_ancestor Hwf Hplay HNe HNj Hlt HNchm HNchn).
  - (* HbVolatile *)
    applys (>> hb_volatile_pointer_ancestor Hwf Hplay Hxvol HNw HNr Hlt HNchm HNchn).
  - (* HbTrans *)
    forwards (ek & HNlogk): hb_Nth_r Hmk.
    forwards Hlenk: Nth_inbound HNlogk.
    forwards Hlench: play_log_CH_length Hplay.
    asserts Hklt: (k < length CH). { rewrite Hlench. exact Hlenk. }
    forwards (ck & HNchk): Nth_inbound_inv Hklt.
    forwards Hanc1: IHmk HNchm HNchk.
    forwards Hanc2: IHkn HNchk HNchn.
    applys* ancestor_trans.
Qed.

(* Every commit that writes [x = v] in a played graph corresponds to a log write
   event of [x = v]: commits are created only by flushing a thread's delta, whose
   [x = v] binding comes (via [delta_is_uncommitted_write]) from a write event. *)
Lemma graph_writes_log_write :
  forall log D TC G LC VC CH cx x v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    graph_writes G cx x v ->
    exists tw m, LibList.Nth m log (event_write tw x v).
Proof.
  introv Hplay. gen cx x v. inductions Hplay; introv Hgw.
  - destruct Hgw as (dd & Hgb & Hbd). simpls.
    destruct (classic (cx = root_commit)).
    + subst.
      forwards Hbinds: binds_update_same_inv Hgb.
      subst.
      forwards* Heq: binds_empty_false Hbd. typeclass.
    + forwards~ Hbinds: binds_update_neq_inv Hgb.
      forwards* Heq: binds_empty_false Hbinds. typeclass.
  - rename H into Hpe.
    inverts Hpe.
    1,3,5: (forwards* (tw & m0 & HN): IHHplay;
           exists tw m0; rew_list; applys Nth_app_l HN).
    + (* PlayReadVolatile: graph_merge *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
    + (* PlayWriteVolatile: graph_commit, but the committed diff is
         [d[x0:=v0]] (the just-written value folded in) rather than simply
         the pre-existing delta [d], so [x = x0] needs its own case: the
         just-appended event is directly the witness. *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc]
      end.
      { subst cx.
        forwards Hbdd: graph_writes_graph_commit_same Hgw.
        destruct (classic (x = x0)) as [Hxeq | Hxneq].
        - subst x0.
          forwards ->: binds_update_same_inv Hbdd.
          exists t (length log). rew_list. applys* Nth_app_r'.
        - forwards Hbdd': binds_update_neq_inv Hbdd Hxneq.
          match goal with
          | HbD : binds ?DD ?tt d, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd';
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd';
            exists tt m'; rew_list; applys Nth_app_l HNm'
          end. }
      { forwards Hgw': graph_writes_graph_commit_inv Hc Hgw.
        (* [Hgw'] is at the intermediate merge graph -- peel that too, since
           its own fresh commit [c'] carries no data either. *)
        destruct (classic (cx = c')) as [Hc2 | Hc2].
        - subst cx. false. applys graph_writes_graph_merge_same_false Hgw'.
        - forwards Hgw'': graph_writes_graph_merge_inv Hc2 Hgw'.
          forwards* (tw & m0 & HN): IHHplay.
          exists tw m0. rew_list. applys Nth_app_l HN. }
    + (* PlayEnd: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            exists tt m'; rew_list; applys Nth_app_l HNm'
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
    + (* PlaySpawn: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            exists tt m'; rew_list; applys Nth_app_l HNm'
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
    + (* PlayJoin: graph_merge *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
    + (* PlayLock: graph_merge *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
    + (* PlayUnlock: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            exists tt m'; rew_list; applys Nth_app_l HNm'
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
Qed.

(* A play step preserves every pre-existing committed write (the new commit is
   fresh, so distinct from any existing writer). *)
Lemma play_event_graph_writes_mono :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' cs x v,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    graph_writes G' cs x v ->
    graph_writes G'' cs x v.
Proof.
  introv Hpe Hgw. forwards Hin: graph_writes_to_indom Hgw.
  inverts Hpe.
  - exact Hgw. (* PlayRead *)
  - (* PlayReadVolatile: single merge layer *)
    apply graph_writes_graph_merge; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - exact Hgw. (* PlayWrite *)
  - (* PlayWriteVolatile: commit wrapping merge -- two layers to lift through *)
    apply graph_writes_graph_commit.
    + intro Heq; subst cs.
      match goal with Hf : commit_fresh (graph_merge _ _ _ _) _ |- _ =>
        applys commit_fresh_not_indom Hf; apply* graph_merge_indom end.
    + apply graph_writes_graph_merge; [ | exact Hgw ].
      intro Heq; subst cs.
      match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - exact Hgw. (* PlayStart *)
  - (* PlayEnd *)
    apply graph_writes_graph_commit; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - (* PlaySpawn *)
    apply graph_writes_graph_commit; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - (* PlayJoin *)
    apply graph_writes_graph_merge; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - (* PlayLock *)
    apply graph_writes_graph_merge; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
  - (* PlayUnlock *)
    apply graph_writes_graph_commit; [ | exact Hgw ].
    intro Heq; subst cs.
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
Qed.

(* The last write of [x] is either still in [tm]'s delta (with value [vm]), or it
   has been flushed into a commit [cs] holding [x = vm] that is an ancestor of
   [tm]'s current commit. *)
Lemma last_write_committed_or_delta :
  forall log s0 D TC G LC VC CH m tm x vm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    ((x \indom (D[tm]) /\ (D[tm])[x] = vm) /\
       (forall g eg, m <= g -> LibList.Nth g log eg -> get_thread eg = tm ->
                     ~ is_commit_event eg)) \/
    (exists f ef cs,
       m <= f /\ LibList.Nth f log ef /\ get_thread ef = tm /\ is_commit_event ef /\
       LibList.Nth f CH cs /\ graph_writes G cs x vm /\
       (forall g eg, m <= g -> g < f -> LibList.Nth g log eg -> get_thread eg = tm ->
                     ~ is_commit_event eg)).
Proof.
  introv Hwf Hplay. gen m tm x vm.
  inductions Hplay; introv HNlog Hlast.
  - inverts HNlog.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + (* write in the prefix *)
      forwards Hib: Nth_inbound HN0.
      asserts Hlast0: (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m).
      { introv HNk. applys Hlast. applys Nth_app_l HNk. }
      forwards IHdisj:
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0 Hlast0).
      destruct IHdisj as
        [((Hidom & Hival) & Hnc) |
         (f & ef & cs & Hmf & HNf & Hgf & Hcf & HNchf & Hcsw & Hncf)].
      2:{ (* RIGHT: the flush already happened in the prefix; lift across the step *)
        right. exists f ef cs. splits.
        - exact Hmf.
        - applys Nth_app_l HNf.
        - exact Hgf.
        - exact Hcf.
        - applys Nth_app_l HNchf.
        - applys play_event_graph_writes_mono H Hcsw.
        - introv Hg Hgflt HNg Hgg.
          forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
          + applys Hncf Hg Hgflt HNg0 Hgg.
          + forwards Hfin: Nth_inbound HNf. nat_math. }
      (* LEFT: [x] still in [tm]'s delta in the prefix; maintain the no-commit clause *)
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        inverts H.
      * (* spawn s1 s2: flush of the spawner s1 *)
        forwards Hns2: spawned_thread_no_prior_event Hwf HN0. cbn [get_thread] in Hns2.
        destruct (classic (s1 = tm)) as [Hs1 | Hs1].
        -- subst s1. right. exists (length log) (event_spawn tm s2).
           eexists. splits.
           ++ nat_math.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ reflexivity.
           ++ simpl; exact I.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ cbn [get_thread]. rewrite read_update_neq; [ | congruence ].
              rewrite read_update_same.
              applys graph_writes_graph_commit_new.
              match goal with Hbd : binds _ tm ?dstg |- binds ?dstg _ _ =>
                forwards Hdeq: read_of_binds Hbd; rewrite <- Hdeq end.
              applys binds_of_indom_read Hidom Hival; typeclass.
           ++ introv Hg Hgflt HNg Hgg.
              forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { nat_math. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ | congruence ].
                 rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ | congruence ].
                 rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg.
              forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst eg; simpls; congruence. }
      * (* join *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* read, non-volatile *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* read, volatile: [PlayReadVolatile] only pulls (merges), it never
           touches [D] and (like every read) it is never a commit event *)
        left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* write wt wj ww, non-volatile *)
        destruct (classic (wt = tm)) as [Hwt | Hwt].
        -- subst wt.
           destruct (classic (wj = x)) as [Hwj | Hwj].
           ++ subst wj. exfalso.
              asserts HNE: (LibList.Nth (length log) (log & event_write tm x ww) (event_write tm x ww)).
              { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
              forwards Hle: Hlast HNE. nat_math.
           ++ left; split.
              ** match goal with Hbd : binds _ tm ?dstg |- _ =>
                   forwards Hdeq: read_of_binds Hbd end.
                 split.
                 --- rewrite read_update_same.
                     apply indom_update_of_indom;
                       (typeclass || (rewrite <- Hdeq; exact Hidom)).
                 --- rewrite read_update_same.
                     rewrite read_update_neq; [ | congruence ].
                     rewrite <- Hdeq. exact Hival.
              ** introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
                 { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst eg; simpls; congruence. }
      * (* write wt wj ww, volatile: [PlayWriteVolatile] FLUSHES [D[wt]]
           entirely (not just a local update at [wj]), matching
           [spawn]/[unlock]/[end]'s flush pattern rather than the local-update
           pattern just above; it also IS a commit event (for [wt]). *)
        destruct (classic (wt = tm)) as [Hwt | Hwt].
        -- subst wt.
           destruct (classic (wj = x)) as [Hwj | Hwj].
           ++ subst wj. exfalso.
              asserts HNE: (LibList.Nth (length log) (log & event_write tm x ww) (event_write tm x ww)).
              { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
              forwards Hle: Hlast HNE. nat_math.
           ++ right. exists (length log) (event_write tm wj ww).
              eexists. splits.
              ** nat_math.
              ** applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
              ** reflexivity.
              ** simpl; assumption.
              ** applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
              ** cbn [get_thread]. rewrite read_update_same.
                 applys graph_writes_graph_commit_new.
                 apply binds_update_neq; [ congruence | ].
                 match goal with Hbd : binds _ tm ?dstg |- binds ?dstg _ _ =>
                   forwards Hdeq: read_of_binds Hbd; rewrite <- Hdeq end.
                 applys binds_of_indom_read Hidom Hival; typeclass.
              ** introv Hg Hgflt HNg Hgg.
                 forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
                 { applys Hnc Hg HNg0 Hgg. } { nat_math. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst eg; simpls; congruence. }
      * (* lock (PlayLock) *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* unlock ut ul: flush of ut *)
        destruct (classic (ut = tm)) as [Hut | Hut].
        -- subst ut. right. exists (length log) (event_unlock tm ul).
           eexists. splits.
           ++ nat_math.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ reflexivity.
           ++ simpl; exact I.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ cbn [get_thread]. rewrite read_update_same.
              applys graph_writes_graph_commit_new.
              match goal with Hbd : binds _ tm ?dstg |- binds ?dstg _ _ =>
                forwards Hdeq: read_of_binds Hbd; rewrite <- Hdeq end.
              applys binds_of_indom_read Hidom Hival; typeclass.
           ++ introv Hg Hgflt HNg Hgg.
              forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { nat_math. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst eg; simpls; congruence. }
      * (* start *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* end ett: flush of ett *)
        destruct (classic (ett = tm)) as [Het | Het].
        -- subst ett. right. exists (length log) (event_end tm).
           eexists. splits.
           ++ nat_math.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ reflexivity.
           ++ simpl; exact I.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ cbn [get_thread]. rewrite read_update_same.
              applys graph_writes_graph_commit_new.
              match goal with Hbd : binds _ tm ?dstg |- binds ?dstg _ _ =>
                forwards Hdeq: read_of_binds Hbd; rewrite <- Hdeq end.
              applys binds_of_indom_read Hidom Hival; typeclass.
           ++ introv Hg Hgflt HNg Hgg.
              forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { nat_math. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst eg; simpls; congruence. }
    + (* the write is the last (appended) event *)
      subst E. inverts H.
      * (* PlayWrite, non-volatile: still pending, uncommitted, in the delta *)
        left. split.
        -- split.
           ++ rewrite read_update_same. apply indom_update_same; typeclass.
           ++ rewrite read_update_same, read_update_same. reflexivity.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { forwards Hglt: Nth_inbound HNg0. nat_math. }
           { subst eg; simpl; auto. }
      * (* PlayWriteVolatile: immediately flushed/committed by this very event *)
        right. exists (length log) (event_write tm x vm).
        eexists. splits.
        -- nat_math.
        -- applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
        -- reflexivity.
        -- simpl; assumption.
        -- applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
        -- cbn [get_thread]. rewrite read_update_same.
           applys graph_writes_graph_commit_new. apply binds_update_same.
        -- introv Hg Hgflt HNg Hgg.
           forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
           { forwards Hglt: Nth_inbound HNg0. nat_math. }
           { nat_math. }
Qed.

(* When [t]'s event [m] happens-before an event [n] of another thread, there is a
   commit event [f] of [t] (at index >= m) that itself happens-before [n] -- the
   flush that carries the value across threads. Refines [hb_preserves_thread]:
   every cross-thread base edge has a commit-event source, which is the [f]. *)
Lemma hb_cross_thread_flush :
  forall log m n,
    hb log m n ->
    forall t em en,
      LibList.Nth m log em -> get_thread em = t ->
      LibList.Nth n log en -> get_thread en <> t ->
      exists f ef, m <= f /\ LibList.Nth f log ef /\ get_thread ef = t /\
                   is_commit_event ef /\ hb log f n.
Proof.
  introv Hhb. induction Hhb as
    [ p q e1 e2 HN1 HN2 Heq Hlt
    | q p lt1 lt2 ll HNsrc HNtgt Hlt
    | p q st1 st2 HNsrc HNtgt Hlt
    | p q jt1 jt2 HNsrc HNtgt Hlt
    | p q vt1 vt2 vx vv vv' Hxvol HNw HNr Hlt
    | p q k Hpk IHpk Hkq IHkq ];
    introv Hm Hgt Hn Hgne.
  - (* HbPo: source and target are the same thread, contradicting [get_thread en <> t] *)
    forwards Heq1: Nth_functional Hm HN1. forwards Heq2: Nth_functional Hn HN2.
    exfalso. apply Hgne. congruence.
  - (* HbLock: the unlock at [p] is a commit event of [t] *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_unlock lt1 ll). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbLock HNsrc HNtgt Hlt.
  - (* HbSpawn: the spawn at [p] is a commit event of [t] *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_spawn st1 st2). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbSpawn HNsrc HNtgt Hlt.
  - (* HbJoin: the end at [p] is a commit event of [t] *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_end jt2). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbJoin HNsrc HNtgt Hlt.
  - (* HbVolatile: the write at [p] is a commit event of [t] (it writes a
       volatile, so [is_commit_event] holds) *)
    forwards Heq: Nth_functional Hm HNw. subst em.
    exists p (event_write vt1 vx vv). splits.
    + nat_math. + exact HNw. + simpls; exact Hgt. + simpl; exact Hxvol.
    + applys HbVolatile Hxvol HNw HNr Hlt.
  - (* HbTrans through [k] *)
    forwards (ek & HNk): hb_Nth_r Hpk.
    forwards Hltpk: hb_lt Hpk.
    destruct (classic (get_thread ek = t)) as [Hgek | Hgek].
    + forwards (f & ef & Hkf & HNf & Hgf & Hcf & Hhbf): IHkq HNk Hgek Hn Hgne.
      exists f ef. splits; try assumption. nat_math.
    + forwards (f & ef & Hpf & HNf & Hgf & Hcf & Hhbf): IHpk Hm Hgt HNk Hgek.
      exists f ef. splits; try assumption. applys HbTrans Hhbf Hkq.
Qed.

(* Graph well-formedness maintained by [play_log] from the empty state: edge
   endpoints and the threads'/locks' commit pointers all live in the graph's
   domain.  Enough to run the "fresh commit is a leaf" argument without the full
   [wf_graph] (which would also need acyclicity). *)
Definition play_graph_wf (TC : commits) (G : graph) (LC : lcommits) (VC : volatiles) : Prop :=
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) /\
  (forall t, t \indom TC -> graph_indom G (TC[t])) /\
  (forall l, l \indom LC -> graph_indom G (LC[l])) /\
  (forall x, x \indom VC -> graph_indom G (VC[x])) /\
  graph_indom G root_commit.

(* Conversion-tolerant membership inversion for an updated pointer map (the
   [Inhab] instance in [indom_update_eq] makes a bare [rewrite] miss the subterm). *)
Lemma indom_update_cases :
  forall (M : map nat commit) x j v,
    j \indom (M[x := v]) -> j = x \/ j \indom M.
Proof. introv H. applys indom_update_inv H; typeclass. Qed.

Lemma play_log_graph_wf :
  forall log D TC G LC VC CH,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    play_graph_wf TC G LC VC.
Proof.
  introv Hplay. inductions Hplay.
  - splits.
    + introv He. simpls. rew_set in He. false.
    + introv Ht. rew_dom. rew_set in Ht. branches;
        [ forwards*: indom_empty_inv|].
      subst. rewrite read_update_same.
      applys* graph_root_indom_same.
    + introv Hl. false. applys indom_empty_inv Hl.
    + introv Hx. false. applys indom_empty_inv Hx.
    + applys* graph_root_indom_same.
  - forwards* Hwf: IHHplay. destruct Hwf as (Hedge & HTC & HLC & HVC & Hroot).
    rename H into Hpe.
    match goal with Hp : play_log _ _ (_, _, ?GG, _, _) _ |- _ => destruct GG as (C & P) end.
    inverts Hpe; try (splits; assumption).
    + (* PlayReadVolatile t0 x: graph_merge (C,P) (vc_read VC x) c c',
         TC[t0:=c'] (VC unchanged) *)
      asserts HVCxindom: (graph_indom (C, P) (vc_read VC x)).
      { unfold vc_read. destruct (classic (x \indom VC)) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HVC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | [He | He]].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC end).
           ++ apply indom_update_same; typeclass.
        -- inverts He. split.
           ++ apply indom_update_of_indom; (typeclass || exact HVCxindom).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlayWriteVolatile t0 x: two layers -- graph_merge (C,P) (vc_read VC' x) c c'
         then graph_commit _ c' c'' d[x:=v0]; TC[t0:=c''], VC'[x:=c''] *)
      asserts HVCxindom: (graph_indom (C, P) (vc_read VC' x)).
      { unfold vc_read. destruct (classic (x \indom VC')) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HVC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | [He | [He | He]]].
        -- (* (c', c'') : the outer commit's own new edge *)
           inverts He. split.
           ++ apply indom_update_of_indom; (typeclass || apply indom_update_same; typeclass).
           ++ apply indom_update_same; typeclass.
        -- (* (c, c') : the inner merge's "own" edge *)
           inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 (apply indom_update_of_indom;
                  (typeclass ||
                   match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                     applys binds_graph_indom Hb HTC end))).
           ++ apply indom_update_of_indom; (typeclass || apply indom_update_same; typeclass).
        -- (* (vc_read VC' x, c') : the inner merge's "other" edge *)
           inverts He. split.
           ++ apply indom_update_of_indom; (typeclass || (apply indom_update_of_indom; (typeclass || exact HVCxindom))).
           ++ apply indom_update_of_indom; (typeclass || apply indom_update_same; typeclass).
        -- (* old edge *)
           forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || (apply indom_update_of_indom; (typeclass || assumption)))).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass ||
              (apply indom_update_of_indom;
               (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])))).
      * introv Hl. apply indom_update_of_indom;
          (typeclass || (apply indom_update_of_indom; (typeclass || applys HLC Hl))).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = x)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass ||
              (apply indom_update_of_indom;
               (typeclass || (applys HVC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])))).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlayEnd t0: graph_commit (C,P) c c' d, TC[t0:=c'] *)
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | He].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC end).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlaySpawn t1 t2: graph_commit, TC[t1:=c'][t2:=c'] *)
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | He].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC end).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj.
        destruct (classic (j = t2)) as [-> | Hne2].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           destruct (classic (j = t1)) as [-> | Hne1].
           ++ rewrite read_update_same. apply indom_update_same; typeclass.
           ++ rewrite read_update_neq; [ | congruence ].
              forwards H1: indom_update_cases Hj. destruct H1 as [Hc1 | H1]; [ congruence | ].
              forwards H2: indom_update_cases H1. destruct H2 as [Hc2 | H2]; [ congruence | ].
              apply indom_update_of_indom; (typeclass || applys HTC H2).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlayJoin t1 t2: graph_merge (C,P) c2 c1 c', TC[t1:=c'] *)
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | [He | He]].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC || applys binds_graph_indom Hb HLC end).
           ++ apply indom_update_same; typeclass.
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC || applys binds_graph_indom Hb HLC end).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t1)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlayLock t l0: graph_merge (C,P) c1 (lc_read LC l0) c', TC[t:=c'] (LC unchanged) *)
      asserts HLClindom: (graph_indom (C, P) (lc_read LC l0)).
      { unfold lc_read. destruct (classic (l0 \indom LC)) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HLC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | [He | He]].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC end).
           ++ apply indom_update_same; typeclass.
        -- inverts He. split.
           ++ apply indom_update_of_indom; (typeclass || exact HLClindom).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
    + (* PlayUnlock t l: graph_commit, TC[t:=c'], LC[l:=c'] *)
      splits.
      * introv He. simpls. rew_set in He. destruct He as [He | He].
        -- inverts He. split.
           ++ apply indom_update_of_indom;
                (typeclass ||
                 match goal with Hb : binds _ _ ?cc |- ?cc \indom _ =>
                   applys binds_graph_indom Hb HTC end).
           ++ apply indom_update_same; typeclass.
        -- forwards (Ha & Hb): Hedge He.
           split; (apply indom_update_of_indom; (typeclass || assumption)).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * intros j Hj. forwards Hcase: indom_update_cases Hj.
        match goal with |- graph_indom _ (_[?key := _][_]) =>
          destruct (classic (j = key)) as [-> | Hne] end.
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HLC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hx. apply indom_update_of_indom; (typeclass || applys HVC Hx).
      * unfolds graph_indom. rew_dom. rew_set. auto.
  Unshelve. all: typeclass.
Qed.

(* [root_commit] is never the target of a graph edge: it is present from the
   very first (empty) graph, and every edge ever added targets a commit that
   was [commit_fresh] (hence not yet [root_commit], which is always indom)
   at the moment the edge was created. *)
Lemma root_commit_no_incoming_edge :
  forall log D TC G LC VC CH,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    forall a, ~ graph_edge G a root_commit.
Proof.
  introv Hplay. inductions Hplay; introv He.
  - unfolds graph_root, graph_edge. rew_set in He. false.
  - rename H into Hpe.
    forwards Hpgwf: play_log_graph_wf Hplay.
    destruct Hpgwf as (_ & _ & _ & _ & Hrootin).
    (* [root_commit] can never be a step's fresh commit (it is always
       indom, never [commit_fresh]), so it is never the target of a
       newly-added edge; old edges are ruled out by [IHHplay]. *)
    inverts Hpe.
    + (* PlayRead: [G] unchanged *) applys* IHHplay.
    + (* PlayReadVolatile: single merge *)
      destruct G' as (C0 & P0). unfolds graph_merge, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | [Heq | HeP]].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlayWrite: [G] unchanged *) applys* IHHplay.
    + (* PlayWriteVolatile: two layers (merge then commit) *)
      asserts Hrootin1: (graph_indom (graph_merge G' (vc_read VC' x) c c') root_commit).
      { destruct G' as (C0 & P0). unfolds graph_merge, graph_indom.
        apply indom_update_of_indom; (exact Hrootin || typeclass). }
      destruct G' as (C0 & P0). unfolds graph_merge, graph_commit, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | [Heq | [Heq | HeP]]].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin1].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlayStart: [G] unchanged *) applys* IHHplay.
    + (* PlayEnd *)
      destruct G' as (C0 & P0). unfolds graph_commit, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | HeP].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlaySpawn *)
      destruct G' as (C0 & P0). unfolds graph_commit, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | HeP].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlayJoin *)
      destruct G' as (C0 & P0). unfolds graph_merge, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | [Heq | HeP]].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlayLock *)
      destruct G' as (C0 & P0). unfolds graph_merge, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | [Heq | HeP]].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
    + (* PlayUnlock *)
      destruct G' as (C0 & P0). unfolds graph_commit, graph_edge. simpl in He. rew_set in He.
      destruct He as [Heq | HeP].
      * inverts Heq. false. applys commit_fresh_not_indom; [eassumption | exact Hrootin].
      * applys* IHHplay.
Qed.

(* A commit graph edge can never point into [root_commit], so ancestry into it
   collapses to reflexivity. *)
Lemma ancestor_into_root :
  forall log D TC G LC VC CH a,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    ancestor G a root_commit -> a = root_commit.
Proof.
  introv Hplay Hanc.
  asserts Hno: (forall a, ~ graph_edge G a root_commit).
  { applys root_commit_no_incoming_edge Hplay. }
  inductions Hanc.
  - reflexivity.
  - false. applys Hno H.
Qed.

(* [vc_read VC x] is always in the graph's domain: either [x] is stored
   ([HVC]) or the default [root_commit] applies ([Hroot]). Mirrors the
   [lc_read]/[LC] reasoning already inlined at each [PlayReadVolatile] /
   [PlayWriteVolatile] case above, packaged for reuse by callers outside this
   file (e.g. [BranchingEquiv.v]'s volatile step cases). *)
Lemma vc_read_graph_indom :
  forall D TC G LC VC CH log x,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    graph_indom G (vc_read VC x).
Proof.
  introv Hplay.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct Hpgwf as (_ & _ & _ & HVC & Hroot).
  unfold vc_read. destruct (classic (x \indom VC)) as [Hindom|Hnotin].
  - rewrite (read_default_indom Hindom). applys* HVC.
  - rewrite (read_default_notindom Hnotin). exact Hroot.
Qed.

(* Replaying a log preserves [wf_graph]: the initial graph is well formed
   ([init_graph_wf]) and every graph-changing event is a [graph_commit] /
   [graph_merge] whose new commit is fresh and whose parent(s) are already in the
   graph (the latter via [play_log_graph_wf] on the prefix). *)
Lemma play_log_wf_graph :
  forall log D TC G LC VC CH,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    wf_graph G.
Proof.
  introv Hplay. inductions Hplay.
  - apply init_graph_wf.
  - forwards* Hwf': IHHplay.
    forwards Hpgwf: play_log_graph_wf Hplay.
    destruct Hpgwf as (_ & HTC & HLC & HVC & Hroot).
    rename H into Hpe.
    match goal with Hp : play_log _ _ (_, _, ?GG, _, _) _ |- _ => destruct GG as (C & P) end.
    inverts Hpe; try assumption.
    + (* PlayReadVolatile: graph_merge (volatile parent from vc_read VC, thread parent from TC) *)
      asserts HVCxindom: (graph_indom (C, P) (vc_read VC x)).
      { unfold vc_read. destruct (classic (x \indom VC)) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HVC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      applys graph_merge_wf Hwf';
        [ assumption
        | exact HVCxindom
        | applys binds_graph_indom; [ eassumption | exact HTC ] ].
    + (* PlayWriteVolatile: graph_commit wrapping graph_merge *)
      asserts HVCxindom: (graph_indom (C, P) (vc_read VC' x)).
      { unfold vc_read. destruct (classic (x \indom VC')) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HVC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      asserts Hmwf: (wf_graph (graph_merge (C, P) (vc_read VC' x) c c')).
      { applys graph_merge_wf Hwf';
          [ assumption
          | exact HVCxindom
          | applys binds_graph_indom; [ eassumption | exact HTC ] ]. }
      applys graph_commit_wf Hmwf;
        [ assumption | apply* graph_merge_indom_same ].
    + (* PlayEnd: graph_commit *)
      applys graph_commit_wf Hwf';
        [ assumption | applys binds_graph_indom; [ eassumption | exact HTC ] ].
    + (* PlaySpawn: graph_commit *)
      applys graph_commit_wf Hwf';
        [ assumption | applys binds_graph_indom; [ eassumption | exact HTC ] ].
    + (* PlayJoin: graph_merge (both parents from TC) *)
      applys graph_merge_wf Hwf';
        [ assumption
        | applys binds_graph_indom; [ eassumption | exact HTC ]
        | applys binds_graph_indom; [ eassumption | exact HTC ] ].
    + (* PlayLock: graph_merge (lock parent from lc_read LC, thread parent from TC) *)
      asserts HLClindom: (graph_indom (C, P) (lc_read LC l0)).
      { unfold lc_read. destruct (classic (l0 \indom LC)) as [Hindom|Hnotin].
        - rewrite (read_default_indom Hindom). applys* HLC.
        - rewrite (read_default_notindom Hnotin). exact Hroot. }
      applys graph_merge_wf Hwf';
        [ assumption
        | exact HLClindom
        | applys binds_graph_indom; [ eassumption | exact HTC ] ].
    + (* PlayUnlock: graph_commit *)
      applys graph_commit_wf Hwf';
        [ assumption | applys binds_graph_indom; [ eassumption | exact HTC ] ].
Qed.

(* [describes] already pins down [wf_cfg]: the graph is the replay of the log
   (well formed by [play_log_wf_graph]) and every thread/lock commit pointer is
   [TC[t]]/[LC[l]], which [play_log_graph_wf] places in the graph. No [wf_log]
   needed. *)
Lemma describes_wf_cfg :
  forall log cfg,
    describes log cfg ->
    wf_cfg cfg.
Proof.
  introv Hdesc. destruct cfg as [((T & G) & L) V].
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & LC & VC & CH & Hplay & HdT & HdL & Hveq & HdomD & HdomTC & HdomLClk)).
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct Hpgwf as (_ & HTC & HLC & HVC & Hroot).
  splits.
  - applys play_log_wf_graph Hplay.
  - exact Hroot.
  - introv Hb.
    lets Hin: (indom_of_binds Hb).
    forwards (ts0 & e0 & Hb0): HdT Hin.
    forwards* Heq: binds_inj Hb Hb0. inverts Heq.
    applys HTC. applys HdomTC Hin.
  - introv Hb.
    lets Hin: (indom_of_binds Hb).
    forwards (ls0 & Hb0): HdL Hin.
    forwards* Heq: binds_inj Hb Hb0. inverts Heq.
    unfold lc_read. destruct (classic (l \indom LC)) as [Hindom|Hnotin].
    + rewrite (read_default_indom Hindom). applys* HLC.
    + rewrite (read_default_notindom Hnotin). exact Hroot.
  - introv Hb.
    rewrite <- Hveq in Hb.
    lets Hin: (indom_of_binds Hb).
    forwards HVCx: HVC Hin.
    forwards Heq: read_of_binds Hb.
    subst c. exact HVCx.
Qed.

(* Every graph x-writer [cx] is the commit produced by some flush at position [f']
   (so [cx = CH[f']], a commit event of its thread [tw']), and the flushed value
   came from an x-write at some earlier position [kw'] that was still uncommitted
   at [f'] -- no commit event of [tw'] occurs in [[kw', f')]. This is the inverse
   of [last_write_committed_or_delta]. *)
(* [kw' <= f'], not strictly [<]: for an ordinary write, the flush [f'] is a
   later, separate commit event, so [kw' < f']; but a *volatile* write is its
   own flush ([is_commit_event] holds directly on the write), so [kw' = f']. *)
Lemma graph_writes_flush :
  forall log D TC G LC VC CH cx x v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    graph_writes G cx x v ->
    exists f' ef' tw' kw',
      LibList.Nth f' CH cx /\ LibList.Nth f' log ef' /\ get_thread ef' = tw' /\
      is_commit_event ef' /\ kw' <= f' /\ LibList.Nth kw' log (event_write tw' x v) /\
      (forall p ep, kw' <= p -> p < f' -> LibList.Nth p log ep -> get_thread ep = tw' ->
                    ~ is_commit_event ep).
Proof.
  introv Hplay. gen cx x v. inductions Hplay; introv Hgw.
  - destruct Hgw as (dd & Hgb & Hbd). simpls.
    destruct (classic (cx = root_commit)).
    + subst.
      forwards Hbinds: binds_update_same_inv Hgb.
      subst.
      forwards* Heq: binds_empty_false Hbd. typeclass.
    + forwards~ Hbinds: binds_update_neq_inv Hgb.
      forwards* Heq: binds_empty_false Hbinds. typeclass.
  - rename H into Hpe.
    (* common tail: lift a prefix witness across the appended event [Ex]/commit [chx] *)
    assert (Hlift : forall (chx : commit) (Ex : event),
              (exists f' ef' tw' kw',
                 LibList.Nth f' CH cx /\ LibList.Nth f' log ef' /\ get_thread ef' = tw' /\
                 is_commit_event ef' /\ kw' <= f' /\ LibList.Nth kw' log (event_write tw' x v) /\
                 (forall p ep, kw' <= p -> p < f' -> LibList.Nth p log ep -> get_thread ep = tw' ->
                               ~ is_commit_event ep)) ->
              exists f' ef' tw' kw',
                LibList.Nth f' (CH & chx) cx /\
                LibList.Nth f' (log & Ex) ef' /\ get_thread ef' = tw' /\
                is_commit_event ef' /\ kw' <= f' /\
                LibList.Nth kw' (log & Ex) (event_write tw' x v) /\
                (forall p ep, kw' <= p -> p < f' -> LibList.Nth p (log & Ex) ep ->
                              get_thread ep = tw' -> ~ is_commit_event ep)).
    { clear Hgw. introv (f' & ef' & tw' & kw' & HNfCH0 & HNflog0 & Hgt0 & Hcom0 & Hkwlt0 & HNkw0 & Hcl0).
      exists f' ef' tw' kw'. splits.
      - applys Nth_app_l HNfCH0.
      - applys Nth_app_l HNflog0.
      - exact Hgt0.
      - exact Hcom0.
      - exact Hkwlt0.
      - applys Nth_app_l HNkw0.
      - introv Hp Hpf HNp Hgp.
        forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp.
        + applys Hcl0 Hp Hpf HNp0 Hgp.
        + forwards Hib: Nth_inbound HNflog0. nat_math. }
    inverts Hpe.
    1,3,5: (applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R).
    + (* PlayReadVolatile: graph_merge -- no diff, same as Join/Lock *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | applys Hlift; forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
    + (* PlayWriteVolatile: two layers -- graph_commit wrapping graph_merge, and
         the committed diff is [d[x0:=v0]] (folding in the just-written value),
         mirroring [graph_writes_log_write]'s [PlayWriteVolatile] case. *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc]
      end.
      { subst cx.
        forwards Hbdd: graph_writes_graph_commit_same Hgw.
        destruct (classic (x = x0)) as [Hxeq | Hxneq].
        - subst x0.
          forwards ->: binds_update_same_inv Hbdd.
          forwards Hlen: play_log_CH_length Hplay.
          exists (length log) (event_write t x v0) t (length log).
          splits.
          + cbn [get_thread]. rewrite read_update_same.
            apply Nth_app_r' with (m := 0).
            * apply Nth_zero.
            * rew_list; nat_math.
          + applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
          + reflexivity.
          + simpl; assumption.
          + nat_math.
          + applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
          + introv Hp Hpf HNp Hgp. forwards Hib: Nth_inbound HNp. nat_math.
        - forwards Hbdd': binds_update_neq_inv Hbdd Hxneq.
          lets HtD: (indom_of_binds H11).
          lets Hrd: (read_of_binds H11).
          rewrite <- Hrd in Hbdd'.
          forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hplay HtD Hbdd'.
          forwards Hlen: play_log_CH_length Hplay.
          forwards Hib': Nth_inbound HNm'.
          exists (length log) (event_write t x0 v0) t m'; splits;
            [ cbn [get_thread]; rewrite read_update_same;
              apply Nth_app_r' with (m := 0); [ apply Nth_zero | rew_list; nat_math ]
            | apply Nth_app_r' with (m := 0); [ apply Nth_zero | rew_list; nat_math ]
            | reflexivity
            | simpl; assumption
            | nat_math
            | applys Nth_app_l HNm'
            | introv Hp0 Hpf HNp0 Hgp;
              forwards [HNp1 | (HpN & _)]: Nth_last_inv HNp0;
              [ applys Hns' Hp0 HNp1 Hgp
              | forwards Hib2: Nth_inbound HNm'; nat_math ] ]. }
      { applys Hlift; forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
        destruct (classic (cx = c')) as [Hc2 | Hc2];
          [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw'
          | forwards Hgw'': graph_writes_graph_merge_inv Hc2 Hgw';
            forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]. }
    + (* PlayEnd: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            forwards Hlen: play_log_CH_length Hp;
            forwards Hib': Nth_inbound HNm';
            exists (length log) (event_end tt) tt m'; splits;
            [ cbn [get_thread]; rewrite read_update_same;
              applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | reflexivity
            | simpl; exact I
            | nat_math
            | applys Nth_app_l HNm'
            | introv Hp0 Hpf HNp Hgp;
              forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hns' Hp0 HNp0 Hgp | nat_math ] ]
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
    + (* PlaySpawn: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (lazymatch goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            forwards Hlen: play_log_CH_length Hp;
            forwards Hib': Nth_inbound HNm';
            exists (length log) (event_spawn t1 t2) t1 m'; splits;
            [ cbn [get_thread];
              destruct (classic (t1 = t2)) as [Heqt | Hnet];
              [ subst t2; rewrite read_update_same;
                applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
              | rewrite read_update_neq;
                [ rewrite read_update_same;
                  applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
                | congruence ] ]
            | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | reflexivity
            | simpl; exact I
            | nat_math
            | applys Nth_app_l HNm'
            | introv Hp0 Hpf HNp Hgp;
              forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hns' Hp0 HNp0 Hgp | nat_math ] ]
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
    + (* PlayJoin: graph_merge *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
    + (* PlayLock: graph_merge *)
      match type of Hgw with
      | graph_writes (graph_merge _ _ _ ?hh) _ _ _ =>
        destruct (classic (cx = hh)) as [Hc | Hc];
        [ subst cx; false; applys graph_writes_graph_merge_same_false Hgw
        | forwards Hgw': graph_writes_graph_merge_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
    + (* PlayUnlock: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _, _) _ |- _ =>
            lets HtD: (indom_of_binds HbD);
            lets Hrd: (read_of_binds HbD);
            rewrite <- Hrd in Hbdd;
            forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd;
            forwards Hlen: play_log_CH_length Hp;
            forwards Hib': Nth_inbound HNm';
            match goal with |- context[event_unlock ?a ?l] =>
              exists (length log) (event_unlock a l) a m' end; splits;
            [ cbn [get_thread]; rewrite read_update_same;
              applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | reflexivity
            | simpl; exact I
            | nat_math
            | applys Nth_app_l HNm'
            | introv Hp0 Hpf HNp Hgp;
              forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hns' Hp0 HNp0 Hgp | nat_math ] ]
           end)
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
Qed.

(* The graph domain only grows along a play step. *)
Lemma play_event_graph_indom_mono :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' c,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    graph_indom G' c -> graph_indom G'' c.
Proof.
  introv Hpe Hin. inverts Hpe; try exact Hin;
    try (destruct G' as (C0 & P0); simpls; apply indom_update_of_indom; (exact Hin || typeclass)).
  (* PlayWriteVolatile: two layers (merge then commit), so indom monotonicity
     applies twice. *)
  destruct G' as (C0 & P0). simpls.
  apply indom_update_of_indom;
    (typeclass || (apply indom_update_of_indom; (exact Hin || typeclass))).
Qed.

(* The commit produced by a commit event is fresh in the prefix graph and present
   in the new graph. *)
Lemma play_event_commit_new :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'',
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    is_commit_event E ->
    commit_fresh G' (TC''[get_thread E]) /\ graph_indom G'' (TC''[get_thread E]).
Proof.
  introv Hpe Hce. inverts Hpe; cbn [is_commit_event get_thread] in *; try contradiction.
  - (* PlayWriteVolatile: [commit_fresh] w.r.t. the pre-merge graph [G'] follows
       contravariantly from freshness w.r.t. the (larger) merge graph. *)
    destruct G' as (C0 & P0). simpls.
    rewrite read_update_same. split.
    + intro Hin. apply H14. apply* indom_update_of_indom. typeclass.
    + apply indom_update_same; typeclass.
  - destruct G' as (C0 & P0).
    rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - destruct G' as (C0 & P0).
    destruct (classic (t1 = t2)) as [Heqt | Hnet].
    + subst t2. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
    + rewrite read_update_neq; [ | congruence ]. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - destruct G' as (C0 & P0).
    rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
Qed.

(* Edge-well-formedness of a merge/commit result, given only edge-wf of the
   base graph plus the new node's parent(s) already being in its domain (not
   the full [wf_graph], which also needs finiteness/antisymmetry -- unneeded
   here). Extracted from the edge-wf conjunct of [graph_merge_wf]/
   [graph_commit_wf]. *)
Lemma graph_merge_edge_wf :
  forall G p1 p2 h,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    graph_indom G p1 -> graph_indom G p2 ->
    (forall a b, graph_edge (graph_merge G p1 p2 h) a b ->
                 graph_indom (graph_merge G p1 p2 h) a /\ graph_indom (graph_merge G p1 p2 h) b).
Proof.
  introv Hedge_wf Hin1 Hin2. destruct G as (C & P). introv He.
  unfolds graph_merge, graph_edge, graph_indom.
  rew_set in He. destruct He as [Heq | [Heq | HeP]].
  - inverts Heq. split.
    + applys~ indom_update_of_indom. typeclass.
    + applys indom_update_same. typeclass.
  - inverts Heq. split.
    + applys~ indom_update_of_indom. typeclass.
    + applys indom_update_same. typeclass.
  - forwards (Ha & Hb): Hedge_wf HeP.
    split; applys~ indom_update_of_indom; typeclass.
Qed.

(* Ancestry into an old (prefix-domain) commit is unaffected by the freshly
   created commit, which is a sink: invert it back to the prefix graph. The
   extra [TC'/VC'-indom] and root-indom premises are only needed for
   [PlayWriteVolatile], to show the intermediate pull-merge's own parents are
   already in [G'] (so its edge-wf can be established, to invert *its* fresh
   commit as a second sink). *)
Lemma play_event_ancestor_inv :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' a b,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    (forall x y, graph_edge G' x y -> graph_indom G' x /\ graph_indom G' y) ->
    (forall t, t \indom TC' -> graph_indom G' (TC'[t])) ->
    (forall x, x \indom VC' -> graph_indom G' (VC'[x])) ->
    graph_indom G' root_commit ->
    graph_indom G' b ->
    ancestor G'' a b ->
    ancestor G' a b.
Proof.
  introv Hpe Hedge HTCin HVCin Hroot Hbdom Hanc. inverts Hpe.
  - (* PlayRead: G unchanged *) exact Hanc.
  - (* PlayReadVolatile: single merge *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_merge_inv Hsink Hbne Hanc.
  - (* PlayWrite: G unchanged *) exact Hanc.
  - (* PlayWriteVolatile: two layers -- invert the outer commit (a sink into
       the merge graph) then the inner merge (a sink into G') *)
    asserts Hp1indom: (graph_indom G' (vc_read VC' x)).
    { unfold vc_read. destruct (classic (x \indom VC')) as [Hindom|Hnotin].
      - rewrite (read_default_indom Hindom). applys* HVCin.
      - rewrite (read_default_notindom Hnotin). exact Hroot. }
    match goal with H : binds TC' t c |- _ => rename H into Hbc end.
    asserts Hp2indom: (graph_indom G' c).
    { rewrite <- (read_of_binds Hbc). exact (HTCin t (indom_of_binds Hbc)). }
    asserts Hmedge: (forall p q, graph_edge (graph_merge G' (vc_read VC' x) c c') p q ->
                                  graph_indom (graph_merge G' (vc_read VC' x) c c') p /\
                                  graph_indom (graph_merge G' (vc_read VC' x) c c') q).
    { applys* graph_merge_edge_wf. }
    asserts Hbdom': (graph_indom (graph_merge G' (vc_read VC' x) c c') b).
    { applys* graph_merge_indom. }
    asserts Hsink2: (forall z, ancestor (graph_merge G' (vc_read VC' x) c c') c'' z -> z = c'').
    { applys* commit_fresh_sink Hmedge. }
    asserts Hbne2: (b <> c'').
    { intro Heq. subst b. applys* commit_fresh_not_indom Hbdom'. }
    forwards Hanc': ancestor_graph_commit_inv Hsink2 Hbne2 Hanc.
    asserts Hsink1: (forall z, ancestor G' c' z -> z = c').
    { applys* commit_fresh_sink Hedge. }
    asserts Hbne1: (b <> c').
    { intro Heq. subst b. applys* commit_fresh_not_indom Hbdom. }
    applys ancestor_graph_merge_inv Hsink1 Hbne1 Hanc'.
  - (* PlayStart: G unchanged *) exact Hanc.
  - (* PlayEnd *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_commit_inv Hsink Hbne Hanc.
  - (* PlaySpawn *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_commit_inv Hsink Hbne Hanc.
  - (* PlayJoin *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_merge_inv Hsink Hbne Hanc.
  - (* PlayLock *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_merge_inv Hsink Hbne Hanc.
  - (* PlayUnlock *)
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end.
    applys ancestor_graph_commit_inv Hsink Hbne Hanc.
Qed.

(* The commit recorded for a commit event lives in the graph domain. *)
Lemma CH_commit_event_indom :
  forall log D TC G LC VC CH k c e,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth k CH c -> LibList.Nth k log e -> is_commit_event e -> graph_indom G c.
Proof.
  introv Hplay. gen k c e. inductions Hplay; introv HNch HNlog Hce.
  - forwards*: Nth_nil_inv HNch.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards [HNch0 | (HkN & Hcx)]: Nth_last_inv HNch.
    + forwards [HNlog0 | (HkN' & HeE)]: Nth_last_inv HNlog.
      * forwards* Hin: IHHplay HNch0 HNlog0 Hce.
        applys play_event_graph_indom_mono Hpe Hin.
      * forwards Hib: Nth_inbound HNch0. nat_math.
    + forwards [HNlog0 | (HkN' & HeE)]: Nth_last_inv HNlog.
      * forwards Hib: Nth_inbound HNlog0. nat_math.
      * subst e. forwards (Hf & Hin): play_event_commit_new Hpe Hce.
        rewrite <- Hcx. exact Hin.
Qed.

(* Graph edges follow creation order, so a proper graph-descendant of a commit
   born at a commit event [ka] is itself born strictly later. *)
Lemma ancestor_creation_order :
  forall log D TC G LC VC CH a b ka kb ea eb,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth ka CH a -> LibList.Nth ka log ea -> is_commit_event ea ->
    LibList.Nth kb CH b -> LibList.Nth kb log eb -> is_commit_event eb ->
    ancestor G a b -> a <> b ->
    ka < kb.
Proof.
  introv Hplay. gen a b ka kb ea eb.
  inductions Hplay; introv HNcha HNloga Hcea HNchb HNlogb Hceb Hanc Hneq.
  - forwards*: Nth_nil_inv HNcha.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards Hpgwf: play_log_graph_wf Hplay.
    destruct Hpgwf as (Hedge & HTCin & _ & HVCin & Hrootin).
    forwards [HNchb0 | (HkbN & Hcxb)]: Nth_last_inv HNchb.
    + (* b is an old commit, in the prefix graph *)
      forwards [HNlogb0 | (HkbN' & HeEb)]: Nth_last_inv HNlogb.
      2:{ forwards Hib: Nth_inbound HNchb0. nat_math. }
      forwards Hbdom: CH_commit_event_indom Hplay HNchb0 HNlogb0 Hceb.
      forwards Hanc': (>> play_event_ancestor_inv Hpe Hedge HTCin HVCin Hrootin Hbdom Hanc).
      forwards Hdisj: ancestor_src_indom Hedge Hanc'.
      destruct Hdisj as [Hain | Haeq]; [ | exfalso; applys Hneq Haeq ].
      forwards Hca: Nth_last_inv HNcha.
      destruct Hca as [HNcha0 | (HkaN & Hcxa)].
      2:{ (* a would be the fresh commit, but it is in the prefix domain *)
          forwards Hla: Nth_last_inv HNloga.
          destruct Hla as [HNloga0 | (HkaN'' & HeEa)].
          { forwards Hib: Nth_inbound HNloga0. nat_math. }
          subst ea. forwards (Hfa & _): play_event_commit_new Hpe Hcea.
          rewrite Hcxa in Hfa. exfalso. applys commit_fresh_not_indom Hfa Hain. }
      forwards Hla: Nth_last_inv HNloga.
      destruct Hla as [HNloga0 | (HkaN'' & HeEa)].
      2:{ forwards Hib: Nth_inbound HNcha0. nat_math. }
      forwards* Hlt: (>> IHHplay HNcha0 HNloga0 Hcea HNchb0 HNlogb0 Hceb Hanc' Hneq).
    + (* b is the freshly created commit: kb = length CH *)
      destruct (classic (ka = kb)) as [Heqk | Hkn].
      * rewrite Heqk in HNcha. forwards Heqab: Nth_functional HNcha HNchb.
        exfalso. applys Hneq Heqab.
      * forwards Hib: Nth_inbound HNcha. rew_list in Hib. nat_math.
Qed.

(* Maximality: the commit [cs = CH[f]] of [tm]'s flush [f] of the LAST x-write is
   the maximal x-writer in the graph -- no strict graph-descendant of [cs] writes
   [x]. *)
Lemma last_write_maximal :
  forall log D TC G LC VC CH m tm x vm f ef cs,
    conflict_free log ->
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    LibList.Nth f log ef -> get_thread ef = tm -> is_commit_event ef -> m <= f ->
    LibList.Nth f CH cs ->
    (forall g eg, m <= g -> g < f -> LibList.Nth g log eg -> get_thread eg = tm ->
                  ~ is_commit_event eg) ->
    graph_writes G cs x vm ->
    forall c' v', graph_writes G c' x v' -> ancestor G cs c' -> c' = cs.
Proof.
  intros log D TC G LC VC CH m tm x vm f ef cs.
  intros Hcf Hwf Hplay HNm Hlast HNf Hgf Hcfe Hmf HNchf Hncf Hcsw c' v' Hc'w Hanc.
  destruct (classic (c' = cs)) as [Heq | Hne]; [ exact Heq | exfalso ].
  forwards (f' & ef' & tw' & kw' & HNfCH & HNflog & Hgtf' & Hcef' & Hkwlt & HNkw & Hncl):
    graph_writes_flush Hplay Hc'w.
  forwards Hkwm: Hlast HNkw.
  asserts Hne2: (cs <> c'). { intros HH. apply Hne. symmetry. exact HH. }
  forwards Hflt: (>> ancestor_creation_order Hplay HNchf HNf Hcfe HNfCH HNflog Hcef' Hanc Hne2).
  destruct (classic (tw' = tm)) as [Htw | Htw].
  - (* same thread: [f] is a [tm]-commit strictly inside [[kw', f')] *)
    asserts Hni: (~ is_commit_event ef).
    { applys Hncl f ef; [ nat_math | exact Hflt | exact HNf | (rewrite Htw; exact Hgf) ]. }
    exact (Hni Hcfe).
  - (* other thread: a crossing flush of [tw'] sits inside [[kw', f')] *)
    asserts Hkwltm: (kw' < m).
    { destruct (classic (kw' = m)) as [He | Hlt].
      - subst kw'. forwards Heqw: Nth_functional HNkw HNm. inverts Heqw. false.
      - nat_math. }
    asserts Hacc: (accesses_variable x (event_write tm x vm)). { simpl. reflexivity. }
    forwards Hhb: (>> Hcf HNkw HNm Hacc Hkwltm).
    asserts Hgtw: (get_thread (event_write tw' x v') = tw'). { reflexivity. }
    asserts Hgtmne: (get_thread (event_write tm x vm) <> tw'). { simpl. auto. }
    forwards (f'' & ef'' & Hkwf'' & HNf'' & Hgf'' & Hcef'' & Hhbf''):
      (>> hb_cross_thread_flush Hhb HNkw Hgtw HNm Hgtmne).
    forwards Hf''lt: hb_lt Hhbf''.
    asserts Hni: (~ is_commit_event ef'').
    { applys Hncl f'' ef''; [ exact Hkwf'' | nat_math | exact HNf'' | exact Hgf'' ]. }
    exact (Hni Hcef'').
Qed.

(* Existence + maximality: the last write of [x] is visible as the latest value at
   [n]'s thread's commit. [x \notindom D[tm]] gives the committed flush [cs = CH[f]]
   (via [last_write_committed_or_delta]); its ancestry to [TC[get_thread en]] uses
   [hb_cross_thread_flush] for the cross-thread case; its maximality is
   [last_write_maximal]. *)
Lemma last_write_visible_commit :
  forall log D TC G LC VC CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hcf Hplay HNm Hlast Hndom HNn Hhb.
  forwards [((Hidom & _) & _) |
            (f & ef & cs & Hmf & HNf & Hgf & Hcfe & HNchf & Hcsw & Hncf)]:
    (>> last_write_committed_or_delta Hwf Hplay HNm Hlast).
  - (* still in the delta: contradicts [x \notindom D[tm]] *)
    false. applys Hndom Hidom.
  - (* committed witness [cs = CH[f]] *)
    exists cs. splits.
    + exact Hcsw.
    + (* ancestor cs (TC[get_thread en]) *)
      forwards Hcsanc: CH_ancestor_TC Hwf Hplay HNf Hgf HNchf.
      destruct (classic (get_thread en = tm)) as [Hgt | Hgt].
      * rewrite Hgt. exact Hcsanc.
      * (* cross-thread: place the flush on the hb chain to [n] *)
        forwards (f' & ef' & Hmf' & HNf' & Hgf' & Hcf' & Hhbf'):
          (>> hb_cross_thread_flush Hhb HNm
              (eq_refl : get_thread (event_write tm x vm) = tm) HNn Hgt).
        asserts Hff': (f <= f').
        { destruct (classic (f <= f')) as [Hle | Hgt2]; auto. exfalso.
          asserts Hlt: (f' < f). { nat_math. }
          forwards Hcon: Hncf Hmf' Hlt HNf' Hgf'. apply Hcon. exact Hcf'. }
        asserts Hhbfn: (hb log f n).
        { destruct (classic (f = f')) as [Hfe | Hfne].
          - subst f'. exact Hhbf'.
          - apply HbTrans with (k := f').
            + applys* HbPo HNf HNf'.
            + exact Hhbf'. }
        forwards Hnlt: Nth_inbound HNn.
        forwards Hlench: play_log_CH_length Hplay.
        asserts Hnch: (n < length CH). { rewrite Hlench. exact Hnlt. }
        forwards (cn & HNchn): Nth_inbound_inv Hnch.
        forwards Hanc1: hb_pointer_ancestor Hwf Hplay Hhbfn HNchf HNchn.
        forwards Hanc2:
          CH_ancestor_TC Hwf Hplay HNn (eq_refl : get_thread en = get_thread en) HNchn.
        applys ancestor_trans Hanc1 Hanc2.
    + (* maximality *)
      introv Hc'w Hanc1 Hanc2.
      assert (Hmax: forall c'' v'', graph_writes G c'' x v'' -> ancestor G cs c'' -> c'' = cs).
      { applys (>> last_write_maximal Hcf Hwf Hplay HNm Hlast HNf Hgf Hcfe Hmf
                   HNchf Hncf Hcsw). }
      applys Hmax Hc'w Hanc1.
Qed.

Lemma hb_last_write_visible :
  forall log D TC G LC VC CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hcf Hplay HNm Hlast Hndom HNn Hhb.
  applys (>> last_write_visible_commit Hwf Hcf Hplay HNm Hlast Hndom HNn Hhb).
Qed.

(* [is_latest_value] guarantees a committed x-write exists, hence the x-write
   filter of the log is non-empty. *)
Lemma is_latest_value_log_write :
  forall log D TC G LC VC CH c x v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    is_latest_value G c x v ->
    exists lw tw vw,
      LibList.filter (fun e => writes_variable x e) log = lw & event_write tw x vw.
Proof.
  introv Hplay Hval.
  destruct Hval as (c' & Hgw & _).
  forwards (tw & m & HN): graph_writes_log_write Hplay Hgw.
  asserts Hmemf:
    (mem (event_write tw x v) (LibList.filter (fun e => writes_variable x e) log)).
  { applys mem_filter; [ applys Nth_mem HN | reflexivity ]. }
  destruct (last_case (LibList.filter (fun e => writes_variable x e) log))
    as [Hnil | (e & lw & Hsnoc)].
  - rewrite Hnil, mem_nil_eq in Hmemf. destruct Hmemf.
  - asserts Hmx: (mem e (LibList.filter (fun e => writes_variable x e) log)).
    { rewrite Hsnoc, mem_last_eq. right. reflexivity. }
    forwards (Hmemx & Hwx): mem_filter_inv Hmx.
    destruct e as [s1 s2 | j1 j2 | rt ri rv | tt jj ww | lt ll | ut ul | stt | ett];
      simpls; tryfalse.
    subst jj. exists lw tt ww. exact Hsnoc.
Qed.

(* A volatile variable is never pending in any thread's delta: the only play
   step that inserts a key into a delta is [PlayWrite], which requires
   [x \notin Volatiles]; every other step either leaves [D] untouched or
   resets a whole thread's delta to [empty]. Phrased via [binds] plus
   [t \indom D] (mirroring every call site, and [conflict_free_last_local_write]'s
   own convention) to sidestep reasoning about reading an unbound key of the
   OUTER [deltas] map, whose [Inhab] default is classically opaque. *)
Lemma volatile_notin_delta :
  forall log D TC G LC VC CH x t v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    t \indom D ->
    binds D[t] x v ->
    False.
Proof.
  introv Hplay Hxvol Htd Hbd. gen t v. inductions Hplay; introv Htd Hbd.
  - rew_dom. rew_set in Htd. branches; [ forwards*: indom_empty_inv | ].
    subst t. rewrite read_update_same in Hbd. forwards* Heq: binds_empty_false Hbd. typeclass.
  - rename H into Hpe. inverts Hpe.
    + (* PlayRead: D unchanged *) forwards*: IHHplay Htd Hbd.
    + (* PlayReadVolatile: D unchanged *) forwards*: IHHplay Htd Hbd.
    + (* PlayWrite t0 x0 v0: only touches [D[t0][x0]], and [x0 \notin Volatiles] *)
      destruct (classic (t = t0)) as [-> | Hne].
      * rewrite read_update_same in Hbd.
        destruct (classic (x = x0)) as [-> | Hxne].
        -- match goal with Hnv : x0 \notin Volatiles |- _ => applys Hnv Hxvol end.
        -- forwards~ Hbd': binds_update_neq_inv Hbd.
           match goal with Hb0 : binds ?DD t0 ?dd |- _ =>
             lets Hindd: (indom_of_binds Hb0);
             rewrite <- (read_of_binds Hb0) in Hbd';
             forwards*: IHHplay Hindd Hbd' end.
      * rewrite~ read_update_neq in Hbd.
        asserts Htd': (t \indom D'). { lets [Hc | Hd]: (indom_update_inv Htd). congruence. exact Hd. }
        forwards*: IHHplay Htd' Hbd.
    + (* PlayWriteVolatile: [D[t0] := empty] -- impossible given [binds D[t] x v]
         when [t = t0], so [t <> t0] and [D] is otherwise untouched at [t]. *)
      asserts Hne: (t <> t0).
      { intros ->. rewrite read_update_same in Hbd.
        lets Hin0: (indom_of_binds Hbd). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hbd.
      asserts Htd': (t \indom D'). { lets [Hc | Hd]: (indom_update_inv Htd). congruence. exact Hd. }
      forwards*: IHHplay Htd' Hbd.
    + (* PlayStart: D unchanged *) forwards*: IHHplay Htd Hbd.
    + (* PlayEnd t0: [D[t0] := empty] *)
      asserts Hne: (t <> t0).
      { intros ->. rewrite read_update_same in Hbd.
        lets Hin0: (indom_of_binds Hbd). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hbd.
      rew_dom. rew_set in Htd. branches; [|congruence].
      forwards*: IHHplay Hbd.
    + (* PlaySpawn t1 t2: [D[t1 := empty][t2 := empty]] *)
      asserts Hne2: (t <> t2).
      { intros ->. rewrite read_update_same in Hbd.
        lets Hin0: (indom_of_binds Hbd). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hbd.
      asserts Hne1: (t <> t1).
      { intros ->. rewrite read_update_same in Hbd.
        lets Hin0: (indom_of_binds Hbd). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hbd.
      rew_dom. rew_set in Htd. repeat (branches; [|congruence]).
      forwards*: IHHplay Hbd.
    + (* PlayJoin: D unchanged *) forwards*: IHHplay Htd Hbd.
    + (* PlayLock: D unchanged *) forwards*: IHHplay Htd Hbd.
    + (* PlayUnlock t0 l: [D[t0] := empty] *)
      asserts Hne: (t <> t0).
      { intros ->. rewrite read_update_same in Hbd.
        lets Hin0: (indom_of_binds Hbd). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hbd.
      rew_dom. rew_set in Htd. branches; [|congruence].
      forwards*: IHHplay Hbd.
Qed.

(* [vc_read VC x] (for a volatile [x] already touched, i.e. [x \indom VC]) is
   always the LATEST value of [x] in the graph: every volatile access
   immediately pulls/pushes through this single pointer, so it is exactly the
   commit of the most recent volatile write (or [root_commit] if untouched). *)
Lemma vc_read_is_latest_value :
  forall log D TC G LC VC CH x,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    x \indom VC ->
    exists v, is_latest_value G (vc_read VC x) x v.
Proof.
  introv Hplay Hxvol. gen x. inductions Hplay; introv Hxvol2 Hxin.
  - rew_dom. rew_set in Hxin. false. applys indom_empty_inv Hxin.
  - forwards Hpgwf: play_log_graph_wf Hplay.
    destruct Hpgwf as (Hedge & HTC & HLC & HVC & Hroot).
    rename H into Hpe.
    inverts Hpe as.
    (* PlayRead *)
    { introv Hnv. forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin. }
    (* PlayReadVolatile *)
    { introv Hxvol' Hbc Hfresh.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      applys~ is_latest_value_graph_merge_mono Hedge Hfresh Hcneq. }
    (* PlayWrite (non-volatile) *)
    { introv Hnv Hbd. forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin. }
    (* PlayWriteVolatile *)
    { introv Hxvol' Hbd Hbc Hfresh Hfresh2.
      destruct (classic (x = x0)) as [-> | Hxne].
      - (* fresh writer: [VC[x0:=c''][x0] = c''] IS the fresh commit itself *)
        exists v.
        asserts HVeq: (vc_read VC'[x0:=c''] x0 = c'').
        { unfold vc_read. apply read_default_update_same. }
        rewrite HVeq.
        asserts Hc'dom: (graph_indom (graph_merge G' (vc_read VC' x0) c c') c').
        { unfold graph_indom, graph_merge. destruct G' as (C&P). apply indom_update_same; typeclass. }
        asserts Hedge2: (forall a b, graph_edge (graph_merge G' (vc_read VC' x0) c c') a b ->
                                      graph_indom (graph_merge G' (vc_read VC' x0) c c') a /\
                                      graph_indom (graph_merge G' (vc_read VC' x0) c c') b).
        { applys graph_merge_edge_wf Hedge.
          { applys vc_read_graph_indom Hplay. }
          { destruct G' as (C0&P0). applys binds_graph_indom Hbc HTC. } }
        applys~ is_latest_value_graph_commit_fresh_writer Hedge2 Hfresh2 Hc'dom.
        apply binds_update_same.
      - (* [x0 <> x]: [VC] unchanged at [x]; graph gets merge then commit, neither
           of which writes [x] (merge writes nothing; commit's diff [d[x0:=v]]
           writes [x0], not [x], since [x] never entered [d] -- [volatile_notin_delta]). *)
        asserts Hxin': (x \indom VC').
        { lets [Hc | Hc]: (indom_update_inv Hxin). congruence. exact Hc. }
        forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin'.
        exists v0.
        asserts HVeq: (vc_read VC'[x0:=c''] x = vc_read VC' x).
        { unfold vc_read. apply read_default_update_neq. intro Heq; applys Hxne; congruence. }
        rewrite HVeq.
        asserts Hcneq: (vc_read VC' x <> c').
        { intro Heq.
          forwards Hdom: (>> vc_read_graph_indom x Hplay).
          rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
        asserts Hedge2: (forall a b, graph_edge (graph_merge G' (vc_read VC' x0) c c') a b ->
                                      graph_indom (graph_merge G' (vc_read VC' x0) c c') a /\
                                      graph_indom (graph_merge G' (vc_read VC' x0) c c') b).
        { applys graph_merge_edge_wf Hedge.
          { applys vc_read_graph_indom Hplay. }
          { destruct G' as (C0&P0). applys binds_graph_indom Hbc HTC. } }
        asserts Hlv2: (is_latest_value (graph_merge G' (vc_read VC' x0) c c') (vc_read VC' x) x v0).
        { applys~ is_latest_value_graph_merge_mono Hedge Hfresh Hcneq. }
        asserts Hcneq2: (vc_read VC' x <> c'').
        { intro Heq.
          asserts Hdom2: (graph_indom (graph_merge G' (vc_read VC' x0) c c') (vc_read VC' x)).
          { forwards Hd: (>> vc_read_graph_indom x Hplay).
            unfold graph_indom, graph_merge in *. destruct G' as (C0&P0). simpl in Hd.
            apply indom_update_of_indom; (typeclass || exact Hd). }
          rewrite Heq in Hdom2. applys commit_fresh_not_indom Hfresh2 Hdom2. }
        asserts Hnw: (forall v', ~ binds d[x0:=v] x v').
        { intros v' Hbdd. forwards Hbdd': binds_update_neq_inv Hbdd Hxne.
          asserts Hbdd'': (binds D'[t] x v').
          { rewrite (read_of_binds Hbd). exact Hbdd'. }
          applys volatile_notin_delta Hplay Hxvol2 (indom_of_binds Hbd) Hbdd''. }
        applys~ is_latest_value_graph_commit_mono Hedge2 Hfresh2 Hcneq2 Hnw Hlv2. }
    (* PlayStart *)
    { forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin. }
    (* PlayEnd *)
    { introv Hbc Hfresh Hbd.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      asserts Hnw: (forall v', ~ binds d x v').
      { intros v' Hbdd.
        asserts Hbdd2: (binds D'[t] x v'). { rewrite (read_of_binds Hbd). exact Hbdd. }
        applys volatile_notin_delta Hplay Hxvol2 (indom_of_binds Hbd) Hbdd2. }
      applys~ is_latest_value_graph_commit_mono Hedge Hfresh Hcneq Hnw. }
    (* PlaySpawn *)
    { introv Hbc Hfresh Hbd.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      asserts Hnw: (forall v', ~ binds d x v').
      { intros v' Hbdd.
        asserts Hbdd2: (binds D'[t1] x v'). { rewrite (read_of_binds Hbd). exact Hbdd. }
        applys volatile_notin_delta Hplay Hxvol2 (indom_of_binds Hbd) Hbdd2. }
      applys~ is_latest_value_graph_commit_mono Hedge Hfresh Hcneq Hnw. }
    (* PlayJoin *)
    { introv Hbc1 Hbc2 Hfresh.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      applys~ is_latest_value_graph_merge_mono Hedge Hfresh Hcneq. }
    (* PlayLock *)
    { introv Hbc Hfresh.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      applys~ is_latest_value_graph_merge_mono Hedge Hfresh Hcneq. }
    (* PlayUnlock *)
    { introv Hbc Hfresh Hbd.
      forwards* (v0 & Hlv): IHHplay Hxvol2 Hxin.
      exists v0.
      asserts Hcneq: (vc_read VC x <> c').
      { intro Heq.
        forwards Hdom: (>> vc_read_graph_indom x Hplay).
        rewrite Heq in Hdom. applys commit_fresh_not_indom Hfresh Hdom. }
      asserts Hnw: (forall v', ~ binds d x v').
      { intros v' Hbdd.
        asserts Hbdd2: (binds D'[t] x v'). { rewrite (read_of_binds Hbd). exact Hbdd. }
        applys volatile_notin_delta Hplay Hxvol2 (indom_of_binds Hbd) Hbdd2. }
      applys~ is_latest_value_graph_commit_mono Hedge Hfresh Hcneq Hnw. }
Qed.

(* [VC]'s domain only grows across a play step: the only step that touches it
   is [PlayWriteVolatile] (adding a key), every other step leaves it untouched. *)
Lemma play_event_indom_VC_mono :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' x,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    x \indom VC' -> x \indom VC''.
Proof.
  introv Hpe Hin. inverts Hpe; try assumption.
  apply indom_update_of_indom; (typeclass || assumption).
Qed.

(* A play step never removes a thread from the delta map. *)
Lemma play_event_indom_D_mono :
  forall E D' TC' G' LC' VC' D'' TC'' G'' LC'' VC'' t,
    play_event E (D', TC', G', LC', VC') (D'', TC'', G'', LC'', VC'') ->
    t \indom D' -> t \indom D''.
Proof.
  introv Hpe Hin. inverts Hpe; try assumption.
  - apply indom_update_of_indom; (typeclass || assumption).
  - apply indom_update_of_indom; (typeclass || assumption).
  - apply indom_update_of_indom; (typeclass || assumption).
  - apply indom_update_of_indom;
      (typeclass || (apply indom_update_of_indom; (typeclass || assumption))).
  - apply indom_update_of_indom; (typeclass || assumption).
Qed.

(* A thread that performs a write event is in the delta map. *)
Lemma write_thread_in_delta :
  forall log s0 D TC G LC VC CH m tm x vm,
    play_log log s0 (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    tm \indom D.
Proof.
  introv Hplay. gen m tm x vm. inductions Hplay; introv HNlog.
  - inverts HNlog.
  - forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + forwards Hin: (>> IHHplay (eq_refl : (D', TC', G', LC', VC') = (D', TC', G', LC', VC')) HN0).
      applys play_event_indom_D_mono H Hin.
    + subst E. inverts H; apply indom_update_same; typeclass.
Qed.

(* The last writer of [x] has flushed it: its write happens-before an event of a
   different thread, so it must have committed (cf. [hb_preserves_thread]). *)
Lemma last_writer_not_in_delta :
  forall log D TC G LC VC CH m tm x vm n en,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    LibList.Nth n log en ->
    get_thread en <> tm ->
    hb log m n ->
    x \notindom (D[tm]).
Proof.
  introv Hplay HNm Hlast HNn Hgne Hhb. intro Hidom.
  forwards HtmD: write_thread_in_delta Hplay HNm.
  asserts Hbv: (binds (D[tm]) x (D[tm][x])).
  { applys binds_of_indom_read Hidom; (reflexivity || typeclass). }
  forwards Hdu: (>> delta_is_uncommitted_write Hplay HtmD Hbv).
  destruct Hdu as (m' & HNm' & Hnc).
  forwards Hm'le: Hlast HNm'.
  asserts Hncm:
    (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = tm -> ~ is_commit_event ep).
  { introv Hle HNp Hgp. intro Hcie.
    apply (Hnc p ep); [ nat_math | exact HNp | exact Hgp | exact Hcie ]. }
  asserts Hgteq: (get_thread en = tm).
  { applys hb_preserves_thread Hhb HNm; try reflexivity; try exact Hncm; try exact HNn. }
  exact (Hgne Hgteq).
Qed.

(* The bridge from log happens-before to graph ancestry between flush commits:
   if [ta]'s write at [ka] (flushed into [ha] at [fa], with no [ta]-commit in
   [[ka, fa)]) happens-before [tb]'s write at [kb] (flushed into [hbb] at [fb]),
   and the threads differ, then [ha] is an ancestor of [hbb]. *)
Lemma write_hb_flush_ancestor :
  forall log D TC G LC VC CH ta tb x va vb ka fa ea ha kb fb eb hbb,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    (LibList.Nth ka log (event_write ta x va) /\ LibList.Nth fa CH ha /\
       LibList.Nth fa log ea /\ get_thread ea = ta /\ is_commit_event ea /\ ka <= fa /\
       (forall p ep, ka <= p -> p < fa -> LibList.Nth p log ep -> get_thread ep = ta ->
                     ~ is_commit_event ep)) ->
    (LibList.Nth kb log (event_write tb x vb) /\ LibList.Nth fb CH hbb /\
       LibList.Nth fb log eb /\ get_thread eb = tb /\ is_commit_event eb /\ kb <= fb) ->
    ta <> tb ->
    hb log ka kb ->
    ancestor G ha hbb.
Proof.
  intros log D TC G LC VC CH ta tb x va vb ka fa ea ha kb fb eb hbb.
  intros Hwf Hplay HA HB Htne Hhb.
  destruct HA as (HNka & HNfaCH & HNfalog & Hgta & Hcea & Hkalt & Hncla).
  destruct HB as (HNkb & HNfbCH & HNfblog & Hgtb & Hceb & Hkblt).
  asserts Hgtwa: (get_thread (event_write ta x va) = ta). reflexivity.
  asserts Hnet: (get_thread (event_write tb x vb) <> ta). { simpl. auto. }
  forwards (f' & ef' & Hkaf' & HNf'log & Hgtf' & Hcef' & Hhbf'):
    hb_cross_thread_flush Hhb HNka Hgtwa HNkb Hnet.
  asserts Hfaf': (fa <= f').
  { destruct (classic (f' < fa)) as [Hlt | Hge]; [ | nat_math ].
    exfalso. forwards Hni: Hncla Hkaf' Hlt HNf'log Hgtf'. applys Hni Hcef'. }
  forwards Hlen: play_log_CH_length Hplay.
  forwards Hf'lt: Nth_inbound HNf'log.
  asserts Hf'ltCH: (f' < length CH). nat_math.
  forwards (cf' & HNf'CH): Nth_inbound_inv Hf'ltCH.
  forwards Hkblen: Nth_inbound HNkb.
  asserts HkbltCH: (kb < length CH). nat_math.
  forwards (cb & HNkbCH): Nth_inbound_inv HkbltCH.
  asserts Hgtwb: (get_thread (event_write tb x vb) = tb). reflexivity.
  asserts Hkbfb: (kb <= fb). nat_math.
  forwards Hanc1: (>> CH_thread_monotone Hwf Hplay HNfalog Hgta HNf'log Hgtf' Hfaf' HNfaCH HNf'CH).
  forwards Hanc2: (>> hb_pointer_ancestor Hwf Hplay Hhbf' HNf'CH HNkbCH).
  forwards Hanc3: (>> CH_thread_monotone Hwf Hplay HNkb Hgtwb HNfblog Hgtb Hkbfb HNkbCH HNfbCH).
  applys ancestor_trans Hanc1. applys ancestor_trans Hanc2 Hanc3.
Qed.

(* Any two writers of the SAME variable [x] are ancestor-comparable in a
   conflict-free log. Extracted from (and reused by)
   [conflict_free_log_describes_conflict_free_graph]. *)
Lemma graph_writes_comparable :
  forall log D TC G LC VC CH x va vb ha hbb,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    graph_writes G ha x va ->
    graph_writes G hbb x vb ->
    ancestor G ha hbb \/ ancestor G hbb ha.
Proof.
  introv Hwf Hcf Hplay Hgwa Hgwb.
  forwards (fa & ea & ta & ka & HNfaCH & HNfalog & Hgta & Hcea & Hkalt & HNka & Hncla):
    graph_writes_flush Hplay Hgwa.
  forwards (fb & eb & tb & kb & HNfbCH & HNfblog & Hgtb & Hceb & Hkblt & HNkb & Hnclb):
    graph_writes_flush Hplay Hgwb.
  destruct (classic (ta = tb)) as [Hteq | Htne].
  - rewrite <- Hteq in Hgtb.
    destruct (classic (fa <= fb)) as [Hle | Hgt].
    + left. applys (>> CH_thread_monotone Hwf Hplay HNfalog Hgta HNfblog Hgtb Hle HNfaCH HNfbCH).
    + right. asserts Hle2: (fb <= fa). nat_math.
      applys (>> CH_thread_monotone Hwf Hplay HNfblog Hgtb HNfalog Hgta Hle2 HNfbCH HNfaCH).
  - asserts Hkne: (ka <> kb).
    { intros Heq. subst kb. forwards Heqw: Nth_functional HNka HNkb.
      applys Htne. congruence. }
    destruct (classic (ka < kb)) as [Hlt | Hge].
    + asserts Hacc: (accesses_variable x (event_write tb x vb)). reflexivity.
      forwards Hhbab: (>> Hcf HNka HNkb Hacc Hlt).
      left.
      applys (>> write_hb_flush_ancestor Hwf Hplay
        (conj HNka (conj HNfaCH (conj HNfalog (conj Hgta (conj Hcea (conj Hkalt Hncla))))))
        (conj HNkb (conj HNfbCH (conj HNfblog (conj Hgtb (conj Hceb Hkblt)))))
        Htne Hhbab).
    + asserts Hltba: (kb < ka). nat_math.
      asserts Hacc: (accesses_variable x (event_write ta x va)). reflexivity.
      forwards Hhbba: (>> Hcf HNkb HNka Hacc Hltba).
      right. asserts Htne2: (tb <> ta). { intros HH. apply Htne. symmetry. exact HH. }
      applys (>> write_hb_flush_ancestor Hwf Hplay
        (conj HNkb (conj HNfbCH (conj HNfblog (conj Hgtb (conj Hceb (conj Hkblt Hnclb))))))
        (conj HNka (conj HNfaCH (conj HNfalog (conj Hgta (conj Hcea Hkalt)))))
        Htne2 Hhbba).
Qed.

(* The commit created by a volatile write event carries exactly that write:
   [graph_writes_graph_commit_new] applied to [PlayWriteVolatile]'s own commit
   step, lifted forward through later steps via [play_event_graph_writes_mono]. *)
Lemma write_volatile_graph_writes :
  forall log D TC G LC VC CH t x v m cm,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    LibList.Nth m log (event_write t x v) ->
    LibList.Nth m CH cm ->
    graph_writes G cm x v.
Proof.
  introv Hplay Hxvol. gen m t v cm. inductions Hplay; introv HNlog HNch.
  - inverts HNlog.
  - rename H into Hpe.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + forwards Hib: Nth_inbound HN0.
      forwards [HN0ch | (HmNch & _)]: Nth_last_inv HNch.
      2:{ rewrite Hlen in HmNch. nat_math. }
      forwards Hgw: (>> IHHplay (eq_refl init_play_cfg) (eq_refl (D', TC', G', LC', VC')) Hxvol HN0 HN0ch).
      applys play_event_graph_writes_mono Hpe Hgw.
    + subst E. inverts Hpe as Hxvol' Hbd Hbc Hfresh Hfresh2.
      * false.
      * forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
        { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
        cbn [get_thread] in Hcmeq. rewrite read_update_same in Hcmeq. subst cm.
        applys graph_writes_graph_commit_new. apply binds_update_same.
Qed.

(* ===========================================================================
   The volatile-read completeness bridge.

   [vc_read_is_latest_value] identifies the latest value at the volatile's OWN
   stored commit [vc_read VC x], BEFORE a pull. [StepReadVolatile] (Branching.v)
   requires [is_latest_value] at the FRESH commit [c''] created by the pull's
   [graph_merge] of [vc_read VC x] and the reading thread's OWN commit [TC[t]] --
   a DIFFERENT commit, not covered by [is_latest_value_graph_merge_mono] (which
   only forward-preserves [is_latest_value] at an old, off-to-the-side commit,
   not at the merge's own new node). [is_latest_value_graph_merge_fresh]
   (GraphFacts.v) supplies exactly this, GIVEN [is_latest_value G (vc_read VC x)
   x v] and that every [x]-writer is already an ancestor of [vc_read VC x]
   ([write_ancestor_VC]: every volatile write chains directly through the
   single [VC] pointer, unconditionally). *)
Lemma is_latest_value_after_volatile_pull :
  forall log D TC G LC VC CH t x v c'',
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    t \indom TC ->
    commit_fresh G c'' ->
    vc_read VC x <> c'' ->
    x \in Volatiles ->
    (exists tw log', LibList.filter (fun e => writes_variable x e) log = log' & event_write tw x v) ->
    is_latest_value (graph_merge G (vc_read VC x) (TC[t]) c'') c'' x v.
Proof.
  introv Hwf Hcf Hplay Htd Httc Hfresh Hcneq Hxvol (tw & log' & Hfilter).
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct Hpgwf as (Hedge & HTC & _ & _ & _).
  asserts Hp1dom: (graph_indom G (vc_read VC x)). { applys vc_read_graph_indom Hplay. }
  asserts Hp2dom: (graph_indom G (TC[t])). { applys HTC Httc. }
  forwards (lw & HNlw & Hlast): last_write_position Hfilter.
  forwards Hlwlt: Nth_inbound HNlw.
  forwards Hlen: play_log_CH_length Hplay.
  asserts HlwltCH: (lw < length CH). { nat_math. }
  forwards (c_lw & HNlwCH): Nth_inbound_inv HlwltCH.
  asserts Hgwlw: (graph_writes G c_lw x v).
  { applys write_volatile_graph_writes Hplay Hxvol HNlw HNlwCH. }
  asserts Hancl: (ancestor G c_lw (vc_read VC x)).
  { applys write_ancestor_VC Hwf Hplay Hxvol HNlw HNlwCH. }
  asserts Hval: (is_latest_value G (vc_read VC x) x v).
  { exists c_lw. splits.
    - exact Hgwlw.
    - exact Hancl.
    - introv Hgw3 Hanc1 Hanc2.
      destruct (classic (c''0 = c_lw)) as [-> | Hne]; [reflexivity | exfalso].
      forwards (f3 & ef3 & tw3 & kw3 & HNf3CH & HNf3log & Hgt3 & Hcef3 & Hkw3lt & HNkw3 & Hncl3):
        graph_writes_flush Hplay Hgw3.
      asserts Hkw3eq: (kw3 = f3).
      { destruct (classic (kw3 = f3)) as [Heq | Hne2]; [exact Heq | exfalso].
        asserts Hlt3: (kw3 < f3). { nat_math. }
        asserts Hle3: (kw3 <= kw3). { nat_math. }
        forwards Hni: Hncl3 Hle3 Hlt3 HNkw3 (eq_refl : get_thread (event_write tw3 x v') = tw3).
        applys Hni. simpl. exact Hxvol. }
      subst kw3.
      asserts Hf3lelw: (f3 <= lw). { applys Hlast HNkw3. }
      asserts Hcelw: (is_commit_event (event_write tw x v)). { simpl. exact Hxvol. }
      asserts Hne': (c_lw <> c''0). { intro Heq. applys Hne (eq_sym Heq). }
      forwards [Hc | Hc]: graph_writes_comparable Hwf Hcf Hplay Hgwlw Hgw3.
      + (* [ancestor c_lw c''0] *)
        forwards Hlwltf3: (>> ancestor_creation_order Hplay HNlwCH HNlw Hcelw HNf3CH HNf3log Hcef3 Hc Hne').
        nat_math.
      + (* [ancestor c''0 c_lw]: antisymmetry with [Hanc1] *)
        forwards Hwfg: play_log_wf_graph Hplay.
        destruct Hwfg as (_ & Hantisym & _).
        applys Hne. symmetry. applys Hantisym Hanc1 Hc. }
  (* every [x]-writer is already an ancestor of [vc_read VC x] *)
  asserts Hdom: (forall c v', graph_writes G c x v' -> ancestor G c (vc_read VC x)).
  { introv Hgw.
    forwards (f' & ef' & tw' & kw' & HNfCH & HNflog & Hgtw & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush Hplay Hgw.
    asserts Hkweq: (kw' = f').
    { destruct (classic (kw' = f')) as [Heq | Hne]; [exact Heq | exfalso].
      asserts Hlt: (kw' < f'). { nat_math. }
      asserts Hle: (kw' <= kw'). { nat_math. }
      forwards Hni: Hncl Hle Hlt HNkw (eq_refl : get_thread (event_write tw' x v') = tw').
      applys Hni. simpl. exact Hxvol. }
    subst kw'.
    applys write_ancestor_VC Hwf Hplay Hxvol HNkw HNfCH. }
  applys~ (>> is_latest_value_graph_merge_fresh Hedge Hfresh Hp1dom Hp2dom Hval Hdom).
Qed.

(* The reverse direction of [is_latest_value_after_volatile_pull]: whatever
   value [v] a [StepReadVolatile] pull actually observes at the fresh merge
   commit, [v] is the log's last write of [x]. Used by [branching_sound]'s
   StepReadVolatile case to justify the matching (non-volatile) SharedMemory
   read. *)
Lemma is_latest_value_after_volatile_pull_inv :
  forall log D TC G LC VC CH t x v c'',
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    t \indom TC ->
    commit_fresh G c'' ->
    vc_read VC x <> c'' ->
    x \in Volatiles ->
    is_latest_value (graph_merge G (vc_read VC x) (TC[t]) c'') c'' x v ->
    exists tw log', LibList.filter (fun e => writes_variable x e) log = log' & event_write tw x v.
Proof.
  introv Hwf Hcf Hplay Hdt HtTC Hfresh Hcneq Hxvol Hlv.
  destruct (last_case (LibList.filter (fun e => writes_variable x e) log)) as [Hnil | (e0 & l0 & Heq)].
  - exfalso.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    asserts Hcwne: (cw <> c'').
    { intro Heqc. subst cw. applys graph_writes_graph_merge_same_false Hgw. }
    forwards Hgw': graph_writes_graph_merge_inv Hcwne Hgw.
    forwards (tw & m & HNm): graph_writes_log_write Hplay Hgw'.
    forwards Hmem: Nth_mem HNm.
    asserts Hmemf: (mem (event_write tw x v) (LibList.filter (fun e => writes_variable x e) log)).
    { applys mem_filter Hmem. reflexivity. }
    rewrite Hnil in Hmemf. rewrite mem_nil_eq in Hmemf. exact Hmemf.
  - asserts Hwv: (writes_variable x e0).
    { asserts Hmeme0: (mem e0 (LibList.filter (fun e => writes_variable x e) log)).
      { rewrite Heq. applys mem_last_r. }
      forwards (_ & Hwv0): mem_filter_inv Hmeme0. exact Hwv0. }
    destruct e0 as [ | | | tw0 x0 v0 | | | | ]; try (simpl in Hwv; contradiction).
    simpl in Hwv. subst x0.
    forwards Hval: (>> is_latest_value_after_volatile_pull Hwf Hcf Hplay Hdt HtTC Hfresh Hcneq Hxvol).
    { exists tw0 l0. exact Heq. }
    destruct Hlv as (cw1 & Hgw1 & Hanc1 & Hmax1).
    destruct Hval as (cw2 & Hgw2 & Hanc2 & Hmax2).
    asserts Hcw1ne: (cw1 <> c''). { intro Heqc. subst cw1. applys graph_writes_graph_merge_same_false Hgw1. }
    asserts Hcw2ne: (cw2 <> c''). { intro Heqc. subst cw2. applys graph_writes_graph_merge_same_false Hgw2. }
    forwards Hgw1': graph_writes_graph_merge_inv Hcw1ne Hgw1.
    forwards Hgw2': graph_writes_graph_merge_inv Hcw2ne Hgw2.
    forwards [Hc | Hc]: graph_writes_comparable Hwf Hcf Hplay Hgw1' Hgw2'.
    + (* [ancestor G cw1 cw2]: [cw1]'s own maximality collapses [cw2] onto it *)
      forwards Hcmerge: ancestor_graph_merge Hc.
      forwards Heqcw: Hmax1 cw2 v0 Hgw2 Hcmerge Hanc2.
      subst cw2.
      forwards Heqv: graph_writes_inj Hgw2' Hgw1'. subst v0.
      exists tw0 l0. exact Heq.
    + (* [ancestor G cw2 cw1]: [cw2]'s own maximality collapses [cw1] onto it *)
      forwards Hcmerge: ancestor_graph_merge Hc.
      forwards Heqcw: Hmax2 cw1 v Hgw1 Hcmerge Hanc1.
      subst cw1.
      forwards Heqv: graph_writes_inj Hgw1' Hgw2'. subst v0.
      exists tw0 l0. exact Heq.
Qed.

(* A data-race-free log replays to a conflict-free commit graph. *)
Theorem conflict_free_log_describes_conflict_free_graph :
  forall log D TC G LC VC CH,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    conflict_free_graph G.
Proof.
  introv Hwf Hcf Hplay.
  forwards Hpgwf: play_log_graph_wf Hplay.
  intros h1 h2 Hd1 Hd2.
  unfold conflict_free_merge. rew_set. intros x Hmem1 Hmem2.
  rew_set in Hmem1. destruct Hmem1 as [Hde | Hcs1].
  { applys indom_empty_inv Hde. }
  destruct G as (C & P). destruct Hpgwf as (Hedge & _ & _).
  unfold change_set in Hcs1, Hmem2.
  destruct Hcs1 as (ha & Hidoma & Hanca1 & Hnanca2).
  destruct Hmem2 as (hbb & Hidomb & Hancb2 & Hnancb1).
  asserts Hdomha: (graph_indom (C, P) ha).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hanca1; [ exact Hin | subst ha; exact Hd1 ]. }
  asserts Hdomhb: (graph_indom (C, P) hbb).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hancb2; [ exact Hin | subst hbb; exact Hd2 ]. }
  asserts Hgwa: (graph_writes (C, P) ha x (C[ha][x])).
  { exists (C[ha]). split.
    - unfold graph_binds. applys binds_of_indom_read Hdomha; (reflexivity || typeclass).
    - applys binds_of_indom_read Hidoma; (reflexivity || typeclass). }
  asserts Hgwb: (graph_writes (C, P) hbb x (C[hbb][x])).
  { exists (C[hbb]). split.
    - unfold graph_binds. applys binds_of_indom_read Hdomhb; (reflexivity || typeclass).
    - applys binds_of_indom_read Hidomb; (reflexivity || typeclass). }
  asserts Hcmp: (ancestor (C, P) ha hbb \/ ancestor (C, P) hbb ha).
  { applys graph_writes_comparable Hwf Hcf Hplay Hgwa Hgwb. }
  destruct Hcmp as [Hc | Hc].
  - applys Hnanca2. applys ancestor_trans Hc Hancb2.
  - applys Hnancb1. applys ancestor_trans Hc Hanca1.
Qed.

(* Forward direction of the global-read correspondence: if [v] is the value of
   the last write to [x] in the log and [t] reads [x] globally (it is not in [t]'s
   delta), then [v] is exactly the value [t] sees in the commit graph
   ([is_latest_value]).

   This is the shared core that both directions of the global-read equivalence
   build on: [branching_complete] uses it as is, and [conflict_free_last_global_write]
   (its converse) recovers it via [is_latest_value_inj]. *)
Lemma last_global_write_latest_value :
  forall log D TC G LC VC CH t x vr v t' log',
    x \notin Volatiles ->
    conflict_free (log & event_read t x vr) ->
    wf_log (log & event_read t x vr) ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \notindom (D[t]) ->
    LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v ->
    is_latest_value G (TC[t]) x v.
Proof.
  introv Hnvol Hcf Hwf Hplay Hndom Hfilter.
  forwards (mw & HNL & Hlast): last_write_position Hfilter.
  forwards HLlt: Nth_inbound HNL.
  (* Play the read as a no-op, and place the write and the read in [log & read]. *)
  asserts Hplayf: (exists CHf, play_log (log & event_read t x vr) init_play_cfg (D, TC, G, LC, VC) CHf).
  { eexists. applys PlaySnoc Hplay. applys PlayRead Hnvol. }
  destruct Hplayf as (CHf & Hplayf).
  asserts HNLf: (LibList.Nth mw (log & event_read t x vr) (event_write t' x v)).
  { applys* Nth_app_l. }
  asserts HNread: (LibList.Nth (length log) (log & event_read t x vr) (event_read t x vr)).
  { applys* Nth_app_r'. }
  asserts Hlastf:
    (forall k tk vk, LibList.Nth k (log & event_read t x vr) (event_write tk x vk) -> k <= mw).
  { introv HNk. forwards [HN' | (Hpe & Hee)]: Nth_last_inv HNk.
    - applys Hlast HN'.
    - inverts Hee. }
  (* conflict-freedom: the last write happens-before the read (they share [x]). *)
  asserts Hacc: (accesses_variable x (event_read t x vr)). { reflexivity. }
  forwards Hhb: Hcf HNLf HNread Hacc HLlt.
  (* the last writer has flushed [x]. *)
  asserts HndomL: (x \notindom (D[t'])).
  { destruct (classic (t' = t)) as [-> | Hne].
    - exact Hndom.
    - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb.
      simpl. congruence. }
  forwards Hlv: (>> hb_last_write_visible Hwf Hcf Hplayf HNLf Hlastf HndomL HNread Hhb).
  simpl in Hlv. exact Hlv.
Qed.

(* Global counterpart of [conflict_free_last_local_write]: when [t] reads [x]
   globally (it is not in [t]'s delta), the value [t] sees ([is_latest_value]) is
   the last write to [x] in the log. This is the converse of
   [last_global_write_latest_value].

   [conflict_free_graph G] is not assumed: it is recovered from the conflict-free
   [log] via [conflict_free_log_describes_conflict_free_graph]. *)
Lemma conflict_free_last_global_write :
  forall log D TC G LC VC CH t x v c,
    x \notin Volatiles ->
    conflict_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    TC[t] = c ->
    is_latest_value G c x v ->
    exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v.
Proof.
  introv Hnvol Hcf Hwf Hplay Hndom Hdom HTC Hval.
  (* [conflict_free_graph] is recovered from the conflict-free log. *)
  forwards Hwf': wf_log_last_inv Hwf.
  forwards Hcflog: conflict_free_last_inv Hcf.
  forwards Hcfg: conflict_free_log_describes_conflict_free_graph Hwf' Hcflog Hplay.
  (* [is_latest_value] ensures there is an x-write; take the last one. *)
  forwards (lw & tL & vL & Hfilter): is_latest_value_log_write Hplay Hval.
  (* the forward direction: [t] sees the last write's value [vL] *)
  forwards Hlv: (>> last_global_write_latest_value Hnvol Hcf Hwf Hplay Hndom Hfilter).
  rewrite HTC in Hlv.
  (* and [is_latest_value] is functional, so [vL = v] *)
  forwards ->: is_latest_value_inj Hcfg Hlv Hval.
  exists tL lw. exact Hfilter.
Qed.

(* The global-read correspondence as a full equivalence: for a data-race-free,
   [t]-readable log, the value [t] sees for [x] in the commit graph
   ([is_latest_value]) is exactly the value of the last write to [x] in the log.
   This simply packages the two directions -- [last_global_write_latest_value] and
   its converse [conflict_free_last_global_write]. *)
Theorem is_latest_value_iff_last_write :
  forall log D TC G LC VC CH t x v,
    x \notin Volatiles ->
    conflict_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    (is_latest_value G (TC[t]) x v
     <-> exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v).
Proof.
  introv Hnvol Hcf Hwf Hplay Hndom Hdom. split.
  - introv Hval.
    applys (>> conflict_free_last_global_write Hnvol Hcf Hwf Hplay Hndom Hdom); [ reflexivity | exact Hval ].
  - introv (t' & log' & Hfilter).
    applys (>> last_global_write_latest_value Hnvol Hcf Hwf Hplay Hndom Hfilter).
Qed.

(* A graph commit [c] that writes a variable [j] still uncommitted by a thread [t]
   must be an ancestor of [t]'s commit [TC[t]].  Otherwise [t]'s pending write to
   [j] and [c]'s committed write to [j] would be two writes to the same variable
   that are not happens-before related -- a data race, which [conflict_free]
   forbids.  (Structurally this mirrors [write_hb_flush_ancestor], but the [t]
   side of the race is a pending delta write rather than a flushed one.) *)
Lemma delta_writer_ancestor :
  forall log D TC G LC VC CH t j vt c vc,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    binds (D[t]) j vt ->
    graph_writes G c j vc ->
    ancestor G c (TC[t]).
Proof.
  introv Hwf Hcf Hplay Htdom Hbd Hgw.
  (* [t]'s uncommitted [j]-write at [kt], with no [t]-commit at or after [kt]. *)
  forwards (kt & HNkt & Hns): delta_is_uncommitted_write Hplay Htdom Hbd.
  asserts Hgtt: (get_thread (event_write t j vt) = t). reflexivity.
  (* the graph writer [c] has flushed: fed by [tc]'s write at [kc], committed at [fc]. *)
  forwards (fc & efc & tc & kc & HNfcCH & HNfclog & Hgtc & Hcec & Hkclt & HNkc & Hncl):
    graph_writes_flush Hplay Hgw.
  (* [CH[kt]] is an ancestor of [TC[t]]. *)
  forwards Hlen: play_log_CH_length Hplay.
  forwards Hktlt: Nth_inbound HNkt.
  asserts HktltCH: (kt < length CH). nat_math.
  forwards (ckt & HNktCH): Nth_inbound_inv HktltCH.
  forwards Hanckt: (>> CH_ancestor_TC Hwf Hplay HNkt Hgtt HNktCH).
  destruct (classic (tc = t)) as [Hteq | Htne].
  - (* [c] is [t]'s own commit, hence below [TC[t]]. *)
    rewrite Hteq in Hgtc. applys CH_ancestor_TC Hwf Hplay HNfclog Hgtc HNfcCH.
  - (* [tc <> t]: use conflict-freedom to order the two [j]-writes. *)
    asserts Hkne: (kt <> kc).
    { intros Heq. subst kc. forwards Heqw: Nth_functional HNkt HNkc.
      inverts Heqw. apply Htne. reflexivity. }
    destruct (classic (kt < kc)) as [Hlt | Hge].
    + (* [kt < kc]: the cross-thread [hb] forces a [t]-commit at or after [kt]. *)
      exfalso.
      asserts Hacc: (accesses_variable j (event_write tc j vc)). reflexivity.
      forwards Hhb: (>> Hcf HNkt HNkc Hacc Hlt).
      asserts Hgtcne: (get_thread (event_write tc j vc) <> t). { simpl. exact Htne. }
      forwards (f'' & ef'' & Hktf'' & HNf'' & Hgf'' & Hcef'' & Hhbf''):
        hb_cross_thread_flush Hhb HNkt Hgtt HNkc Hgtcne.
      applys Hns Hktf'' HNf'' Hgf'' Hcef''.
    + (* [kc < kt]: [tc]'s flush is below [TC[t]], so is its earlier commit [c]. *)
      asserts Hltba: (kc < kt). nat_math.
      asserts Hacc: (accesses_variable j (event_write t j vt)). reflexivity.
      forwards Hhb: (>> Hcf HNkc HNkt Hacc Hltba).
      asserts Hgtc2: (get_thread (event_write tc j vc) = tc). reflexivity.
      asserts Hgtne: (get_thread (event_write t j vt) <> tc).
      { simpl. intros HH. apply Htne. symmetry. exact HH. }
      forwards (f' & ef' & Hkcf' & HNf' & Hgf' & Hcef' & Hhbf'):
        hb_cross_thread_flush Hhb HNkc Hgtc2 HNkt Hgtne.
      asserts Hfcf': (fc <= f').
      { destruct (classic (f' < fc)) as [Hltf | Hgef]; [ | nat_math ].
        exfalso. forwards Hni: Hncl Hkcf' Hltf HNf' Hgf'. applys Hni Hcef'. }
      forwards Hf'lt: Nth_inbound HNf'.
      asserts Hf'ltCH: (f' < length CH). nat_math.
      forwards (cf' & HNf'CH): Nth_inbound_inv Hf'ltCH.
      forwards Hanc1: (>> CH_thread_monotone Hwf Hplay HNfclog Hgtc HNf' Hgf' Hfcf' HNfcCH HNf'CH).
      forwards Hanc2: (>> hb_pointer_ancestor Hwf Hplay Hhbf' HNf'CH HNktCH).
      applys ancestor_trans Hanc1. applys ancestor_trans Hanc2. exact Hanckt.
Qed.

(* Volatile write-write ordering: if [t] is about to write a volatile [x]
   (making the log [log & event_write t x v] conflict-free), then [t]'s own
   commit [TC[t]] already descends from [x]'s currently-stored commit
   [vc_read VC x] -- i.e. pulling [vc_read VC x] into [t]'s own diff (now
   including [x]) cannot conflict on [x] itself. Any change-set witness [c]
   for [x] must be a writer of [x] (from [x \indom C[c]]); [conflict_free]
   (applied at [c]'s own flush/write position, which -- since [x] is
   volatile -- IS the write itself, [Hncl] ruling out any strictly earlier
   flush) gives [hb] from that position to [t]'s write; the LAST hop of that
   [hb] derivation must be program order on thread [t]
   ([hb_last_write_same_thread_witness]), landing on some [t]-owned position
   [q] within the existing log; [hb_pointer_ancestor] (or a direct
   [Nth_functional] if the witness collapses to [c]'s own position) turns
   that into graph ancestry, and [CH_ancestor_TC] finishes by relating [q]'s
   own recorded commit to [TC[t]]. *)
Lemma vc_read_change_set_empty_conflict_free :
  forall log D TC G LC VC CH t x v,
    wf_log log ->
    conflict_free (log & event_write t x v) ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \in Volatiles ->
    t \indom TC ->
    x \notin change_set G (TC[t]) (vc_read VC x).
Proof.
  introv Hwf0 Hcf Hplay Hxvol Httc.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct Hpgwf as (Hedge & _).
  forwards Hvcdom: (>> vc_read_graph_indom x Hplay).
  destruct G as (C & P).
  intro Hex. destruct Hex as (c & Hxc & Hancc & Hnanc).
  asserts Hcdom: (graph_indom (C, P) c).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hancc; [ exact Hin | subst c; exact Hvcdom ]. }
  asserts Hgwc: (graph_writes (C, P) c x (C[c][x])).
  { exists (C[c]). split.
    - unfold graph_binds. applys binds_of_indom_read Hcdom; (reflexivity || typeclass).
    - applys binds_of_indom_read Hxc; (reflexivity || typeclass). }
  forwards (f & ef & tw & kw & HNfCH & HNflog & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
    graph_writes_flush Hplay Hgwc.
  asserts Hkweqf: (kw = f).
  { destruct (classic (kw = f)) as [Heq | Hne]; [ exact Heq | exfalso ].
    asserts Hltf: (kw < f). { nat_math. }
    asserts Hle: (kw <= kw). { nat_math. }
    forwards Hni: Hncl Hle Hltf HNkw (eq_refl : get_thread (event_write tw x (C[c][x])) = tw).
    applys Hni. simpl. exact Hxvol. }
  subst kw.
  forwards Hflt: Nth_inbound HNflog.
  asserts HNkwapp: (LibList.Nth f (log & event_write t x v) (event_write tw x (C[c][x]))).
  { applys Nth_app_l HNkw. }
  asserts HNenapp: (LibList.Nth (length log) (log & event_write t x v) (event_write t x v)).
  { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
  asserts Hacc: (accesses_variable x (event_write t x v)). { reflexivity. }
  forwards Hhb: (>> Hcf HNkwapp HNenapp Hacc Hflt).
  forwards (q & eq & Hqlt & HNqapp & Hgq & Hdisj): hb_last_write_same_thread_witness Hhb HNenapp.
  forwards [HNqlog | (mm & Heqm & _)]: Nth_app_inv HNqapp.
  2:{ nat_math. }
  forwards Hlen: play_log_CH_length Hplay.
  asserts HqltCH: (q < length CH). { rewrite Hlen. exact Hqlt. }
  forwards (cq & HNqCH): Nth_inbound_inv HqltCH.
  forwards HancqTC: (>> CH_ancestor_TC Hwf0 Hplay HNqlog Hgq HNqCH).
  destruct Hdisj as [Heqfq | Hhbfq].
  - (* [f = q]: [cq] is exactly [c] *)
    subst q.
    forwards Heqc: Nth_functional HNfCH HNqCH. subst cq.
    applys Hnanc HancqTC.
  - (* [hb (log & e) f q]: lift to the prefix, then [hb ==> ancestor] *)
    forwards Hhbfq': hb_app_inv Hhbfq Hqlt.
    forwards Hancfq: (>> hb_pointer_ancestor Hwf0 Hplay Hhbfq' HNfCH HNqCH).
    applys Hnanc. applys ancestor_trans Hancfq HancqTC.
Qed.

(* Adding one more variable [x] to a diff [d] keeps a merge conflict-free, as
   long as [x] itself isn't in the OTHER side's change set: [dom (d[x:=v])]
   is just [dom d] plus [x], so the disjointness splits into the already-known
   [conflict_free_merge d ...] plus the single fact [x \notin change_set ...]. *)
Lemma conflict_free_merge_add_var :
  forall d c1 c2 G x v,
    conflict_free_merge d c1 c2 G ->
    x \notin change_set G c1 c2 ->
    conflict_free_merge (d[x := v]) c1 c2 G.
Proof.
  introv Hcfm Hxnin. unfold conflict_free_merge in *.
  rew_set in Hcfm. rew_set. intros j Hj1 Hj2.
  rew_set in Hj1. destruct Hj1 as [Hjd | Hjcs].
  - lets [-> | Hjd']: (indom_update_inv Hjd).
    + applys Hxnin Hj2.
    + applys Hcfm j; [ rew_set; left; exact Hjd' | exact Hj2 ].
  - applys Hcfm j; [ rew_set; right; exact Hjcs | exact Hj2 ].
Qed.

(* The merge obligation discharged: when a running thread [t] (pending delta
   [D[t]], commit [TC[t]]) merges with another commit [hc], the merge is
   conflict-free.  The [change_set]/[change_set] half is the keystone
   ([conflict_free_log_describes_conflict_free_graph]); the [dom (D[t])] half is
   [delta_writer_ancestor] (no pending write of [t] can sit in the change set
   merged in from [hc]). *)
Theorem conflict_free_merge_holds :
  forall log D TC G LC VC CH t hc,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    t \indom TC ->
    graph_indom G hc ->
    conflict_free_merge (D[t]) (TC[t]) hc G.
Proof.
  introv Hwf Hcf Hplay Htd Htc Hhc.
  forwards Hcfg: conflict_free_log_describes_conflict_free_graph Hwf Hcf Hplay.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct G as (C & P). destruct Hpgwf as (Hedge & HTCdom & _).
  asserts Htcdom: (graph_indom (C, P) (TC[t])). { applys HTCdom Htc. }
  unfold conflict_free_merge. rew_set. intros j Hj1 Hj2.
  rew_set in Hj1. destruct Hj1 as [Hjd | Hjcs].
  - (* [j] is pending in [t]'s delta: it cannot lie in [change_set (TC[t]) hc]. *)
    unfold change_set in Hj2. destruct Hj2 as (c & Hjc & Hanchc & Hnanc).
    asserts Hdomc: (graph_indom (C, P) c).
    { forwards [Hin | Heq]: ancestor_src_indom Hedge Hanchc; [ exact Hin | subst c; exact Hhc ]. }
    asserts Hgwc: (graph_writes (C, P) c j (C[c][j])).
    { exists (C[c]). split.
      - unfold graph_binds. applys binds_of_indom_read Hdomc; (reflexivity || typeclass).
      - applys binds_of_indom_read Hjc; (reflexivity || typeclass). }
    asserts Hbdj: (binds (D[t]) j (D[t][j])).
    { applys binds_of_indom_read Hjd; (reflexivity || typeclass). }
    applys Hnanc. applys (>> delta_writer_ancestor Hwf Hcf Hplay Htd Hbdj Hgwc).
  - (* [j] lies in both change sets: contradicts conflict-freedom of the graph. *)
    forwards Hcfm: Hcfg Htcdom Hhc.
    unfold conflict_free_merge in Hcfm. rew_set in Hcfm.
    applys Hcfm j; [ rew_set; right; exact Hjcs | exact Hj2 ].
Qed.

(* ===========================================================================
   Soundness of conflict detection (branching).

   The branching model gets *stuck* on a synchronisation only at a [pull], where
   it checks [conflict_free_merge].  The two theorems below are the contrapositive
   of [conflict_free_merge_holds]: if a thread is poised to join a terminated
   thread, or to acquire a free lock, and the corresponding merge check fails --
   so the step is blocked, and not by a deadlock, since the joinee has terminated
   / the lock is free -- then the log already exhibits a data race
   ([~ conflict_free log], i.e. some write and a later access to the same variable
   are not ordered by happens-before).
   =========================================================================== *)

Theorem branching_join_conflict_sound :
  forall log T G L V t e d c K t' r c',
    wf_log log ->
    describes log (T, G, L, V) ->
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, c') ->
    ~ conflict_free_merge d c c' G ->
    ~ conflict_free log.
Proof.
  introv Hwf Hdesc Hbt Hul Hbt' Hncf Hcflog.
  forwards (HwfG & _ & Hcommits & Hlockcommits & _): describes_wf_cfg Hdesc.
  forwards Hcdom: Hcommits Hbt'.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & _ & HdomD & HdomTC & HdomLC)).
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (ts0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  apply Hncf.
  applys (>> conflict_free_merge_holds Hwf Hcflog Hplay HtD HtTC Hcdom).
Qed.

Theorem branching_lock_conflict_sound :
  forall log T G L V t e d c K l c',
    wf_log log ->
    describes log (T, G, L, V) ->
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, c') ->
    ~ conflict_free_merge d c c' G ->
    ~ conflict_free log.
Proof.
  introv Hwf Hdesc Hbt Hul Hbl Hncf Hcflog.
  forwards (HwfG & _ & Hcommits & Hlockcommits & _): describes_wf_cfg Hdesc.
  forwards Hcdom: Hlockcommits Hbl.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & _ & HdomD & HdomTC & HdomLC)).
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (ts0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  apply Hncf.
  applys (>> conflict_free_merge_holds Hwf Hcflog Hplay HtD HtTC Hcdom).
Qed.

(* Reading a volatile [x] is a pull against [vc_read V x], graph-indom by
   [vc_read_graph_indom] regardless of any relationship between [t] and
   whoever last wrote [x] -- so, just like locks and joins, this is a direct
   corollary of [conflict_free_merge_holds]: no extra argument is needed
   because a read never adds [x] itself to the checked diff. *)
Theorem branching_volatile_read_conflict_sound :
  forall log T G L V t e d c K x,
    wf_log log ->
    describes log (T, G, L, V) ->
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_read x) ->
    x \in Volatiles ->
    ~ conflict_free_merge d c (vc_read V x) G ->
    ~ conflict_free log.
Proof.
  introv Hwf Hdesc Hbt Hul Hxvol Hncf Hcflog.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
  subst V.
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (ts0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  forwards Hcdom: (>> vc_read_graph_indom x Hplay).
  apply Hncf.
  applys (>> conflict_free_merge_holds Hwf Hcflog Hplay HtD HtTC Hcdom).
Qed.

(* Writing a volatile [x] additionally folds [x] itself into the checked
   diff ([d[x := v]], per the write-write race fix), so -- unlike the other
   four synchronisations -- this is NOT a direct corollary of
   [conflict_free_merge_holds] alone: [x]'s own membership in the OTHER
   party's change set is exactly the fact [vc_read_change_set_empty_conflict_free]
   supplies, but only relative to the log EXTENDED with this very write ([HbVolatile]
   being write-then-read-only, unlike locks/joins/reads there is no rule making
   [t]'s not-yet-logged pull of [x] unconditionally consistent with [conflict_free
   log] alone -- see the discussion on [ancestor_pos_hb] in BranchingOOTA.v).
   Concretely: if the check fails, appending this very write would ALREADY
   break conflict-freedom -- matching exactly the guard [branching_complete]
   relies on ([BranchingEquiv.v]) to admit a real [conflict_free (log &
   event_write t x v)] step. *)
Theorem branching_volatile_write_conflict_sound :
  forall log T G L V t e d c K x v,
    wf_log log ->
    describes log (T, G, L, V) ->
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    ~ conflict_free_merge d[x := v] c (vc_read V x) G ->
    ~ conflict_free (log & event_write t x v).
Proof.
  introv Hwf Hdesc Hbt Hul Hxvol Hncf Hcflog.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
  subst V.
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (ts0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  forwards Hcdom: (>> vc_read_graph_indom x Hplay).
  forwards Hcflog0: conflict_free_last_inv Hcflog.
  apply Hncf.
  applys conflict_free_merge_add_var.
  - applys (>> conflict_free_merge_holds Hwf Hcflog0 Hplay HtD HtTC Hcdom).
  - applys (>> vc_read_change_set_empty_conflict_free Hwf Hcflog Hplay Hxvol HtTC).
Qed.
