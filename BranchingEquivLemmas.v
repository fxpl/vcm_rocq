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
  forall log D TC G LC CH t x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
          lets Hin: (indom_of_binds H2).
          asserts Hb': (binds (D'[t0]) x v). { forwards: read_of_binds H2. subst*. }
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
    + (* PlayLockFresh: no-op, D unchanged *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
Qed.

Lemma conflict_free_last_local_write :
  forall log D TC G LC CH t x v,
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
             forwards : read_of_binds H2.
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
           (* There is at least one write by t to x0 in log (by Hfilter).
              This write is in the delta of t (by Hdelta), so it has not been committed.
              The log is conflict free (by Hcf) so the write by t to x0
              happens before the write by t0 to x0.
              But since t <> t0 and the write is uncommitted, the happens before
              relation is a contradiction.
            *)
           (* The write [event_write t x0 v] is still in [t]'s delta, hence
              uncommitted: [t] performs no commit event after it. So it cannot
              happen-before the final write by [t0 <> t] (a cross-thread hb edge
              would need a commit event of [t]). But conflict-freedom forces such
              an hb edge. *)
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
    + (* PlayLockFresh: D unchanged *)
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
  forall E D' TC' G' LC' D'' TC'' G'' LC'' x y,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    ancestor G' x y ->
    ancestor G'' x y.
Proof.
  introv Hpe Hanc.
  inverts Hpe; auto using ancestor_graph_commit, ancestor_graph_merge.
Qed.

(* After any play step, each thread's commit pointer advances to a descendant
   (in the new graph) -- except a freshly spawned thread, hence the side-condition. *)
Lemma play_event_TC_advance :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' t,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
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
  forall log s0 D TC G LC CH m em t cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
      forwards Hanc: IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0 Hgt HN0ch.
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
  forall log s0 D TC G LC CH m n em en t cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC'))
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
  forall E D' TC' G' LC' D'' TC'' G'' LC'' t c,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    binds TC' t c ->
    get_thread E <> t ->
    (forall t1, E <> event_spawn t1 t) ->
    binds TC'' t c.
Proof.
  introv Hpe Hb Hgt Hsp.
  inverts Hpe; simpls; try assumption.
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
  forall log s0 D TC G LC CH m t2 cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
      forwards Hbpre: (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0 HN0ch).
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
  forall log s0 D TC G LC CH m t1 t2 cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
      forwards Hbpre: (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0 Hnst0 HN0ch).
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

(* A single play step leaves [LC[l]] untouched whenever the event is not an
   unlock of [l] (only [PlayUnlock] writes the lock map). *)
Lemma play_event_LC_preserved :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' l c,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    (forall t3, E <> event_unlock t3 l) ->
    binds LC' l c ->
    binds LC'' l c.
Proof.
  introv Hpe Hne Hb. inverts Hpe; try assumption.
  - (* PlayUnlock t l0: LC'' = LC'[l0 := c']; l0 <> l from Hne *)
    applys binds_update_neq; [ | assumption ].
    intro Heq. subst. eapply Hne; reflexivity.
  - (* PlayLockFresh t lf: LC'' = LC'[lf := TC[t]]; l = lf makes [Hb] vacuous *)
    match goal with Hf : ?lf \notindom LC' |- _ =>
      destruct (classic (l = lf)) as [-> | Hne2];
      [ lets Hin: (indom_of_binds Hb); exfalso; applys Hf Hin
      | applys binds_update_neq; [ congruence | exact Hb ] ] end.
Qed.

(* Held-lock invariant: if the [l]-filter of the log ends in [event_lock t l]
   (so [t] currently holds [l]), then [l]'s stored commit is an ancestor of [t]'s
   current commit. Acquiring [l] merged [LC[l]] into [t], and [LC[l]] is unchanged
   until [t] releases. *)
Lemma held_dominates :
  forall log s0 D TC G LC CH l t pre,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
    LibList.filter (fun e => touches_lock l e) log = pre & event_lock t l ->
    exists cl, binds LC l cl /\ ancestor G cl (TC[t]).
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
      inverts H as Hb1 HbL Hfr.
      * (* PlayLock: merged [LC[l]] into [t] *)
        exists c2. split.
        -- exact HbL.
        -- rewrite read_update_same. apply ancestor_graph_merge_edge_r.
      * (* PlayLockFresh: [t] records its own commit, [TC] unchanged *)
        exists (TC[t]). split.
        -- apply binds_update_same.
        -- apply ancestor_refl.
    + (* E does not touch l: LC[l] and the held relation are preserved *)
      rew_list in Hfilter.
      asserts Hmemfilt:
        (mem (event_lock t l) (LibList.filter (fun e => touches_lock l e) log)).
      { rewrite Hfilter. rewrite mem_last_eq. right. reflexivity. }
      forwards (Hmemf & _): mem_filter_inv Hmemfilt.
      forwards (klock & Hklock): mem_Nth Hmemf.
      forwards (cl & Hbcl & Hanccl):
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) Hfilter).
      exists cl. split.
      * applys play_event_LC_preserved H Hbcl.
        intros t3 Heq. apply Ht. rewrite Heq. reflexivity.
      * apply ancestor_trans with (c' := TC'[t]).
        -- eapply play_event_graph_extends; eassumption.
        -- applys play_event_TC_advance. eassumption.
           introv Heqsp. rewrite Heqsp in Hwf.
           forwards Hng: spawned_thread_no_prior_event Hwf Hklock.
           cbn [get_thread] in Hng. exact Hng.
Qed.

(* Lock semantics: just before [t] unlocks [l], the lock holds some commit [cl]
   that is an ancestor of [t]'s current commit. *)
Lemma unlock_holder_dominates :
  forall log s0 D TC G LC CH t l c,
    wf_log (log & event_unlock t l) ->
    play_log log s0 (D, TC, G, LC) CH ->
    binds TC t c ->
    exists cl, binds LC l cl /\ ancestor G cl c.
Proof.
  introv Hwf Hplay Hbc.
  forwards (pre & Hpre): unlock_prev_lock Hwf.
  forwards Hwf0: wf_log_last_inv Hwf.
  forwards (cl & Hbcl & Hanc): (>> held_dominates Hwf0 Hplay Hpre).
  exists cl. split. exact Hbcl.
  forwards Hrd: read_of_binds Hbc.
  rewrite <- Hrd. exact Hanc.
Qed.

(* The lock chain: every unlock-of-[l] commit is an ancestor of [l]'s current
   stored commit. [LC[l]] only advances to descendants -- each unlock deposits a
   child of the holder's commit, which (holder fact) already dominates the
   previous [LC[l]]. *)
Lemma unlock_ancestor_LC :
  forall log s0 D TC G LC CH m t1 l cm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth m CH cm ->
    exists cl, binds LC l cl /\ ancestor G cm cl.
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
      forwards (clc & HbLC & Hanc):
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0 HN0ch).
      destruct (classic (exists t3, E = event_unlock t3 l)) as [(t3 & HE) | Hne].
      * (* same lock: chain through the holder's commit *)
        subst E.
        inverts H as Hbc Hfresh Hbd.
        forwards (cl & HbLCl & Hdom): (>> unlock_holder_dominates Hwf Hplay Hbc).
        assert (clc = cl) as Heqcl by (applys binds_inj HbLC HbLCl; typeclass).
        eexists. split.
        -- applys binds_update_same.
        -- apply ancestor_trans with (c' := c).
           ++ apply ancestor_graph_commit.
              apply ancestor_trans with (c' := clc).
              ** exact Hanc.
              ** rewrite Heqcl. exact Hdom.
           ++ apply ancestor_graph_commit_edge.
      * (* different lock (or non-unlock event): LC[l] preserved *)
        exists clc. split.
        -- applys play_event_LC_preserved H HbLC.
           intros t3 Heq. apply Hne. exists t3. exact Heq.
        -- eapply play_event_graph_extends; eassumption.
    + (* unlock m is the last (appended) event *)
      subst E.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      inverts H as Hbc Hfresh Hbd.
      cbn [get_thread] in Hcmeq.
      rewrite read_update_same in Hcmeq. subst cm.
      eexists. split.
      -- applys binds_update_same.
      -- apply ancestor_refl.
Qed.

(* The three synchronisation edges: each mirrors the graph_merge / graph_commit
   performed by the corresponding play_event, so the source's commit is an
   ancestor of the target's. *)
Lemma hb_lock_pointer_ancestor :
  forall log s0 D TC G LC CH m n t1 t2 l cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC'))
            HNm0 HNn0 Hlt HNchm0 HNchn0).
      eapply play_event_graph_extends; eassumption.
    + (* lock is the last (appended) event: it merges [l]'s stored commit *)
      subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards (cl & HbLCl & Hanc_cm): (>> unlock_ancestor_LC Hwf0 Hplay HNm0 HNchm0).
      forwards Hanc_lift: play_event_graph_extends H Hanc_cm.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H as Hbc1 HbLC Hfresh.
      * (* PlayLock: merges [l]'s stored commit *)
        cbn [get_thread] in Hcneq.
        rewrite read_update_same in Hcneq. subst cn.
        assert (cl = c2) as Heqc by (applys binds_inj HbLCl HbLC; typeclass).
        apply ancestor_trans with (c' := cl).
        -- exact Hanc_lift.
        -- rewrite Heqc. apply ancestor_graph_merge_edge_r.
      * (* PlayLockFresh: impossible, [l] was unlocked at [m] so [l] ∈ dom LC' *)
        exfalso. lets* Hin: (indom_of_binds HbLCl).
Qed.

Lemma hb_spawn_pointer_ancestor :
  forall log s0 D TC G LC CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC'))
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
  forall log s0 D TC G LC CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC'))
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

(* happens-before implies commit-pointer ancestry. Every hb edge is one
   of the four cases above; transitivity composes them. *)
Lemma hb_pointer_ancestor :
  forall log s0 D TC G LC CH m n cm cn,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
    hb log m n ->
    LibList.Nth m CH cm ->
    LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay Hhb. gen cm cn.
  induction Hhb as
    [ m n t e1 e2 HN1 HN2 Hg1 Hg2 Hlt
    | n m t1 t2 l HNu HNl Hlt
    | m n t1 t2 HNs HNst Hlt
    | m n t1 t2 HNe HNj Hlt
    | m n k Hmk IHmk Hkn IHkn ];
    introv HNchm HNchn.
  - (* HbPo *)
    asserts Hle: (m <= n). { nat_math. }
    applys (>> CH_thread_monotone Hwf Hplay HN1 Hg1 HN2 Hg2 Hle HNchm HNchn).
  - (* HbLock *)
    applys (>> hb_lock_pointer_ancestor Hwf Hplay HNu HNl Hlt HNchm HNchn).
  - (* HbSpawn *)
    applys (>> hb_spawn_pointer_ancestor Hwf Hplay HNs HNst Hlt HNchm HNchn).
  - (* HbJoin *)
    applys (>> hb_join_pointer_ancestor Hwf Hplay HNe HNj Hlt HNchm HNchn).
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

(* hb -> ancestry: the bridge between the log's happens-before order and the
   commit graph. If [m] is the LAST write to [x] in the log, that write is
   committed (no longer in [tm]'s delta), and [m] happens-before some event [n],
   then [vm] is exactly the latest value of [x] visible at [n]'s thread's commit.
   (Being the last write pins the committed value to [vm]; the [hb] edge forces
   [n]'s thread to actually see it — no stale read.) This is the core soundness
   lemma; proved separately via [hb -> commit-pointer ancestry]. *)

(* Every commit that writes [x = v] in a played graph corresponds to a log write
   event of [x = v]: commits are created only by flushing a thread's delta, whose
   [x = v] binding comes (via [delta_is_uncommitted_write]) from a write event. *)
Lemma graph_writes_log_write :
  forall log D TC G LC CH cx x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
    1,2,3: (forwards* (tw & m0 & HN): IHHplay;
           exists tw m0; rew_list; applys Nth_app_l HN).
    + (* PlayEnd: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
    + (* PlayLockFresh: graph unchanged *)
      forwards* (tw & m0 & HN): IHHplay.
      exists tw m0. rew_list. applys Nth_app_l HN.
Qed.

(* A play step preserves every pre-existing committed write (the new commit is
   fresh, so distinct from any existing writer). *)
Lemma play_event_graph_writes_mono :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' cs x v,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    graph_writes G' cs x v ->
    graph_writes G'' cs x v.
Proof.
  introv Hpe Hgw. forwards Hin: graph_writes_to_indom Hgw.
  inverts Hpe; try assumption;
    [ apply graph_writes_graph_commit
    | apply graph_writes_graph_commit
    | apply graph_writes_graph_merge
    | apply graph_writes_graph_merge
    | apply graph_writes_graph_commit];
    try exact Hgw;
    intro Heq; subst cs;
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
Qed.

(* The last write of [x] is either still in [tm]'s delta (with value [vm]), or it
   has been flushed into a commit [cs] holding [x = vm] that is an ancestor of
   [tm]'s current commit. By induction on [play_log]: the write enters [tm]'s
   delta, stays there until a commit event of [tm] flushes it into a new commit
   (being the last x-write, the value is still [vm] at flush time). *)
Lemma last_write_committed_or_delta :
  forall log s0 D TC G LC CH m tm x vm,
    wf_log log ->
    play_log log s0 (D, TC, G, LC) CH ->
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
        (>> IHHplay Hwf0 (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0 Hlast0).
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
      * (* read *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* write wt wj ww *)
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
      * (* lock (PlayLock) *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst eg; simpl; auto. }
      * (* lock (PlayLockFresh): graph unchanged, not a commit event *)
        left; split.
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
      left. split.
      * split.
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_same. rewrite read_update_same. reflexivity.
      * introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
        { forwards Hglt: Nth_inbound HNg0. nat_math. }
        { subst eg; simpl; auto. }
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
    [ p q th e1 e2 HN1 HN2 Hg1 Hg2 Hlt
    | q p lt1 lt2 ll HNsrc HNtgt Hlt
    | p q st1 st2 HNsrc HNtgt Hlt
    | p q jt1 jt2 HNsrc HNtgt Hlt
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
Definition play_graph_wf (TC : commits) (G : graph) (LC : lcommits) : Prop :=
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) /\
  (forall t, t \indom TC -> graph_indom G (TC[t])) /\
  (forall l, l \indom LC -> graph_indom G (LC[l])).

(* Conversion-tolerant membership inversion for an updated pointer map (the
   [Inhab] instance in [indom_update_eq] makes a bare [rewrite] miss the subterm). *)
Lemma indom_update_cases :
  forall (M : map nat commit) x j v,
    j \indom (M[x := v]) -> j = x \/ j \indom M.
Proof. introv H. applys indom_update_inv H; typeclass. Qed.

Lemma play_log_graph_wf :
  forall log D TC G LC CH,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    play_graph_wf TC G LC.
Proof.
  introv Hplay. inductions Hplay.
  - splits.
    + introv He. simpls. rew_set in He. false.
    + introv Ht. rew_dom. rew_set in Ht. branches;
        [ forwards*: indom_empty_inv|].
      subst. rewrite read_update_same.
      applys* graph_root_indom_same.
    + introv Hl. false. applys indom_empty_inv Hl.
  - forwards* Hwf: IHHplay. destruct Hwf as (Hedge & HTC & HLC).
    rename H into Hpe.
    match goal with Hp : play_log _ _ (_, _, ?GG, _) _ |- _ => destruct GG as (C & P) end.
    inverts Hpe; try (splits; assumption).
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
    + (* PlayLock t l: graph_merge (C,P) c2 c1 c', TC[t:=c'] (c2 from LC, c1 from TC) *)
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
        destruct (classic (j = t)) as [-> | Hne].
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_neq; [ | congruence ].
           apply indom_update_of_indom;
             (typeclass || (applys HTC; destruct Hcase as [Hc | Hc]; [ congruence | exact Hc ])).
      * introv Hl. apply indom_update_of_indom; (typeclass || applys HLC Hl).
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
    + splits*.
      introv Hl. simpls. rew_dom. rew_set in Hl. branches.
      * destruct (classic (l = l0)).
        -- subst. rewrite* read_update_same.
        -- rewrite* read_update_neq.
      * subst. rewrite* read_update_same.
  Unshelve. all: typeclass.
Qed.

(* Every graph x-writer [cx] is the commit produced by some flush at position [f']
   (so [cx = CH[f']], a commit event of its thread [tw']), and the flushed value
   came from an x-write at some earlier position [kw'] that was still uncommitted
   at [f'] -- no commit event of [tw'] occurs in [[kw', f')]. This is the inverse
   of [last_write_committed_or_delta], obtained by carrying the [delta_is_uncommitted_write]
   witness through the same case analysis as [graph_writes_log_write] while keeping
   the flush position. *)
Lemma graph_writes_flush :
  forall log D TC G LC CH cx x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    graph_writes G cx x v ->
    exists f' ef' tw' kw',
      LibList.Nth f' CH cx /\ LibList.Nth f' log ef' /\ get_thread ef' = tw' /\
      is_commit_event ef' /\ kw' < f' /\ LibList.Nth kw' log (event_write tw' x v) /\
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
                 is_commit_event ef' /\ kw' < f' /\ LibList.Nth kw' log (event_write tw' x v) /\
                 (forall p ep, kw' <= p -> p < f' -> LibList.Nth p log ep -> get_thread ep = tw' ->
                               ~ is_commit_event ep)) ->
              exists f' ef' tw' kw',
                LibList.Nth f' (CH & chx) cx /\
                LibList.Nth f' (log & Ex) ef' /\ get_thread ef' = tw' /\
                is_commit_event ef' /\ kw' < f' /\
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
    1,2,3: (applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R).
    + (* PlayEnd: graph_commit *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp ?dd) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          (match goal with
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
           | HbD : binds ?DD ?tt dd, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
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
    + (* PlayLockFresh: graph unchanged *)
      applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R.
Qed.

(* Graph edges only ever point to the freshly created commit, so ancestry follows
   creation order: a proper descendant of a commit born at [ka] (a commit event at
   [ka] with [CH[ka] = a]) is born strictly later. *)

(* The graph domain only grows along a play step. *)
Lemma play_event_graph_indom_mono :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' c,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    graph_indom G' c -> graph_indom G'' c.
Proof.
  introv Hpe Hin. inverts Hpe; try exact Hin;
    destruct G' as (C0 & P0); simpls; apply indom_update_of_indom; (exact Hin || typeclass).
Qed.

(* The commit produced by a commit event is fresh in the prefix graph and present
   in the new graph. *)
Lemma play_event_commit_new :
  forall E D' TC' G' LC' D'' TC'' G'' LC'',
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    is_commit_event E ->
    commit_fresh G' (TC''[get_thread E]) /\ graph_indom G'' (TC''[get_thread E]).
Proof.
  introv Hpe Hce. inverts Hpe; cbn [is_commit_event get_thread] in *; try contradiction;
    destruct G' as (C0 & P0).
  - rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - destruct (classic (t1 = t2)) as [Heqt | Hnet].
    + subst t2. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
    + rewrite read_update_neq; [ | congruence ]. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
Qed.

(* Ancestry into an old (prefix-domain) commit is unaffected by the freshly
   created commit, which is a sink: invert it back to the prefix graph. *)
Lemma play_event_ancestor_inv :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' a b,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    (forall x y, graph_edge G' x y -> graph_indom G' x /\ graph_indom G' y) ->
    graph_indom G' b ->
    ancestor G'' a b ->
    ancestor G' a b.
Proof.
  introv Hpe Hedge Hbdom Hanc. inverts Hpe; try exact Hanc;
    match goal with Hf : commit_fresh G' ?cf |- _ =>
      assert (Hsink: forall z, ancestor G' cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end;
    first [ applys ancestor_graph_commit_inv Hsink Hbne Hanc
          | applys ancestor_graph_merge_inv Hsink Hbne Hanc
          | applys ancestor_graph_root_inv Hsink Hbne Hanc].
Qed.

(* The commit recorded for a commit event lives in the graph domain. *)
Lemma CH_commit_event_indom :
  forall log D TC G LC CH k c e,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
   born at a commit event [ka] is itself born strictly later.  By induction on the
   replay: if the target [b] is the freshly created commit ([kb = length log]) then
   [a <> b] forces [ka < kb] directly.  Otherwise [b] is older and lives in the
   prefix graph, so the fresh commit (a sink) is not on any path into [b]; invert
   the ancestry to the prefix graph and apply the IH (the source [a] cannot be the
   fresh commit, as it is an ancestor source hence in the prefix domain). *)
Lemma ancestor_creation_order :
  forall log D TC G LC CH a b ka kb ea eb,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth ka CH a -> LibList.Nth ka log ea -> is_commit_event ea ->
    LibList.Nth kb CH b -> LibList.Nth kb log eb -> is_commit_event eb ->
    ancestor G a b -> a <> b ->
    ka < kb.
Proof.
  introv Hplay. gen a b ka kb ea eb.
  inductions Hplay; introv HNcha HNloga Hcea HNchb HNlogb Hceb Hanc Hneq.
  - forwards*: Nth_nil_inv HNcha.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (Hedge & _ & _).
    forwards [HNchb0 | (HkbN & Hcxb)]: Nth_last_inv HNchb.
    + (* b is an old commit, in the prefix graph *)
      forwards [HNlogb0 | (HkbN' & HeEb)]: Nth_last_inv HNlogb.
      2:{ forwards Hib: Nth_inbound HNchb0. nat_math. }
      forwards Hbdom: CH_commit_event_indom Hplay HNchb0 HNlogb0 Hceb.
      forwards Hanc': play_event_ancestor_inv Hpe Hedge Hbdom Hanc.
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
   [x].  Suppose [c' <> cs] is an x-writer below [cs].  By [graph_writes_flush] it
   is a flush at [f'] of some thread [tw'] fed by an x-write at [kw' <= m] with no
   [tw']-commit in [[kw', f')].  If [tw' = tm]: [c'] is a proper descendant of [cs]
   so (by [ancestor_creation_order]) [f < f'], but [f] is itself a [tm]-commit in
   [[kw', f')] -- contradiction.  If [tw' <> tm]: [conflict_free] orders the x-write
   at [kw' < m] before the one at [m] ([hb kw' m]); being cross-thread,
   [hb_cross_thread_flush] yields a [tw']-commit [f''] with [kw' <= f'' < m <= f < f'],
   again inside [[kw', f')] -- contradiction. *)
Lemma last_write_maximal :
  forall log D TC G LC CH m tm x vm f ef cs,
    conflict_free log ->
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    LibList.Nth f log ef -> get_thread ef = tm -> is_commit_event ef -> m <= f ->
    LibList.Nth f CH cs ->
    (forall g eg, m <= g -> g < f -> LibList.Nth g log eg -> get_thread eg = tm ->
                  ~ is_commit_event eg) ->
    graph_writes G cs x vm ->
    forall c' v', graph_writes G c' x v' -> ancestor G cs c' -> c' = cs.
Proof.
  intros log D TC G LC CH m tm x vm f ef cs.
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
    apply Hni. exact Hcfe.
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
    apply Hni. exact Hcef''.
Qed.

(* Existence + maximality: the last write of [x] is visible as the latest value at
   [n]'s thread's commit. [x \notindom D[tm]] gives the committed flush [cs = CH[f]]
   (via [last_write_committed_or_delta]); its ancestry to [TC[get_thread en]] uses
   [hb_cross_thread_flush] for the cross-thread case; its maximality is
   [last_write_maximal]. *)
Lemma last_write_visible_commit :
  forall log D TC G LC CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
            + applys HbPo HNf HNf' Hgf Hgf'. nat_math.
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
  forall log D TC G LC CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    conflict_free_graph G ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hcf Hcfg Hplay HNm Hlast Hndom HNn Hhb.
  applys (>> last_write_visible_commit Hwf Hcf Hplay HNm Hlast Hndom HNn Hhb).
Qed.

(* [is_latest_value] guarantees a committed x-write exists, hence the x-write
   filter of the log is non-empty. *)
Lemma is_latest_value_log_write :
  forall log D TC G LC CH c x v,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
  - rewrite Hnil in Hmemf. rewrite mem_nil_eq in Hmemf. destruct Hmemf.
  - asserts Hmx: (mem e (LibList.filter (fun e => writes_variable x e) log)).
    { rewrite Hsnoc. rewrite mem_last_eq. right. reflexivity. }
    forwards (Hmemx & Hwx): mem_filter_inv Hmx.
    destruct e as [s1 s2 | j1 j2 | rt ri rv | tt jj ww | lt ll | ut ul | stt | ett];
      simpls; tryfalse.
    subst jj. exists lw tt ww. exact Hsnoc.
Qed.

(* A play step never removes a thread from the delta map. *)
Lemma play_event_indom_D_mono :
  forall E D' TC' G' LC' D'' TC'' G'' LC'' t,
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    t \indom D' -> t \indom D''.
Proof.
  introv Hpe Hin. inverts Hpe; try assumption.
  - apply indom_update_of_indom; (typeclass || assumption).
  - apply indom_update_of_indom; (typeclass || assumption).
  - apply indom_update_of_indom;
      (typeclass || (apply indom_update_of_indom; (typeclass || assumption))).
  - apply indom_update_of_indom; (typeclass || assumption).
Qed.

(* A thread that performs a write event is in the delta map. *)
Lemma write_thread_in_delta :
  forall log s0 D TC G LC CH m tm x vm,
    play_log log s0 (D, TC, G, LC) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    tm \indom D.
Proof.
  introv Hplay. gen m tm x vm. inductions Hplay; introv HNlog.
  - inverts HNlog.
  - forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + forwards Hin: (>> IHHplay (eq_refl : (D', TC', G', LC') = (D', TC', G', LC')) HN0).
      applys play_event_indom_D_mono H Hin.
    + subst E. inverts H. apply indom_update_same; typeclass.
Qed.

(* The last writer of [x] has flushed it: its write happens-before an event of a
   different thread, so it must have committed (cf. [hb_preserves_thread]). *)
Lemma last_writer_not_in_delta :
  forall log D TC G LC CH m tm x vm n en,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
  apply Hgne. exact Hgteq.
Qed.

(* Global counterpart of [conflict_free_last_local_write]: when [t] reads [x]
   globally (it is not in [t]'s delta), the value [t] sees ([is_latest_value]) is
   the last write to [x] in the log. The read of [x=v] by [t] is included in the
   (tightened) conflict-free log, so it happens-after every x-write; combined with
   [hb_last_write_visible] this forces the last write's value to equal [v]. *)
Lemma conflict_free_last_global_write :
  forall log D TC G LC CH t x v c,
    conflict_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    conflict_free_graph G ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    TC[t] = c ->
    is_latest_value G c x v ->
    exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v.
Proof.
  introv Hcf Hwf Hcfg Hplay Hndom Hdom HTC Hval.
  (* [is_latest_value] ensures there is an x-write; take the last one. *)
  forwards (lw & tL & vL & Hfilter): is_latest_value_log_write Hplay Hval.
  forwards (L & HNL & Hlast): last_write_position Hfilter.
  forwards HLlt: Nth_inbound HNL.
  (* Play the read as a no-op, and place the write and the read in [log & read]. *)
  asserts Hplayf: (exists CHf, play_log (log & event_read t x v) init_play_cfg (D, TC, G, LC) CHf).
  { eexists. applys PlaySnoc Hplay. apply PlayRead. }
  destruct Hplayf as (CHf & Hplayf).
  asserts HNLf: (LibList.Nth L (log & event_read t x v) (event_write tL x vL)).
  { applys* Nth_app_l. }
  asserts HNread: (LibList.Nth (length log) (log & event_read t x v) (event_read t x v)).
  { applys* Nth_app_r'. }
  asserts Hlastf:
    (forall k tk vk, LibList.Nth k (log & event_read t x v) (event_write tk x vk) -> k <= L).
  { introv HNk. forwards [HN' | (Hpe & Hee)]: Nth_last_inv HNk.
    - applys Hlast HN'.
    - inverts Hee. }
  (* conflict-freedom: the last write happens-before the read. *)
  asserts Hacc: (accesses_variable x (event_read t x v)). { reflexivity. }
  forwards Hhb: Hcf HNLf HNread Hacc HLlt.
  (* the last writer has flushed [x]. *)
  asserts HndomL: (x \notindom (D[tL])).
  { destruct (classic (tL = t)) as [-> | Hne].
    - exact Hndom.
    - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb.
      simpl. congruence. }
  (* the bridge: [vL] is the latest value [t] sees, which is [v]. *)
  forwards Hlv: (>> hb_last_write_visible Hwf Hcf Hcfg Hplayf HNLf Hlastf HndomL HNread Hhb).
  simpl in Hlv. rewrite HTC in Hlv.
  forwards ->: is_latest_value_inj Hcfg Hlv Hval.
  exists tL lw. exact Hfilter.
Qed.

(* The bridge from log happens-before to graph ancestry between flush commits:
   if [ta]'s write at [ka] (flushed into [ha] at [fa], with no [ta]-commit in
   [[ka, fa)]) happens-before [tb]'s write at [kb] (flushed into [hbb] at [fb]),
   and the threads differ, then [ha] is an ancestor of [hbb].  The crossing flush
   from [hb_cross_thread_flush] lands at or after [fa] and reaches [kb], and
   [CH_thread_monotone] carries [ha] down to it and [kb] up to [hbb]. *)
Lemma write_hb_flush_ancestor :
  forall log D TC G LC CH ta tb x va vb ka fa ea ha kb fb eb hbb,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    (LibList.Nth ka log (event_write ta x va) /\ LibList.Nth fa CH ha /\
       LibList.Nth fa log ea /\ get_thread ea = ta /\ is_commit_event ea /\ ka < fa /\
       (forall p ep, ka <= p -> p < fa -> LibList.Nth p log ep -> get_thread ep = ta ->
                     ~ is_commit_event ep)) ->
    (LibList.Nth kb log (event_write tb x vb) /\ LibList.Nth fb CH hbb /\
       LibList.Nth fb log eb /\ get_thread eb = tb /\ is_commit_event eb /\ kb < fb) ->
    ta <> tb ->
    hb log ka kb ->
    ancestor G ha hbb.
Proof.
  intros log D TC G LC CH ta tb x va vb ka fa ea ha kb fb eb hbb.
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

(* A data-race-free log replays to a conflict-free commit graph.
   Two incomparable x-writers in the graph would each have a feeding log write
   ([graph_writes_flush]); [conflict_free] orders those writes by [hb], and
   [write_hb_flush_ancestor] then forces the two writer commits to be
   ancestor-comparable -- contradiction. *)
Theorem conflict_free_log_describes_conflict_free_graph :
  forall log D TC G LC CH,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
  { forwards (fa & ea & ta & ka & HNfaCH & HNfalog & Hgta & Hcea & Hkalt & HNka & Hncla):
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
      + asserts Hacc: (accesses_variable x (event_write tb x (C[hbb][x]))). reflexivity.
        forwards Hhbab: (>> Hcf HNka HNkb Hacc Hlt).
        left.
        applys (>> write_hb_flush_ancestor Hwf Hplay
          (conj HNka (conj HNfaCH (conj HNfalog (conj Hgta (conj Hcea (conj Hkalt Hncla))))))
          (conj HNkb (conj HNfbCH (conj HNfblog (conj Hgtb (conj Hceb Hkblt)))))
          Htne Hhbab).
      + asserts Hltba: (kb < ka). nat_math.
        asserts Hacc: (accesses_variable x (event_write ta x (C[ha][x]))). reflexivity.
        forwards Hhbba: (>> Hcf HNkb HNka Hacc Hltba).
        right. asserts Htne2: (tb <> ta). { intros HH. apply Htne. symmetry. exact HH. }
        applys (>> write_hb_flush_ancestor Hwf Hplay
          (conj HNkb (conj HNfbCH (conj HNfblog (conj Hgtb (conj Hceb (conj Hkblt Hnclb))))))
          (conj HNka (conj HNfaCH (conj HNfalog (conj Hgta (conj Hcea Hkalt)))))
          Htne2 Hhbba). }
  destruct Hcmp as [Hc | Hc].
  - applys Hnanca2. applys ancestor_trans Hc Hancb2.
  - applys Hnancb1. applys ancestor_trans Hc Hanca1.
Qed.

(* A graph commit [c] that writes a variable [j] still uncommitted by a thread [t]
   must be an ancestor of [t]'s commit [TC[t]].  Otherwise [t]'s pending write to
   [j] and [c]'s committed write to [j] would be two writes to the same variable
   that are not happens-before related -- a data race, which [conflict_free]
   forbids.  (Structurally this mirrors [write_hb_flush_ancestor], but the [t]
   side of the race is a pending delta write rather than a flushed one.) *)
Lemma delta_writer_ancestor :
  forall log D TC G LC CH t j vt c vc,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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

(* The merge obligation discharged: when a running thread [t] (pending delta
   [D[t]], commit [TC[t]]) merges with another commit [hc], the merge is
   conflict-free.  The [change_set]/[change_set] half is the keystone
   ([conflict_free_log_describes_conflict_free_graph]); the [dom (D[t])] half is
   [delta_writer_ancestor] (no pending write of [t] can sit in the change set
   merged in from [hc]). *)
Lemma conflict_free_merge_holds :
  forall log D TC G LC CH t hc,
    wf_log log ->
    conflict_free log ->
    play_log log init_play_cfg (D, TC, G, LC) CH ->
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
