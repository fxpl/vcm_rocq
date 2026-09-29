From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Linear.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingLinear.
From Vcm Require Import LoggingLinearFacts.

Import Graph.
Import GraphFacts.
Import Linear.
Import Log.
Import LogFacts.
Import LoggingLinear.

Existing Instance inhab_val.
Existing Instance inhab_exp.

(* A value sitting in a thread's local diff comes from a write by that thread
   that it has not yet committed: there is an [event_write t x v] in the log
   after which [t] performs no commit event. *)
Lemma delta_is_uncommitted_write :
  forall log D TC G g CH t x v,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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
    forwards* Heq: binds_empty_false Hbinds.
  - (* PlaySnoc *)
    inverts H.
    + (* PlayRead *)
      forwards* (wm & wHN & wHns): IHHplay.
      exists wm. split;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto ].
    + (* PlayReadVolatile: D unchanged (same as PlayRead) *)
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
          match goal with H : binds D' t0 d |- _ => rename H into HbindsDd end.
          lets Hin: (indom_of_binds HbindsDd).
          asserts Hb': (binds (D'[t0]) x v). { forwards: read_of_binds HbindsDd. subst*. }
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
    + (* PlayWriteVolatile (event_write t0 x0 v0): flushes D[t0] (immediately
         committed, same as PlayEnd/PlayUnlock) *)
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

(* When replaying a race-free log, every value in a thread's local diff is
   the last write of that variable in the whole log. *)
Lemma race_free_last_local_write :
  forall log D TC G g CH t x v,
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t x v.
Proof.
  introv Hrf Hplay Hdom Hdelta.
  hint race_free_last_inv.
  inductions Hplay.
  - rew_dom. rew_set in Hdom.
    branches;
      [forwards*: indom_empty_inv|].
    subst.
    rewrite read_update_same in Hdelta.
    forwards* Heq: binds_empty_false Hdelta.
  - inverts H.
    + (* PlayRead *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayReadVolatile: D unchanged (same as PlayRead) *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayWrite *)
      destruct (classic (t = t0)).
      * subst. rewrite read_update_same in Hdelta.
        destruct (classic (x = x0)).
        -- subst.
           forwards ->: binds_update_same_inv Hdelta.
           exists. rew_listx*. cases_if*.
        -- forwards~ Hdelta': binds_update_neq_inv Hdelta.
           match goal with H : binds D' t0 d |- _ => rename H into HbindsDd end.
           asserts Hbinds: (binds D'[t0] x v).
           { forwards : read_of_binds HbindsDd. subst*. }
           forwards* (log' & Hfilter): IHHplay.
           exists log'. rew_listx. cases_if. rew_list*.
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
           forwards Hhb: Hrf HN0f Hnth Hacc Hlt0.
           asserts Hns0f:
             (forall p ep, m0 <= p ->
                LibList.Nth p (log & event_write t0 x0 v0) ep ->
                get_thread ep = t -> ~ is_commit_event ep).
           { applys no_commit_event_snoc Hns0. intros _; simpl; auto. }
           asserts Hem: (get_thread (event_write t x0 v) = t). { reflexivity. }
           forwards Hgt0: hb_preserves_thread Hhb HN0f Hem Hns0f Hnth.
           simpl in Hgt0. congruence.
        -- rew_list*.
    + (* PlayWriteVolatile (event_write t0 x0 v0): flushes D[t0] ENTIRELY (the
         just-written value is committed, not kept locally, unlike PlayWrite) *)
      destruct (classic (t = t0)).
      * (* t = t0: D[t0] just got flushed to empty *)
        subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta). forwards*: indom_empty_inv.
      * (* t <> t0 *)
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
           forwards Hhb: Hrf HN0f Hnth Hacc Hlt0.
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
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayEnd *)
      asserts Hneq: (t <> t0).
      { intros contra. subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlaySpawn *)
      asserts Hneq2: (t <> t2).
      { intros contra. subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hdelta.
      asserts Hneq1: (t <> t1).
      { intros contra. subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. repeat (branches; [|congruence]).
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayJoin *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayLock *)
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
    + (* PlayUnlock *)
      asserts Hneq: (t <> t0).
      { intros contra. subst. rewrite read_update_same in Hdelta.
        forwards contra: (indom_of_binds Hdelta). forwards*: indom_empty_inv. }
      rewrite~ read_update_neq in Hdelta.
      rew_dom. rew_set in Hdom. inverts Hdom; [|congruence].
      forwards* (log' & Hfilter): IHHplay.
      exists log'. rew_listx. cases_if. rew_list*.
Qed.

(* In a totally ordered graph (such as the Linear single-branch graph) any two
   commits are ancestor-comparable, so one of the two one-directional change sets
   is always empty.  Hence the graph is automatically conflict free, and we avoid
   the heavy [race_free_log_describes_conflict_free_graph] argument that the
   Branching development needs. *)
Lemma total_order_conflict_free_graph :
  forall G,
    total_order G ->
    conflict_free_graph G.
Proof.
  introv Htot. introv Hd1 Hd2.
  unfold conflict_free_merge. rew_set. intros x Hin1 Hin2.
  rew_set in Hin1. destruct Hin1 as [Hde | Hcs1].
  { applys indom_empty_inv Hde. }
  destruct G as (C & P).
  unfold change_set in Hcs1, Hin2.
  destruct Hcs1 as (ha & Hidoma & Hanca1 & Hnanca2).
  destruct Hin2 as (hbb & Hidomb & Hancb2 & Hnancb1).
  forwards [Hc12 | Hc21]: Htot Hd1 Hd2.
  - apply Hnanca2. applys ancestor_trans Hanca1 Hc12.
  - apply Hnancb1. applys ancestor_trans Hancb2 Hc21.
Qed.

(* A play step never removes a thread from the delta map (flushes set it to
   [empty], which keeps the key in the domain). *)
Lemma play_event_indom_D_mono :
  forall E D' TC' G' g' D'' TC'' G'' g'' t,
    play_event E (D', TC', G', g') (D'', TC'', G'', g'') ->
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
  forall log s0 D TC G g CH m tm x vm,
    play_log log s0 (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    tm \indom D.
Proof.
  introv Hplay. gen m tm x vm. inductions Hplay; introv HNlog.
  - inverts HNlog.
  - forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNlog.
    + forwards Hin: (>> IHHplay (eq_refl : (D', TC', G', g') = (D', TC', G', g')) HN0).
      applys play_event_indom_D_mono H Hin.
    + subst E. inverts H; apply indom_update_same; typeclass.
Qed.

(* The last writer of [x] has flushed it: its write happens-before an event of a
   different thread, so it must have committed (cf. [hb_preserves_thread] and the
   uncommitted-write characterisation). *)
Lemma last_writer_not_in_delta :
  forall log D TC G g CH m tm x vm n en,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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

Hint Extern 1 (Inhab _) => typeclass : vcm.


(* Head invariant for a Linear play state: the graph is totally ordered, every
   commit is an ancestor of the head [g], and every thread pointer is below the
   head.  Linear never merges, so the "pointer advances to a descendant" fact
   that Branching reads off merge edges here follows from "everything is below
   the head". *)
Definition play_state_inv (TC : commits) (G : graph) (g : commit) : Prop :=
  total_order G /\
  (forall c, graph_indom G c -> ancestor G c g) /\
  (forall t, t \indom TC -> ancestor G (TC[t]) g).

(* A single play step preserves the head invariant. *)
Lemma play_event_preserves_inv :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    play_state_inv TCp Gp gp ->
    play_state_inv TC G g.
Proof.
  introv Hpe Hinv'.
  destruct Hinv' as (Htot' & Hmax' & Hptr').
  inverts Hpe.
  - (* PlayRead *) exact (conj Htot' (conj Hmax' Hptr')).
  - (* PlayReadVolatile: TCp[t := gp], graph unchanged (same as PlayStart) *)
    unfold play_state_inv. splits; [ exact Htot' | exact Hmax' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. apply ancestor_refl.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys Hptr' Hin.
  - (* PlayWrite *) exact (conj Htot' (conj Hmax' Hptr')).
  - (* PlayWriteVolatile: graph_commit, head gp -> g', TCp[t := g'] (same as PlayEnd/PlayUnlock) *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    unfold play_state_inv. splits.
    + applys total_order_commit Htot' Hmax' Hfresh.
    + intros c Hc. applys max_ancestor_commit Hmax' Hfresh Hc.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. apply ancestor_refl.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys ancestor_trans.
        -- applys ancestor_graph_commit. applys Hptr' Hin.
        -- applys ancestor_graph_commit_edge.
  - (* PlayStart: TCp[t := gp], graph unchanged *)
    unfold play_state_inv. splits; [ exact Htot' | exact Hmax' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. apply ancestor_refl.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys Hptr' Hin.
  - (* PlayEnd: graph_commit, head gp -> g', TCp[t := g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    unfold play_state_inv. splits.
    + applys total_order_commit Htot' Hmax' Hfresh.
    + intros c Hc. applys max_ancestor_commit Hmax' Hfresh Hc.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. apply ancestor_refl.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys ancestor_trans.
        -- applys ancestor_graph_commit. applys Hptr' Hin.
        -- applys ancestor_graph_commit_edge.
  - (* PlaySpawn: graph_commit, head gp -> g', TCp[t1:=g'][t2:=g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    unfold play_state_inv. splits.
    + applys total_order_commit Htot' Hmax' Hfresh.
    + intros c Hc. applys max_ancestor_commit Hmax' Hfresh Hc.
    + intros tq Htq. destruct (classic (tq = t2)) as [->|Hne2].
      * (* the spawned thread points at the old head [gp], an ancestor of [g'] *)
        rewrite read_update_same. applys ancestor_refl.
      * rewrite read_update_neq; auto.
        destruct (classic (tq = t1)) as [->|Hne1].
        -- rewrite read_update_same. apply ancestor_refl.
        -- rewrite read_update_neq; auto.
           asserts Hin: (tq \indom TCp).
           { asserts Ho2: (tq = t2 \/ tq \indom (TCp[t1 := g])). { applys* indom_update_inv Htq. }
             destruct Ho2 as [Heq|Hin2]; [congruence|].
             asserts Ho1: (tq = t1 \/ tq \indom TCp). { applys* indom_update_inv Hin2. }
             destruct Ho1 as [Heq|Hin1]; [congruence|exact Hin1]. }
           applys ancestor_trans.
           ++ applys ancestor_graph_commit. applys Hptr' Hin.
           ++ applys ancestor_graph_commit_edge.
  - (* PlayJoin: TCp[t1 := gp], graph unchanged *)
    unfold play_state_inv. splits; [ exact Htot' | exact Hmax' | ].
    intros tq Htq. destruct (classic (tq = t1)) as [->|Hne].
    + rewrite read_update_same. apply ancestor_refl.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t1 \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys Hptr' Hin.
  - (* PlayLock: TCp[t := gp], graph unchanged *)
    unfold play_state_inv. splits; [ exact Htot' | exact Hmax' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. apply ancestor_refl.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys Hptr' Hin.
  - (* PlayUnlock: graph_commit, head gp -> g', TCp[t := g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    unfold play_state_inv. splits.
    + applys total_order_commit Htot' Hmax' Hfresh.
    + intros c Hc. applys max_ancestor_commit Hmax' Hfresh Hc.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. apply ancestor_refl.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys ancestor_trans.
        -- applys ancestor_graph_commit. applys Hptr' Hin.
        -- applys ancestor_graph_commit_edge.
Qed.

Lemma play_log_inv :
  forall log D TC G g CH,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    play_state_inv TC G g.
Proof.
  introv Hplay.
  inductions Hplay.
  - (* PlayNil *)
    unfold play_state_inv. splits.
    + intros a b Ha Hb. unfolds graph_indom, graph_root. rew_dom.
      rew_set in *. repeat branches; try solve[forwards*: indom_empty_inv].
      subst*.
    + intros c Hc. unfolds graph_indom, graph_root. rew_dom.
      rew_set in *. branches; try solve[forwards*: indom_empty_inv].
      subst*.
    + intros t Ht. rew_dom. rew_set in *. branches; try solve[forwards*: indom_empty_inv].
      subst. rewrite* read_update_same.
  - (* PlaySnoc *)
    forwards~ Hinv': IHHplay.
    applys* play_event_preserves_inv H.
Qed.

(* ============================================================================
   Bridge from the commit graph to the log, for the global-read soundness lemma
   [race_free_last_global_write].  Dependency order (Linear adaptations of
   the LoggingBranchingFacts cluster; Linear has no merges, so several merge
   arguments collapse and [play_log_inv] replaces [play_log_graph_wf]'s ancestry
   facts).  Stubs first; proofs filled in below where done.
   ============================================================================ *)

(* [1] CH is parallel to the log. *)
Lemma play_log_CH_length :
  forall log s0 sf CH,
    play_log log s0 sf CH ->
    length CH = length log.
Proof. introv Hplay. induction Hplay; rew_list*. Qed.

(* [2] A play step only grows the graph: existing ancestry is preserved.
   Linear only ever [graph_commit]s or [graph_root]s (no merges). *)
Lemma play_event_graph_extends :
  forall E D' TC' G' g' D'' TC'' G'' g'' x y,
    play_event E (D', TC', G', g') (D'', TC'', G'', g'') ->
    ancestor G' x y ->
    ancestor G'' x y.
Proof.
  introv Hpe Hanc.
  inverts Hpe; auto using ancestor_graph_commit.
Qed.

(* [3] After a play step a thread's pointer advances to a descendant.  For
   sync events (start/join/lock) Linear keeps the graph fixed and sets the
   pointer to the head [g'], so this needs [play_state_inv] (everything is below
   the head) rather than Branching's merge edges. *)
Lemma play_event_TC_advance :
  forall E Dp TCp Gp gp D TC G g t,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    play_state_inv TCp Gp gp ->
    t \indom TCp ->
    (forall t1 t2, E = event_spawn t1 t2 -> t <> t2) ->
    ancestor G (TCp[t]) (TC[t]).
Proof.
  introv Hpe Hinv Htin Hspawn.
  destruct Hinv as (Htot & Hmax & Hptr).
  inverts Hpe.
  - (* PlayRead *) apply ancestor_refl.
  - (* PlayReadVolatile: TCp[t0 := gp], graph unchanged (same as PlayStart) *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same. applys Hptr Htin.
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayWrite *) apply ancestor_refl.
  - (* PlayWriteVolatile: graph_commit, TCp[t0 := g'] (same as PlayEnd) *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same.
      applys ancestor_trans;
        [ applys ancestor_graph_commit; applys Hptr Htin | applys ancestor_graph_commit_edge ].
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayStart *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same. applys Hptr Htin.
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayEnd *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same.
      applys ancestor_trans;
        [ applys ancestor_graph_commit; applys Hptr Htin | applys ancestor_graph_commit_edge ].
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlaySpawn *)
    forwards Hne2: Hspawn t1 t2; [ reflexivity | ].
    destruct (classic (t = t1)) as [->|Hne1].
    + rewrite read_update_neq; auto. rewrite read_update_same.
      applys ancestor_trans;
        [ applys ancestor_graph_commit; applys Hptr Htin | applys ancestor_graph_commit_edge ].
    + rewrite read_update_neq; auto. rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayJoin *)
    destruct (classic (t = t1)) as [->|Hne].
    + rewrite read_update_same. applys Hptr Htin.
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayLock *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same. applys Hptr Htin.
    + rewrite read_update_neq; auto. apply ancestor_refl.
  - (* PlayUnlock *)
    destruct (classic (t = t0)) as [->|Hne].
    + rewrite read_update_same.
      applys ancestor_trans;
        [ applys ancestor_graph_commit; applys Hptr Htin | applys ancestor_graph_commit_edge ].
    + rewrite read_update_neq; auto. apply ancestor_refl.
Qed.

Lemma play_log_indom_TC :
  forall log D' TC' G' g' CH m em,
    wf_log log ->
    play_log log init_play_cfg (D', TC', G', g') CH ->
    LibList.Nth m log em ->
    get_thread em \indom TC'.
Proof.
  introv Hwf Hplay Hnth. gen m em.
  inductions Hplay; introv Hnth.
  - forwards*: Nth_nil_inv.
  - forwards~ Hdisj: Nth_last_inv Hnth.
    forwards~ Hwf': wf_log_last_inv Hwf.
    inverts H;
      try (rew_dom; rew_set; branches;
        [forwards*: IHHplay| unpack; subst; simpls*]).
    + asserts (n & Hnth'): (exists n, LibList.Nth n log (event_start t)).
      {
        lets (_ & _ & _ & _ & Hstart & _): Hwf.
        forwards* Hmem: Hstart log (@nil event) (event_read t x v) t.
        apply* mem_Nth.
      }
      forwards*: IHHplay.
    + asserts (n & Hnth'): (exists n, LibList.Nth n log (event_start t)).
      {
        lets (_ & _ & _ & _ & Hstart & _): Hwf.
        forwards* Hmem: Hstart log (@nil event) (event_write t x v) t.
        apply* mem_Nth.
      }
      forwards*: IHHplay.
Qed.

(* [4] The commit pointer recorded for an event is an ancestor of the thread's
   final pointer (pointers only advance). *)
Lemma CH_ancestor_TC :
  forall log D TC G g CH m em t cm,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
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
      forwards~ Hanc: IHHplay Hwf0 HN0 Hgt HN0ch.
      apply ancestor_trans with (c' := TC'[t]).
      * eapply play_event_graph_extends; eassumption.
      * applys play_event_TC_advance; [ eassumption | | |].
        -- applys* play_log_inv.
        -- subst. applys* play_log_indom_TC.
        -- introv Heq. subst E.
           forwards Hne: spawned_thread_no_prior_event Hwf HN0.
           congruence.
    + (* last event = E *)
      subst em.
      forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
      { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
      subst cm. rewrite Hgt. apply ancestor_refl.
Qed.


(* [5] A cross-thread happens-before edge passes through a commit event of the
   source thread.  Log-only (no graph); a verbatim port. *)
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
    [ p q e1 e2 HN1 HN2 Hg1 Hg2 Hlt
    | q p lt1 lt2 ll HNsrc HNtgt Hlt
    | p q st1 st2 HNsrc HNtgt Hlt
    | p q jt1 jt2 HNsrc HNtgt Hlt
    | p q vt1 vt2 vx vv vv' Hxvol HNsrc HNtgt Hlt
    | p q k Hpk IHpk Hkq IHkq ];
    introv Hm Hgt Hn Hgne.
  - forwards Heq1: Nth_functional Hm HN1. forwards Heq2: Nth_functional Hn HN2.
    exfalso. apply Hgne. congruence.
  - forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_unlock lt1 ll). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbLock HNsrc HNtgt Hlt.
  - forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_spawn st1 st2). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbSpawn HNsrc HNtgt Hlt.
  - forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_end jt2). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact I.
    + applys HbJoin HNsrc HNtgt Hlt.
  - forwards Heq: Nth_functional Hm HNsrc. subst em.
    exists p (event_write vt1 vx vv). splits.
    + nat_math. + exact HNsrc. + simpls; exact Hgt. + simpl; exact Hxvol.
    + applys HbVolatile Hxvol HNsrc HNtgt Hlt.
  - forwards (ek & HNk): hb_Nth_r Hpk.
    forwards Hltpk: hb_lt Hpk.
    destruct (classic (get_thread ek = t)) as [Hgek | Hgek].
    + forwards (f & ef & Hkf & HNf & Hgf & Hcf & Hhbf): IHkq HNk Hgek Hn Hgne.
      exists f ef. splits; try assumption. nat_math.
    + forwards (f & ef & Hpf & HNf & Hgf & Hcf & Hhbf): IHpk Hm Hgt HNk Hgek.
      exists f ef. splits; try assumption. applys HbTrans Hhbf Hkq.
Qed.

(* [6] hb_pointer_ancestor is proved further down, after the [10] machinery
   (it depends on CH_commit_event_indom). *)

(* [7] Every write recorded in the graph comes from a write event in the log. *)
Lemma graph_writes_log_write :
  forall log D TC G g CH cx x v,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    graph_writes G cx x v ->
    exists tw m, LibList.Nth m log (event_write tw x v).
Proof.
  introv Hplay. gen cx x v. inductions Hplay; introv Hgw.
  - destruct Hgw as (dd & Hgb & Hbd). simpls.
    destruct (classic (cx = root_commit)).
    + subst.
      forwards Hbinds: binds_update_same_inv Hgb.
      subst.
      forwards* Heq: binds_empty_false Hbd.
    + forwards~ Hbinds: binds_update_neq_inv Hgb.
      forwards* Heq: binds_empty_false Hbinds.
  - rename H into Hpe.
    inverts Hpe.
    (* PlayRead/ReadVolatile/Write/Start/Join/Lock: graph unchanged *)
    1,2,3,5,8,9: (forwards* (tw & m0 & HN): IHHplay;
                exists tw m0; rew_list; applys Nth_app_l HN).
    + (* PlayWriteVolatile: graph_commit of (d0[x0 := v0]) -- either [x] IS the
         just-written variable [x0] (this event is directly the witness) or
         it comes from [d0] via [delta_is_uncommitted_write] (same as PlayEnd) *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp (?dd0[?xx0 := ?vv0])) _ _ _ =>
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          destruct (classic (x = xx0)) as [Hxeq | Hxneq];
          [ subst xx0;
            forwards ->: binds_update_same_inv Hbdd;
            (match goal with |- exists tw m, LibList.Nth m (?lg & event_write ?tt _ _) _ =>
              exists tt (length lg) end);
            applys* Nth_app_r'
          | forwards Hbdd': binds_update_neq_inv Hbdd Hxneq;
            (match goal with
             | HbD : binds ?DD ?tt dd0, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
              lets HtD: (indom_of_binds HbD);
              lets Hrd: (read_of_binds HbD);
              rewrite <- Hrd in Hbdd';
              forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd';
              exists tt m'; rew_list; applys Nth_app_l HNm'
             end) ]
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          forwards* (tw & m0 & HN): IHHplay;
          exists tw m0; rew_list; applys Nth_app_l HN ]
      end.
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
Qed.

(* [8] [is_latest_value] guarantees the x-write filter of the log is non-empty. *)
Lemma is_latest_value_log_write :
  forall log D TC G g CH c x v,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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

(* [9] Each graph write has a feeding flush: the commit [cx] is created by a
   commit event in the log flushing a delta whose last write of [x] is [v].
   [kw' <= f'] (weakened from [<], harmlessly: no caller inspects this fact
   directly) accommodates [PlayWriteVolatile], where the write and its commit
   are the SAME log event ([kw' = f']) -- unlike every other commit event,
   which flushes writes staged in an EARLIER, separate event. *)
Lemma graph_writes_flush :
  forall log D TC G g CH cx x v,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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
      forwards* Heq: binds_empty_false Hbd.
    + forwards~ Hbinds: binds_update_neq_inv Hgb.
      forwards* Heq: binds_empty_false Hbinds.
  - rename H into Hpe.
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
    (* PlayRead/ReadVolatile/Write/Start/Join/Lock: graph unchanged *)
    1,2,3,5,8,9: (applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R).
    + (* PlayWriteVolatile: graph_commit of (d0[x0 := v0]) -- the write and its
         commit COINCIDE in one event ([kw' = f' = length log]) when [x = x0];
         otherwise same as PlayEnd via [delta_is_uncommitted_write] *)
      match type of Hgw with
      | graph_writes (graph_commit _ _ ?ccp (?dd0[?xx0 := ?vv0])) _ _ _ =>
        match goal with H : xx0 \in Volatiles |- _ => rename H into Hxvol0 end;
        destruct (classic (cx = ccp)) as [Hc | Hc];
        [ subst cx;
          forwards Hbdd: graph_writes_graph_commit_same Hgw;
          destruct (classic (x = xx0)) as [Hxeq | Hxneq];
          [ subst xx0;
            forwards ->: binds_update_same_inv Hbdd;
            (match goal with Hp : play_log _ _ _ _ |- _ => forwards Hlen: play_log_CH_length Hp end);
            exists (length log) (event_write t x vv0) t (length log); splits;
            [ cbn [get_thread]; rewrite read_update_same;
              applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | reflexivity
            | simpl; exact Hxvol0
            | nat_math
            | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
            | introv Hp0 Hpf HNp Hgp; nat_math ]
          | forwards Hbdd': binds_update_neq_inv Hbdd Hxneq;
            (match goal with
             | HbD : binds ?DD ?tt dd0, Hp : play_log _ _ (?DD, _, _, _) _ |- _ =>
              lets HtD: (indom_of_binds HbD);
              lets Hrd: (read_of_binds HbD);
              rewrite <- Hrd in Hbdd';
              forwards (m' & HNm' & Hns'): delta_is_uncommitted_write Hp HtD Hbdd';
              forwards Hlen: play_log_CH_length Hp;
              forwards Hib': Nth_inbound HNm';
              exists (length log) (event_write t xx0 vv0) tt m'; splits;
              [ cbn [get_thread]; rewrite read_update_same;
                applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
              | applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]
              | reflexivity
              | simpl; exact Hxvol0
              | nat_math
              | applys Nth_app_l HNm'
              | introv Hp0 Hpf HNp Hgp;
                forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
                [ applys Hns' Hp0 HNp0 Hgp | nat_math ] ]
             end) ]
        | forwards Hgw': graph_writes_graph_commit_inv Hc Hgw;
          applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R ]
      end.
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
Qed.

(* --- [10] machinery --- *)

(* graph_indom is preserved by a play step. *)
Lemma play_event_graph_indom_mono :
  forall E D' TC' G' g' D'' TC'' G'' g'' c,
    play_event E (D', TC', G', g') (D'', TC'', G'', g'') ->
    graph_indom G' c -> graph_indom G'' c.
Proof.
  introv Hpe Hin. inverts Hpe; try assumption;
    [ applys graph_commit_indom Hin
    | applys graph_commit_indom Hin
    | applys graph_commit_indom Hin
    | applys graph_commit_indom Hin
    ].
Qed.

(* Auxiliary invariant: graph edges land in the domain, and (until the very first
   event, when [D] is still empty) the head [g] is in the graph.  The [D = empty]
   escape is self-maintaining: every commit/write step has a [binds D ...] premise
   that rules it out, so no [wf_log] is needed. *)
Definition play_graph_wf (D : deltas) (G : graph) (g : commit) : Prop :=
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) /\
  (D = empty \/ graph_indom G g).

Lemma play_event_preserves_graph_wf :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    play_graph_wf Dp Gp gp ->
    play_graph_wf D G g.
Proof.
  introv Hpe Hwf. destruct Hwf as (Hedge & Hdisj).
  inverts Hpe.
  (* Read/ReadVolatile/Write/Start/Join/Lock: graph unchanged *)
  1,2,3,5,8,9: (split;
    [ exact Hedge
    | destruct Hdisj as [HDe | Hgi];
      [ try (left; assumption);
        subst Dp; exfalso;
        match goal with HbD : binds empty _ _ |- _ => applys binds_empty_false HbD; typeclass end
      | right; exact Hgi ] ]).
  (* WriteVolatile/End/Spawn/Unlock: graph_commit *)
  1,2,3,4: (
    destruct Gp as (C0 & P0);
    asserts Hgpd: (graph_indom (C0, P0) gp);
    [ destruct Hdisj as [HDe | Hgi];
      [ subst Dp; exfalso;
        match goal with HbD : binds empty _ _ |- _ => applys binds_empty_false HbD; typeclass end
      | exact Hgi ]
    | ];
    split;
    [ introv He; unfold graph_edge, graph_commit in He; rew_set in He; destruct He as [He | He];
      [ inverts He; split; [ applys graph_commit_indom Hgpd | applys graph_commit_indom_same ]
      | forwards (Ha & Hb): Hedge He; split; applys graph_commit_indom; assumption ]
    | right; applys graph_commit_indom_same ]).
Qed.

Lemma play_log_graph_wf :
  forall log D TC G g CH,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    play_graph_wf D G g.
Proof.
  introv Hplay. inductions Hplay.
  - split.
    + introv He. unfold graph_edge, empty_graph in He. rew_set in He. false.
    + right. applys* graph_root_indom_same.
  - forwards* Hwf': IHHplay.
    applys play_event_preserves_graph_wf H Hwf'.
Qed.

(* The fresh commit of a commit event is recorded as that thread's new pointer
   and is in the new graph. *)
Lemma play_event_commit_new :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    is_commit_event E ->
    commit_fresh Gp (TC[get_thread E]) /\ graph_indom G (TC[get_thread E]).
Proof.
  introv Hpe Hce. inverts Hpe; cbn [is_commit_event get_thread] in *; try contradiction;
    destruct Gp as (C0 & P0).
  - (* PlayWriteVolatile: same shape as PlayEnd/PlayUnlock *)
    rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - destruct (classic (t1 = t2)) as [Heqt | Hnet].
    + subst t2. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
    + rewrite read_update_neq; [ | congruence ]. rewrite read_update_same.
      split; [ assumption | simpls; apply indom_update_same; typeclass ].
  - rewrite read_update_same. split; [ assumption | simpls; apply indom_update_same; typeclass ].
Qed.

(* Ancestry into an already-existing commit does not use the freshly added edge. *)
Lemma play_event_ancestor_inv :
  forall E Dp TCp Gp gp D TC G g a b,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    (forall x y, graph_edge Gp x y -> graph_indom Gp x /\ graph_indom Gp y) ->
    graph_indom Gp b ->
    ancestor G a b ->
    ancestor Gp a b.
Proof.
  introv Hpe Hedge Hbdom Hanc. inverts Hpe; try exact Hanc;
    match goal with Hf : commit_fresh Gp ?cf |- _ =>
      assert (Hsink: forall z, ancestor Gp cf z -> z = cf) by (applys commit_fresh_sink Hedge Hf);
      assert (Hbne: b <> cf) by (intro Heq; subst b; applys commit_fresh_not_indom Hf Hbdom)
    end;
    first [ applys ancestor_graph_commit_inv Hsink Hbne Hanc
          | applys ancestor_graph_root_inv Hsink Hbne Hanc].
Qed.

(* The [CH] entry of a commit event is in the graph's domain. *)
Lemma CH_commit_event_indom :
  forall log D TC G g CH k c e,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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

(* [10] Commit order in the graph follows position order in [CH]. *)
Lemma ancestor_creation_order :
  forall log D TC G g CH a b ka kb ea eb,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth ka CH a -> LibList.Nth ka log ea -> is_commit_event ea ->
    LibList.Nth kb CH b -> LibList.Nth kb log eb -> is_commit_event eb ->
    ancestor G a b -> a <> b ->
    ka < kb.
Proof.
  introv Hplay. gen a b ka kb ea eb.
  inductions Hplay; introv HNcha HNloga Hcea HNchb HNlogb Hceb Hanc Hneq.
  - forwards*: Nth_nil_inv HNcha.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (Hedge & _).
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
      2:{ forwards Hla: Nth_last_inv HNloga.
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

(* --- [6] machinery: hb -> ancestry between recorded pointers --- *)

(* Same thread: commit pointers only move forward along the log. *)
Lemma CH_thread_monotone :
  forall log D TC G g CH m n em en t cm cn,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log em -> get_thread em = t ->
    LibList.Nth n log en -> get_thread en = t ->
    m <= n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. unfold empty_graph, root_commit in Hplay. gen m n em en t cm cn.
  inductions Hplay; introv HNlogm Hgtm HNlogn Hgtn Hle HNchm HNchn.
  - inverts HNlogm.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & HemE)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      forwards Hwf0: wf_log_last_inv Hwf.
      asserts Hanc: (ancestor G' cm cn).
      {
        applys* IHHplay Hle.
      }
      eapply play_event_graph_extends; eassumption.
    + subst en.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      subst cn.
      destruct (classic (m = length log)) as [Hmis | Hmne].
      * subst m.
        forwards [HNchm0 | (_ & Hcmeq)]: Nth_last_inv HNchm.
        { forwards Hib: Nth_inbound HNchm0. nat_math. }
        subst cm. rewrite Hgtn. apply ancestor_refl.
      * rewrite Hgtn.
        forwards Hfull: (>> PlaySnoc Hplay H).
        forwards Hfin: (>> CH_ancestor_TC Hwf Hfull HNlogm Hgtm HNchm).
        exact Hfin.
Qed.

(* The three cross-thread sync edges.  Unlike Branching (which reads the merge
   edge), in Linear the target (lock/start/join) just syncs to the head, so its
   recorded pointer IS the head, and the source's commit is below the head by
   [play_log_inv]. *)
Lemma hb_lock_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 l cm cn,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth n log (event_lock t2 l) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. unfold empty_graph, root_commit in Hplay. gen m n t1 t2 l cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      asserts Hanc: (ancestor G' cm cn).
      {
        applys* IHHplay Hlt.
      }
      eapply play_event_graph_extends; eassumption.
    + subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      asserts Hce: (is_commit_event (event_unlock t1 l)). { simpl. exact I. }
      forwards Hcmdom: CH_commit_event_indom Hplay HNchm0 HNm0 Hce.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H.
      cbn [get_thread] in Hcneq. rewrite read_update_same in Hcneq. subst cn.
      forwards Hinv: play_log_inv Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

Lemma hb_spawn_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_spawn t1 t2) ->
    LibList.Nth n log (event_start t2) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. unfold empty_graph, root_commit in Hplay. gen m n t1 t2 cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      asserts Hanc: (ancestor G' cm cn).
      {
        applys* IHHplay Hlt.
      }
      eapply play_event_graph_extends; eassumption.
    + subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      asserts Hce: (is_commit_event (event_spawn t1 t2)). { simpl. exact I. }
      forwards Hcmdom: CH_commit_event_indom Hplay HNchm0 HNm0 Hce.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H.
      cbn [get_thread] in Hcneq. rewrite read_update_same in Hcneq. subst cn.
      forwards Hinv: play_log_inv Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

Lemma hb_join_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_end t2) ->
    LibList.Nth n log (event_join t1 t2) ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hwf Hplay. unfold empty_graph, root_commit in Hplay. gen m n t1 t2 cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      asserts Hanc: (ancestor G' cm cn).
      {
        applys* IHHplay Hlt.
      }
      eapply play_event_graph_extends; eassumption.
    + subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      asserts Hce: (is_commit_event (event_end t2)). { simpl. exact I. }
      forwards Hcmdom: CH_commit_event_indom Hplay HNchm0 HNm0 Hce.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H.
      cbn [get_thread] in Hcneq. rewrite read_update_same in Hcneq. subst cn.
      forwards Hinv: play_log_inv Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

(* The [HbVolatile] counterpart of [hb_lock_pointer_ancestor]/etc: a write to a
   volatile variable is a commit event, so the reader's pointer (fast-forwarded
   to the global head at read time) descends from the writer's just-created
   commit, exactly as for lock/spawn/join edges. The only wrinkle: the event at
   the read position [n] could a priori be either [PlayRead] or
   [PlayReadVolatile] (both produce [event_read t2 x v']) -- but [PlayRead]
   requires [x \notin Volatiles], contradicting the [x \in Volatiles] this
   lemma already carries, so that case is vacuous. *)
Lemma hb_volatile_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 x v v' cm cn,
    x \in Volatiles ->
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_write t1 x v) ->
    LibList.Nth n log (event_read t2 x v') ->
    m < n ->
    LibList.Nth m CH cm -> LibList.Nth n CH cn ->
    ancestor G cm cn.
Proof.
  introv Hxvol Hwf Hplay. unfold empty_graph, root_commit in Hplay. gen m n t1 t2 v v' cm cn.
  inductions Hplay; introv HNlogm HNlogn Hlt HNchm HNchn.
  - inverts HNlogn.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards [HNn0 | (HnN & HenE)]: Nth_last_inv HNlogn.
    + forwards Hibn: Nth_inbound HNn0.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      forwards [HNchn0 | (HnNc & _)]: Nth_last_inv HNchn. 2:{ rewrite Hlen in HnNc. nat_math. }
      asserts Hanc: (ancestor G' cm cn).
      {
        applys* IHHplay Hlt.
      }
      eapply play_event_graph_extends; eassumption.
    + subst E.
      forwards [HNm0 | (HmN & _)]: Nth_last_inv HNlogm. 2:{ nat_math. }
      forwards [HNchm0 | (HmNc & _)]: Nth_last_inv HNchm. 2:{ rewrite Hlen in HmNc. nat_math. }
      asserts Hce: (is_commit_event (event_write t1 x v)). { simpl. exact Hxvol. }
      forwards Hcmdom: CH_commit_event_indom Hplay HNchm0 HNm0 Hce.
      forwards [HNchn0 | (HnNc & Hcneq)]: Nth_last_inv HNchn.
      { forwards Hib: Nth_inbound HNchn0. rewrite <- Hlen in HnN. nat_math. }
      inverts H.
      * (* PlayRead: contradicts [x \in Volatiles] *)
        match goal with Hnv : x \notin Volatiles |- _ => false; applys Hnv Hxvol end.
      * cbn [get_thread] in Hcneq. rewrite read_update_same in Hcneq. subst cn.
        forwards Hinv: play_log_inv Hplay. destruct Hinv as (_ & Hmax & _).
        applys Hmax Hcmdom.
Qed.

(* [6] A happens-before edge maps to graph ancestry between the recorded pointers. *)
Lemma hb_pointer_ancestor :
  forall log D TC G g CH m n cm cn,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
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
    | m n vt1 vt2 vx vv vv' Hxvol HNvw HNvr Hlt
    | m n k Hmk IHmk Hkn IHkn ];
    introv HNchm HNchn.
  - asserts Hle: (m <= n). { nat_math. }
    applys* (>> CH_thread_monotone Hwf Hplay HN1 HN2 Hle HNchm HNchn).
  - applys (>> hb_lock_pointer_ancestor Hwf Hplay HNu HNl Hlt HNchm HNchn).
  - applys (>> hb_spawn_pointer_ancestor Hwf Hplay HNs HNst Hlt HNchm HNchn).
  - applys (>> hb_join_pointer_ancestor Hwf Hplay HNe HNj Hlt HNchm HNchn).
  - applys (>> hb_volatile_pointer_ancestor Hxvol Hwf Hplay HNvw HNvr Hlt HNchm HNchn).
  - forwards (ek & HNlogk): hb_Nth_r Hmk.
    forwards Hlenk: Nth_inbound HNlogk.
    forwards Hlench: play_log_CH_length Hplay.
    asserts Hklt: (k < length CH). { rewrite Hlench. exact Hlenk. }
    forwards (ck & HNchk): Nth_inbound_inv Hklt.
    forwards Hanc1: IHmk HNchm HNchk.
    forwards Hanc2: IHkn HNchk HNchn.
    applys* ancestor_trans.
Qed.

(* [11] The commit flushing the last x-write is maximal among x-writers. *)
Lemma last_write_maximal :
  forall log D TC G g CH m tm x vm f ef cs,
    race_free log ->
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    LibList.Nth f log ef -> get_thread ef = tm -> is_commit_event ef -> m <= f ->
    LibList.Nth f CH cs ->
    (forall p ep, m <= p -> p < f -> LibList.Nth p log ep -> get_thread ep = tm ->
                  ~ is_commit_event ep) ->
    graph_writes G cs x vm ->
    forall c' v', graph_writes G c' x v' -> ancestor G cs c' -> c' = cs.
Proof.
  intros log D TC G LC CH m tm x vm f ef cs.
  intros Hrf Hwf Hplay HNm Hlast HNf Hgf Hcfe Hmf HNchf Hncf Hcsw c' v' Hc'w Hanc.
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
    forwards Hhb: (>> Hrf HNkw HNm Hacc Hkwltm).
    asserts Hgtw: (get_thread (event_write tw' x v') = tw'). { reflexivity. }
    asserts Hgtmne: (get_thread (event_write tm x vm) <> tw'). { simpl. auto. }
    forwards (f'' & ef'' & Hkwf'' & HNf'' & Hgf'' & Hcef'' & Hhbf''):
      (>> hb_cross_thread_flush Hhb HNkw Hgtw HNm Hgtmne).
    forwards Hf''lt: hb_lt Hhbf''.
    asserts Hni: (~ is_commit_event ef'').
    { applys Hncl f'' ef''; [ exact Hkwf'' | nat_math | exact HNf'' | exact Hgf'' ]. }
    exact (Hni Hcef'').
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
    | apply graph_writes_graph_commit
    | apply graph_writes_graph_commit
    ];
    try exact Hgw;
    intro Heq; subst cs;
    match goal with Hf : commit_fresh _ _ |- _ => applys commit_fresh_not_indom Hf Hin end.
Qed.

(* [12] The last x-write is either still uncommitted in [tm]'s delta, or it was
   flushed at some commit [cs = CH[f]]. *)
Lemma last_write_committed_or_delta :
  forall log s0 D TC G g CH m tm x vm,
    wf_log log ->
    play_log log s0 (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    ((x \indom (D[tm]) /\ (D[tm])[x] = vm) /\
       (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = tm ->
                     ~ is_commit_event ep)) \/
    (exists f ef cs,
       m <= f /\ LibList.Nth f log ef /\ get_thread ef = tm /\ is_commit_event ef /\
       LibList.Nth f CH cs /\ graph_writes G cs x vm /\
       (forall p ep, m <= p -> p < f -> LibList.Nth p log ep -> get_thread ep = tm ->
                     ~ is_commit_event ep)).
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
      forwards~ IHdisj: IHHplay Hwf0 HN0 Hlast0.
      destruct IHdisj as
        [((Hidom & Hival) & Hnc) |
         (f & ef & cs & Hmf & HNf & Hgf & Hcf & HNchf & Hcsw & Hncf)].
      2:{ (* RIGHT: the flush already happened in the prefix; lift across the step *)
        right. exists f ef cs. splits~.
        - applys Nth_app_l HNf.
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
              { applys Hnc Hg HNg0 Hgg. } { subst; simpls; congruence. }
      * (* join *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
      * (* read (PlayRead): D unchanged *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
      * (* read (PlayReadVolatile): D unchanged too -- identical proof *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
      * (* write wt wj ww (PlayWrite): stays local in [tm]'s delta *)
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
                 { applys Hnc Hg HNg0 Hgg. }
                 { subst ep; simpl; auto. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst; simpls; congruence. }
      * (* write wt wj ww (PlayWriteVolatile): flushes [tm]'s WHOLE delta into a
           fresh commit -- if [wt = tm], [x]'s pending value (if any, i.e.
           [wj <> x] -- [wj = x] is excluded exactly as for PlayWrite) is
           committed ALONGSIDE [wj], not merely overwritten *)
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
                 match goal with Hbd : binds _ tm ?dstg |- binds (?dstg[wj := ww]) _ _ =>
                   forwards Hdeq: read_of_binds Hbd; rewrite <- Hdeq end.
                 applys binds_update_neq; [ congruence | ].
                 applys binds_of_indom_read Hidom Hival; typeclass.
              ** introv Hg Hgflt HNg Hgg.
                 forwards [HNg0 | (HgN & _)]: Nth_last_inv HNg.
                 { applys Hnc Hg HNg0 Hgg. } { nat_math. }
        -- left; split.
           ++ split.
              ** rewrite read_update_neq; [ exact Hidom | congruence ].
              ** rewrite read_update_neq; [ exact Hival | congruence ].
           ++ introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
              { applys Hnc Hg HNg0 Hgg. } { subst; simpls; congruence. }
      * (* lock (PlayLock) *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
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
              { applys Hnc Hg HNg0 Hgg. } { subst; simpls; congruence. }
      * (* start *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
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
              { applys Hnc Hg HNg0 Hgg. } { subst; simpls; congruence. }
    + (* the write is the last (appended) event *)
      subst E. inverts H.
      * (* PlayWrite: stays local -- [x] is exactly the value just written *)
        left. split.
        -- split.
           ++ rewrite read_update_same. apply indom_update_same; typeclass.
           ++ rewrite read_update_same, read_update_same. reflexivity.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { forwards Hglt: Nth_inbound HNg0. nat_math. }
           { subst ep; simpl; auto. }
      * (* PlayWriteVolatile: this write IS its own commit -- [kw = f = m],
           matching the [kw' <= f'] weakening in [graph_writes_flush]. The
           fresh commit is named [g] here, not [g'], since [g'] is already
           taken by this lemma's own top-level state pair. *)
        right. exists (length log) (event_write tm x vm) g. splits.
        -- nat_math.
        -- applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
        -- reflexivity.
        -- simpl; assumption.
        -- cbn [get_thread]; rewrite read_update_same;
           applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
        -- applys graph_writes_graph_commit_new.
           apply binds_update_same.
        -- introv Hg Hgflt HNg Hgg. nat_math.
Qed.

(* [13] The value a reader sees ([is_latest_value] at its pointer) is the last
   write of [x] in the log. *)
Lemma last_write_visible_commit :
  forall log D TC G g CH m n tm x vm en,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hrf Hplay HNm Hlast Hndom HNn Hhb.
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
      { applys (>> last_write_maximal Hrf Hwf Hplay HNm Hlast HNf Hgf Hcfe Hmf
                   HNchf Hncf Hcsw). }
      applys Hmax Hc'w Hanc1.
Qed.

(* [14] Wrapper around [last_write_visible_commit]. *)
Lemma hb_last_write_visible :
  forall log D TC G g CH m n tm x vm en,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hrf Hplay HNm Hlast Hndom HNn Hhb.
  applys* last_write_visible_commit.
Qed.

(* A volatile write event's own log position IS its commit's graph write:
   Linear analog of Branching's [write_volatile_graph_writes], simplified
   since a volatile write here commits directly (no merge). *)
Lemma write_volatile_graph_writes :
  forall log D TC G g CH t x v m cm,
    play_log log init_play_cfg (D, TC, G, g) CH ->
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
      forwards Hgw: (>> IHHplay (eq_refl init_play_cfg) (eq_refl (D', TC', G', g')) Hxvol HN0 HN0ch).
      applys play_event_graph_writes_mono Hpe Hgw.
    + subst E. inverts Hpe as Hxvol1 Hbd1 Hxvol2 Hbd2 Hfresh2.
      * false; applys Hxvol1 Hxvol.
      * forwards [HN0ch | (HmNch & Hcmeq)]: Nth_last_inv HNch.
        { forwards Hib: Nth_inbound HN0ch. rewrite <- Hlen in HmN. nat_math. }
        cbn [get_thread] in Hcmeq. rewrite read_update_same in Hcmeq. subst cm.
        applys graph_writes_graph_commit_new. apply binds_update_same.
Qed.

(* The value seen after a [StepReadVolatile] pull (which reads [is_latest_value]
   at the CURRENT global head [g] directly, no merge -- unlike Branching, which
   pulls via a [graph_merge] of a per-variable [vc_read VVC x] pointer) is the
   log's last [x]-write. *)
Lemma is_latest_value_after_volatile_pull :
  forall log D TC G g CH x v,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \in Volatiles ->
    (exists tw log', LibList.filter (fun e => writes_variable x e) log = log' & event_write tw x v) ->
    is_latest_value G g x v.
Proof.
  introv Hwf Hrf Hplay Hxvol (tw & log' & Hfilter).
  forwards Hinv: play_log_inv Hplay. destruct Hinv as (_ & Hmax & _).
  forwards (lw & HNlw & Hlast): last_write_position Hfilter.
  forwards Hlwlt: Nth_inbound HNlw.
  forwards Hlen: play_log_CH_length Hplay.
  asserts HlwltCH: (lw < length CH). { nat_math. }
  forwards (c_lw & HNlwCH): Nth_inbound_inv HlwltCH.
  asserts Hgwlw: (graph_writes G c_lw x v).
  { applys write_volatile_graph_writes Hplay Hxvol HNlw HNlwCH. }
  asserts Hdomlw: (graph_indom G c_lw). { applys graph_writes_to_indom Hgwlw. }
  asserts Hcelw: (is_commit_event (event_write tw x v)). { simpl. exact Hxvol. }
  exists c_lw. splits.
  - exact Hgwlw.
  - applys Hmax Hdomlw.
  - introv Hgw3 Hanc1 Hanc2.
    destruct (classic (c'' = c_lw)) as [-> | Hne]; [reflexivity | exfalso].
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
    asserts Hcef3': (is_commit_event (event_write tw3 x v')). { simpl. exact Hxvol. }
    asserts Hneq': (c_lw <> c''). { intro Heq. applys Hne (eq_sym Heq). }
    forwards Hlwltf3: (>> ancestor_creation_order Hplay HNlwCH HNlw Hcelw HNf3CH HNkw3 Hcef3' Hanc1 Hneq').
    nat_math.
Qed.

(* The reverse direction of [is_latest_value_after_volatile_pull]: whatever
   value a [StepReadVolatile] pull actually observes at the global head [g] is
   the log's last write of [x]. *)
Lemma is_latest_value_after_volatile_pull_inv :
  forall log D TC G g CH x v,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \in Volatiles ->
    is_latest_value G g x v ->
    exists tw log', LibList.filter (fun e => writes_variable x e) log = log' & event_write tw x v.
Proof.
  introv Hwf Hrf Hplay Hxvol Hlv.
  destruct (last_case (LibList.filter (fun e => writes_variable x e) log)) as [Hnil | (e0 & l0 & Heq)].
  - exfalso.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    forwards (tw & m & HNm): graph_writes_log_write Hplay Hgw.
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
    forwards Hval: is_latest_value_after_volatile_pull Hwf Hrf Hplay Hxvol.
    { exists tw0 l0. exact Heq. }
    forwards Hinv: play_log_inv Hplay. destruct Hinv as (Htot & _ & _).
    forwards Hcfg: total_order_conflict_free_graph Htot.
    forwards ->: is_latest_value_inj Hcfg Hlv Hval.
    exists tw0 l0. exact Heq.
Qed.

(* Forward direction of the global-read correspondence: if [v] is the value of
   the last write to [x] in the log and [t] reads [x] globally (it is not in [t]'s
   delta), then [v] is exactly the value [t] sees in the commit graph
   ([is_latest_value]).

   This is the shared core that both directions of the global-read equivalence
   build on: [linear_complete] uses it as is, and [race_free_last_global_write]
   (its converse) recovers it via [is_latest_value_inj].  It is the single place
   where [hb_last_write_visible] is applied.  The read value [vr] is kept distinct
   from the last-write value [v]: they coincide in [linear_complete] but genuinely
   differ in the converse. *)
Lemma last_global_write_latest_value :
  forall log D TC G g CH t x vr v t' log',
    x \notin Volatiles ->
    race_free (log & event_read t x vr) ->
    wf_log (log & event_read t x vr) ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \notindom (D[t]) ->
    LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v ->
    is_latest_value G (TC[t]) x v.
Proof.
  introv Hxnvol Hrf Hwf Hplay Hndom Hfilter.
  forwards (mw & HNL & Hlast): last_write_position Hfilter.
  forwards HLlt: Nth_inbound HNL.
  asserts Hplayf: (exists CHf, play_log (log & event_read t x vr)
                     init_play_cfg (D, TC, G, g) CHf).
  { eexists. applys PlaySnoc Hplay. apply* PlayRead. }
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
  (* race-freedom: the last write happens-before the read (they share [x]). *)
  asserts Hacc: (accesses_variable x (event_read t x vr)). { reflexivity. }
  forwards Hhb: Hrf HNLf HNread Hacc HLlt.
  asserts HndomL: (x \notindom (D[t'])).
  { destruct (classic (t' = t)) as [-> | Hne].
    - exact Hndom.
    - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb.
      simpl. congruence. }
  forwards Hlv: (>> hb_last_write_visible Hwf Hrf Hplayf HNLf Hlastf HndomL HNread Hhb).
  simpl in Hlv. exact Hlv.
Qed.

(* [15] GOAL: the value a thread reads globally is the last write of [x] in the
   log.  Converse of [last_global_write_latest_value].  Linear drops Branching's
   [conflict_free_graph G] premise: it follows from [play_log_inv] (total order)
   via [total_order_conflict_free_graph]. *)
Lemma race_free_last_global_write :
  forall log D TC G g CH t x v c,
    x \notin Volatiles ->
    race_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    TC[t] = c ->
    is_latest_value G c x v ->
    exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v.
Proof.
  introv Hxnvol Hrf Hwf Hplay Hndom Hdom HTC Hval.
  forwards Hinv: play_log_inv Hplay.
  destruct Hinv as (Htot & _ & _).
  forwards Hcfg: total_order_conflict_free_graph Htot.
  (* [is_latest_value] ensures there is an x-write; take the last one. *)
  forwards (lw & tL & vL & Hfilter): is_latest_value_log_write Hplay Hval.
  (* the forward direction: [t] sees the last write's value [vL] *)
  forwards Hlv: (>> last_global_write_latest_value Hxnvol Hrf Hwf Hplay Hndom Hfilter).
  rewrite HTC in Hlv.
  (* and [is_latest_value] is functional, so [vL = v] *)
  forwards ->: is_latest_value_inj Hcfg Hlv Hval.
  exists tL lw. exact Hfilter.
Qed.

(* The global-read correspondence as a full equivalence: for a data-race-free,
   [t]-readable log, the value [t] sees for [x] in the commit graph
   ([is_latest_value]) is exactly the value of the last write to [x] in the log.
   This simply packages the two directions -- [last_global_write_latest_value] and
   its converse [race_free_last_global_write]. *)
Theorem is_latest_value_iff_last_write :
  forall log D TC G g CH t x v,
    x \notin Volatiles ->
    race_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    (is_latest_value G (TC[t]) x v
     <-> exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v).
Proof.
  introv Hxnvol Hrf Hwf Hplay Hndom Hdom. split.
  - introv Hval.
    applys (>> race_free_last_global_write Hxnvol Hrf Hwf Hplay Hndom Hdom); [ reflexivity | exact Hval ].
  - introv (t' & log' & Hfilter).
    applys (>> last_global_write_latest_value Hxnvol Hrf Hwf Hplay Hndom Hfilter).
Qed.

(* ============================================================================
   Completeness ingredient 1: a thread's pending delta is always conflict-free
   to push onto the global head, when the log is race-free.
   ============================================================================ *)

(* Any committed graph write of [j] is an ancestor of [t]'s pointer, when [t]
   has a pending (uncommitted) write of [j].  [t]'s pending write is the last
   one (race-freedom), so every committed [j]-writer precedes it. *)
Lemma delta_writer_ancestor :
  forall log D TC G g CH t j vt c vc,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    t \indom D ->
    binds (D[t]) j vt ->
    graph_writes G c j vc ->
    ancestor G c (TC[t]).
Proof.
  introv Hwf Hrf Hplay Htdom Hbd Hgw.
  forwards (kt & HNkt & Hns): delta_is_uncommitted_write Hplay Htdom Hbd.
  asserts Hgtt: (get_thread (event_write t j vt) = t). reflexivity.
  forwards (fc & efc & tc & kc & HNfcCH & HNfclog & Hgtc & Hcec & Hkclt & HNkc & Hncl):
    graph_writes_flush Hplay Hgw.
  forwards Hlen: play_log_CH_length Hplay.
  forwards Hktlt: Nth_inbound HNkt.
  asserts HktltCH: (kt < length CH). nat_math.
  forwards (ckt & HNktCH): Nth_inbound_inv HktltCH.
  forwards Hanckt: (>> CH_ancestor_TC Hwf Hplay HNkt Hgtt HNktCH).
  destruct (classic (tc = t)) as [Hteq | Htne].
  - rewrite Hteq in Hgtc. applys CH_ancestor_TC Hwf Hplay HNfclog Hgtc HNfcCH.
  - asserts Hkne: (kt <> kc).
    { intros Heq. subst kc. forwards Heqw: Nth_functional HNkt HNkc.
      inverts Heqw. apply Htne. reflexivity. }
    destruct (classic (kt < kc)) as [Hlt | Hge].
    + exfalso.
      asserts Hacc: (accesses_variable j (event_write tc j vc)). reflexivity.
      forwards Hhb: (>> Hrf HNkt HNkc Hacc Hlt).
      asserts Hgtcne: (get_thread (event_write tc j vc) <> t). { simpl. exact Htne. }
      forwards (f'' & ef'' & Hktf'' & HNf'' & Hgf'' & Hcef'' & Hhbf''):
        hb_cross_thread_flush Hhb HNkt Hgtt HNkc Hgtcne.
      applys Hns Hktf'' HNf'' Hgf'' Hcef''.
    + asserts Hltba: (kc < kt). nat_math.
      asserts Hacc: (accesses_variable j (event_write t j vt)). reflexivity.
      forwards Hhb: (>> Hrf HNkc HNkt Hacc Hltba).
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

(* When replaying a race-free log, a thread's pending delta is disjoint from
   the changes between its pointer and the head: pushing [D[t]] onto the head [g]
   is conflict-free.  (This is the [dom (D[t])] half of Branching's
   [conflict_free_merge_holds]; Linear needs no merge, so the change-set/
   change-set half is unnecessary.) *)
Lemma lin_conflict_free_holds :
  forall log D TC G g CH t,
    wf_log log ->
    race_free log ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    t \indom D ->
    t \indom TC ->
    lin_conflict_free (D[t]) (TC[t]) g G.
Proof.
  introv Hwf Hrf Hplay Htd Htc.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct G as (C & P). destruct Hpgwf as (Hedge & Hdg).
  (* [g] is the in-graph head whenever the delta map is non-empty (here [t \in D]). *)
  asserts Hg: (graph_indom (C, P) g).
  { destruct Hdg as [-> | Hin]; [ forwards*: indom_empty_inv Htd | exact Hin ]. }
  unfold lin_conflict_free. rew_set. intros j Hjd Hj2.
  unfold change_set in Hj2. destruct Hj2 as (c & Hjc & Hancg & Hnanc).
  asserts Hdomc: (graph_indom (C, P) c).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hancg; [ exact Hin | subst c; exact Hg ]. }
  asserts Hgwc: (graph_writes (C, P) c j (C[c][j])).
  { exists (C[c]). split.
    - unfold graph_binds. applys binds_of_indom_read Hdomc; (reflexivity || typeclass).
    - applys binds_of_indom_read Hjc; (reflexivity || typeclass). }
  asserts Hbdj: (binds (D[t]) j (D[t][j])).
  { applys binds_of_indom_read Hjd; (reflexivity || typeclass). }
  applys Hnanc. applys (>> delta_writer_ancestor Hwf Hrf Hplay Htd Hbdj Hgwc).
Qed.

(* Adding the volatile write's own variable [x] to the checked delta doesn't
   introduce a NEW conflict: whatever last wrote [x] is already dominated by
   [t]'s own pointer, given a [race_free] log ending in this very write.
   Verbatim analogue of [lin_conflict_free_holds], specialised to the single
   variable [x] being written -- [t] has no delta binding for [x] to appeal
   to (it is ABOUT to write it), so the [hb] edge comes from [race_free]
   applied directly to the appended write, not from [delta_writer_ancestor]. *)
Lemma global_head_change_set_empty_race_free :
  forall log D TC G g CH t x v,
    wf_log log ->
    race_free (log & event_write t x v) ->
    play_log log init_play_cfg (D, TC, G, g) CH ->
    x \in Volatiles ->
    t \indom D ->
    t \indom TC ->
    x \notin change_set G (TC[t]) g.
Proof.
  introv Hwf0 Hrf Hplay Hxvol Htd Httc.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct G as (C & P). destruct Hpgwf as (Hedge & Hdg).
  asserts Hg: (graph_indom (C, P) g).
  { destruct Hdg as [-> | Hin]; [ forwards*: indom_empty_inv Htd | exact Hin ]. }
  intro Hex. destruct Hex as (c & Hxc & Hancc & Hnanc).
  asserts Hcdom: (graph_indom (C, P) c).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hancc; [ exact Hin | subst c; exact Hg ]. }
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
  forwards Hhb: (>> Hrf HNkwapp HNenapp Hacc Hflt).
  forwards (q & eq & Hqlt & HNqapp & Hgq & Hdisj): hb_last_write_same_thread_witness Hhb HNenapp.
  forwards [HNqlog | (mm & Heqm & _)]: Nth_app_inv HNqapp.
  2:{ nat_math. }
  forwards Hlen: play_log_CH_length Hplay.
  asserts HqltCH: (q < length CH). { rewrite Hlen. exact Hqlt. }
  forwards (cq & HNqCH): Nth_inbound_inv HqltCH.
  forwards HancqTC: (>> CH_ancestor_TC Hwf0 Hplay HNqlog Hgq HNqCH).
  destruct Hdisj as [Heqfq | Hhbfq].
  - subst q.
    forwards Heqc: Nth_functional HNfCH HNqCH. subst cq.
    applys Hnanc HancqTC.
  - forwards Hhbfq': hb_app_inv Hhbfq Hqlt.
    forwards Hancfq: (>> hb_pointer_ancestor Hwf0 Hplay Hhbfq' HNfCH HNqCH).
    applys Hnanc. applys ancestor_trans Hancfq HancqTC.
Qed.

(* Folding the newly-checked variable [x] into the diff preserves
   conflict-freedom, given it does not itself land in the change set --
   the [lin_conflict_free] analogue of [conflict_free_merge_add_var]
   (simpler: no merge, so no second, symmetric change-set term). *)
Lemma lin_conflict_free_add_var :
  forall d c g G x v,
    lin_conflict_free d c g G ->
    x \notin change_set G c g ->
    lin_conflict_free (d[x := v]) c g G.
Proof.
  introv Hlcf Hxnin. unfold lin_conflict_free in *.
  rew_set in Hlcf. rew_set. intros j Hj1 Hj2.
  lets [-> | Hjd']: (indom_update_inv Hj1).
  - applys Hxnin Hj2.
  - applys Hlcf Hjd' Hj2.
Qed.

(* ===========================================================================
   Soundness of conflict detection (linear).

   Every linear synchronisation -- end, spawn, join, lock, release -- commits or
   fast-forwards onto the global head, guarded by the same check
   [lin_conflict_free (D[t]) (TC[t]) g G].  This theorem is the contrapositive of
   [lin_conflict_free_holds]: if a running thread's staged writes conflict with the
   global head -- so any synchronisation it attempts is blocked -- then the log
   already exhibits a data race ([~ race_free log]).  It thus covers all five
   linear synchronisation actions uniformly.
   =========================================================================== *)

Theorem linear_sync_conflict_sound :
  forall log T G g L t e d c,
    wf_log log ->
    describes log (T, G, L) ->
    is_global_head G g ->
    binds T t (state_running, te_exp e, d, c) ->
    ~ lin_conflict_free d c g G ->
    ~ race_free log.
Proof.
  introv Hwf Hdesc Hhead Hbt Hncf Hrflog.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
  forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
  forwards Heqg: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (st0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  apply Hncf.
  applys (>> lin_conflict_free_holds Hwf Hrflog Hplay HtD HtTC).
Qed.

(* Writing a volatile [x] additionally folds [x] itself into the checked
   diff ([d[x := v]], per the write-write race fix), so -- unlike the other
   five synchronisations -- this is NOT a direct instance of
   [linear_sync_conflict_sound]: [x]'s own membership in the global head's
   change set is exactly the fact [global_head_change_set_empty_race_free]
   supplies, but only relative to the log EXTENDED with this very write (there
   is no [hb] rule making [t]'s not-yet-logged write of [x] unconditionally
   consistent with [race_free log] alone). Concretely: if the check fails,
   appending this very write would ALREADY break race-freedom -- matching
   exactly the guard [linear_complete] relies on ([LinearEquiv.v]) to admit a
   real [race_free (log & event_write t x v)] step. *)
Theorem linear_volatile_write_conflict_sound :
  forall log T G g L t e d c K x v,
    wf_log log ->
    describes log (T, G, L) ->
    is_global_head G g ->
    binds T t (state_running, te_exp e, d, c) ->
    step_ul e K (eff_write x v) ->
    x \in Volatiles ->
    ~ lin_conflict_free d[x := v] c g G ->
    ~ race_free (log & event_write t x v).
Proof.
  introv Hwf Hdesc Hhead Hbt Hul Hxvol Hncf Hrflog.
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & g0 & CH & Hplay & Hdelta & HdomD & HdomTC)).
  forwards (HwfG & _ & Hhead0): play_log_head_wf Hplay.
  forwards Heqg: is_global_head_unique HwfG Hhead0 Hhead. subst g0.
  lets Htin: (indom_of_binds Hbt).
  asserts HtD: (t \indom D). { applys HdomD Htin. }
  asserts HtTC: (t \indom TC). { applys HdomTC Htin. }
  forwards (st0 & e0 & Hbd): Hdelta Htin.
  forwards* Heq: binds_inj Hbt Hbd. inverts Heq.
  forwards Hrflog0: race_free_last_inv Hrflog.
  apply Hncf.
  applys lin_conflict_free_add_var.
  - applys (>> lin_conflict_free_holds Hwf Hrflog0 Hplay HtD HtTC).
  - applys (>> global_head_change_set_empty_race_free Hwf Hrflog Hplay Hxvol HtD HtTC).
Qed.

(* The graph-membership half of [wf_cfg], read straight off the replay (no
   [wf_log] needed): the graph stays well formed (graph_commit only ever extends
   the totally-ordered chain at the in-graph head), the head is in the graph, and
   every thread pointer is in the graph. Mirrors [play_event_preserves_inv]. *)
Lemma play_event_preserves_graph_facts :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    wf_graph Gp /\ graph_indom Gp gp /\ (forall t, t \indom TCp -> graph_indom Gp (TCp[t])) ->
    wf_graph G /\ graph_indom G g /\ (forall t, t \indom TC -> graph_indom G (TC[t])).
Proof.
  introv Hpe (Hwf' & Hg' & HTC'). inverts Hpe.
  - (* PlayRead *) splits; assumption.
  - (* PlayReadVolatile: TCp[t := gp], graph/head unchanged (same as PlayStart) *)
    splits; [ exact Hwf' | exact Hg' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. exact Hg'.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys HTC' Hin.
  - (* PlayWrite *) splits; assumption.
  - (* PlayWriteVolatile: graph_commit, TCp[t := g'] (same as PlayEnd) *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    splits.
    + applys graph_commit_wf Hwf' Hfresh Hg'.
    + applys graph_commit_indom_same.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. applys graph_commit_indom_same.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys graph_commit_indom. applys HTC' Hin.
  - (* PlayStart: TCp[t := gp], graph/head unchanged *)
    splits; [ exact Hwf' | exact Hg' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. exact Hg'.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys HTC' Hin.
  - (* PlayEnd: graph_commit Gp gp g' d, TCp[t := g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    splits.
    + applys graph_commit_wf Hwf' Hfresh Hg'.
    + applys graph_commit_indom_same.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. applys graph_commit_indom_same.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys graph_commit_indom. applys HTC' Hin.
  - (* PlaySpawn: graph_commit, TCp[t1 := g'][t2 := g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    splits.
    + applys graph_commit_wf Hwf' Hfresh Hg'.
    + applys graph_commit_indom_same.
    + intros tq Htq. destruct (classic (tq = t2)) as [->|Hne2].
      * rewrite read_update_same. applys graph_commit_indom_same.
      * rewrite read_update_neq; auto. destruct (classic (tq = t1)) as [->|Hne1].
        -- rewrite read_update_same. applys graph_commit_indom_same.
        -- rewrite read_update_neq; auto.
           asserts Hin: (tq \indom TCp).
           { asserts Ho2: (tq = t2 \/ tq \indom (TCp[t1 := g])). { applys* indom_update_inv Htq. }
             destruct Ho2 as [Heq|Hin2]; [congruence|].
             asserts Ho1: (tq = t1 \/ tq \indom TCp). { applys* indom_update_inv Hin2. }
             destruct Ho1 as [Heq|Hin1]; [congruence|exact Hin1]. }
           applys graph_commit_indom. applys HTC' Hin.
  - (* PlayJoin: TCp[t1 := gp], graph/head unchanged *)
    splits; [ exact Hwf' | exact Hg' | ].
    intros tq Htq. destruct (classic (tq = t1)) as [->|Hne].
    + rewrite read_update_same. exact Hg'.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t1 \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys HTC' Hin.
  - (* PlayLock: TCp[t := gp], graph/head unchanged *)
    splits; [ exact Hwf' | exact Hg' | ].
    intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
    + rewrite read_update_same. exact Hg'.
    + rewrite read_update_neq; auto.
      asserts Hin: (tq \indom TCp).
      { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
      applys HTC' Hin.
  - (* PlayUnlock: graph_commit, TCp[t := g'] *)
    match goal with Hf : commit_fresh _ _ |- _ => rename Hf into Hfresh end.
    splits.
    + applys graph_commit_wf Hwf' Hfresh Hg'.
    + applys graph_commit_indom_same.
    + intros tq Htq. destruct (classic (tq = t)) as [->|Hne].
      * rewrite read_update_same. applys graph_commit_indom_same.
      * rewrite read_update_neq; auto.
        asserts Hin: (tq \indom TCp).
        { asserts Hor: (tq = t \/ tq \indom TCp). { applys* indom_update_inv Htq. }
          destruct Hor as [Heq|Hin]; [congruence|exact Hin]. }
        applys graph_commit_indom. applys HTC' Hin.
Qed.

Lemma play_log_graph_facts :
  forall log D TC G g CH,
    play_log log init_play_cfg (D, TC, G, g) CH ->
    wf_graph G /\ graph_indom G g /\ (forall t, t \indom TC -> graph_indom G (TC[t])).
Proof.
  introv Hplay. inductions Hplay.
  - splits.
    + apply init_graph_wf.
    + applys graph_root_indom_same.
    + intros t Ht.
      asserts Hor: (t = t_root \/ t \indom (empty : commits)). { applys* indom_update_inv Ht. }
      destruct Hor as [-> | Hin].
      * rewrite read_update_same. applys graph_root_indom_same.
      * false. applys indom_empty_inv Hin.
  - forwards* Hfacts: IHHplay.
    applys* play_event_preserves_graph_facts H Hfacts.
Qed.

(* As for Branching, [describes] already implies [wf_cfg], with no [wf_log]
   needed: the graph-membership conjuncts come from [play_log_graph_facts] and the
   [total_order] / head-is-maximum conjuncts from [play_log_inv]. *)
Lemma describes_wf_cfg :
  forall log cfg,
    describes log cfg ->
    wf_cfg cfg.
Proof.
  introv Hdesc. destruct cfg as [[T G] L].
  destruct Hdesc as (_ & _ & _ & _ & _ & _ &
    (D & TC & g & CH & Hplay & HdT & HdomD & HdomTC)).
  forwards (Hwfg & Hgin & HTCin): play_log_graph_facts Hplay.
  forwards (Htot & Hmax & _): play_log_inv Hplay.
  splits.
  - exact Hwfg.
  - exact Htot.
  - exists g. splits*.
  - introv Hb.
    lets Hin: (indom_of_binds Hb).
    forwards (st0 & e0 & Hb0): HdT Hin.
    forwards* Heq: binds_inj Hb Hb0. inverts Heq.
    applys HTCin. applys HdomTC Hin.
Qed.
