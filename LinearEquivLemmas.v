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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists m,
      LibList.Nth m log (event_write t x v) /\
      (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
Proof.
  introv Hplay Hdom Hbinds.
  inductions Hplay.
  - (* PlayNil: D = empty *)
    forwards*: indom_empty_inv.
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
    + (* PlayInit (event_init t0): flushes D[t0] *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns): IHHplay.
        exists wm. split;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros _; simpl; auto ]. }
Qed.

(* When replaying a conflict-free log, every value in a thread's local diff is
   the last write of that variable in the whole log. *)
Lemma conflict_free_last_local_write :
  forall log D TC G g CH t x v,
    conflict_free log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t x v.
Proof.
  introv Hcf Hplay Hdom Hdelta.
  hint conflict_free_last_inv.
  inductions Hplay.
  - forwards*: indom_empty_inv.
  - inverts H.
    + (* PlayRead *)
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
           asserts Hbinds: (binds D'[t0] x v).
           { forwards : read_of_binds H2. subst*. }
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
    + (* PlayInit *)
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
   the heavy [conflict_free_log_describes_conflict_free_graph] argument that the
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
  - apply indom_update_of_indom;
      (typeclass || (apply indom_update_of_indom; (typeclass || assumption))).
  - apply indom_update_of_indom; (typeclass || assumption).
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
    + subst E. inverts H. apply indom_update_same; typeclass.
Qed.

(* The last writer of [x] has flushed it: its write happens-before an event of a
   different thread, so it must have committed (cf. [hb_preserves_thread] and the
   uncommitted-write characterisation). *)
Lemma last_writer_not_in_delta :
  forall log D TC G g CH m tm x vm n en,
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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

(* A single play step preserves the head invariant.  Only the very first event
   (the init) needs to know the graph was empty beforehand; that fact is supplied
   by the caller through the second premise. *)
Lemma play_event_preserves_inv :
  forall E Dp TCp Gp gp D TC G g,
    play_event E (Dp, TCp, Gp, gp) (D, TC, G, g) ->
    (forall t0, E = event_init t0 -> Gp = empty_graph /\ TCp = empty) ->
    play_state_inv TCp Gp gp ->
    play_state_inv TC G g.
Proof.
  introv Hpe Hinit Hinv'.
  destruct Hinv' as (Htot' & Hmax' & Hptr').
  inverts Hpe.
  - (* PlayRead *) exact (conj Htot' (conj Hmax' Hptr')).
  - (* PlayWrite *) exact (conj Htot' (conj Hmax' Hptr')).
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
      * rewrite read_update_same. apply ancestor_refl.
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
  - (* PlayInit: graph was empty, so the new graph is the singleton root *)
    forwards (HGe & HTCe): Hinit t; [ reflexivity | ].
    subst Gp TCp.
    unfold play_state_inv. splits.
    + unfolds total_order, graph_root, empty_graph, graph_indom.
      introv Ha Hb.
      asserts ->: (a = root_commit).
      { rew_dom. rew_set in Ha. branches; [forwards*: indom_empty_inv | auto]. }
      asserts ->: (b = root_commit).
      { rew_dom. rew_set in Hb. branches; [forwards*: indom_empty_inv | auto]. }
      left. apply ancestor_refl.
    + introv Hc.
      asserts ->: (c = root_commit).
      { unfolds graph_indom, graph_root, empty_graph.
        rew_dom. rew_set in Hc. branches; [forwards*: indom_empty_inv | auto]. }
      apply ancestor_refl.
    + intros tq Htq.
      asserts ->: (tq = t).
      { asserts Hor: (tq = t \/ tq \indom (empty : commits)). { applys* indom_update_inv Htq. }
        destruct Hor as [Heq|Hin]; [auto | false; applys* indom_empty_inv Hin]. }
      rewrite read_update_same. apply ancestor_refl.
Qed.

Lemma play_log_inv :
  forall log D TC G g CH,
    wf_log log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    play_state_inv TC G g.
Proof.
  introv Hwf Hplay.
  inductions Hplay.
  - (* PlayNil *)
    unfold play_state_inv. splits.
    + intros a b Ha Hb. unfolds graph_indom, empty_graph. exfalso. applys* indom_empty_inv Ha.
    + intros c Hc. unfolds graph_indom, empty_graph. exfalso. applys* indom_empty_inv Hc.
    + intros t Ht. exfalso. applys* indom_empty_inv Ht.
  - (* PlaySnoc *)
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards~ Hinv': IHHplay.
    applys play_event_preserves_inv H; [ | exact Hinv' ].
    introv Heq. subst E.
    lets (_ & _ & _ & _ & _ & _ & _ & Hinit & _): Hwf.
    forwards (_ & Hl0): Hinit log (@nil event) t0. { rew_list*. }
    subst log.
    inverts Hplay.
    + splits; reflexivity.
    + forwards*: last_eq_nil_inv.
Qed.

(* ============================================================================
   Bridge from the commit graph to the log, for the global-read soundness lemma
   [conflict_free_last_global_write].  Dependency order (Linear adaptations of
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
  inverts Hpe; auto using ancestor_graph_commit, ancestor_graph_root.
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
    (forall t1, E = event_init t1 -> t <> t1) ->
    ancestor G (TCp[t]) (TC[t]).
Proof.
  introv Hpe Hinv Htin Hspawn Hinit.
  destruct Hinv as (Htot & Hmax & Hptr).
  inverts Hpe.
  - (* PlayRead *) apply ancestor_refl.
  - (* PlayWrite *) apply ancestor_refl.
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
  - (* PlayInit *)
    forwards Hne0: Hinit t0; [ reflexivity | ].
    rewrite read_update_neq; auto. apply ancestor_refl.
Qed.

Lemma play_log_indom_TC :
  forall log D' TC' G' g' CH m em,
    wf_log log ->
    play_log log (\{}, \{}, (\{}, \{}), 0) (D', TC', G', g') CH ->
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
      * applys play_event_TC_advance; [ eassumption | | | |].
        -- applys* play_log_inv.
        -- subst. applys* play_log_indom_TC.
        -- introv Heq. subst E.
           forwards Hne: spawned_thread_no_prior_event Hwf HN0.
           congruence.
        -- introv Heq. subst E.
           destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hinit & _).
           forwards* (-> & ->): Hinit log (@nil event) t1.
           forwards*: Nth_nil_inv.
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
    [ p q th e1 e2 HN1 HN2 Hg1 Hg2 Hlt
    | q p lt1 lt2 ll HNsrc HNtgt Hlt
    | p q st1 st2 HNsrc HNtgt Hlt
    | p q jt1 jt2 HNsrc HNtgt Hlt
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    graph_writes G cx x v ->
    exists tw m, LibList.Nth m log (event_write tw x v).
Proof.
  introv Hplay. gen cx x v. inductions Hplay; introv Hgw.
  - destruct Hgw as (dd & Hgb & Hbd). simpls. exfalso. applys binds_empty_false Hgb; typeclass.
  - rename H into Hpe.
    inverts Hpe.
    (* PlayRead/Write/Start/Join/Lock: graph unchanged *)
    1,2,3,6,7: (forwards* (tw & m0 & HN): IHHplay;
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
    + (* PlayInit: graph_root *)
      asserts Hneq: (cx <> root_commit).
      { intros contra. subst. forwards*: graph_writes_graph_root_same_false. }
      forwards*: graph_writes_graph_root_inv Hgw.
      forwards* (tw & m0 & HN): IHHplay.
      exists tw m0. applys* Nth_app_l.
Qed.

(* [8] [is_latest_value] guarantees the x-write filter of the log is non-empty. *)
Lemma is_latest_value_log_write :
  forall log D TC G g CH c x v,
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
    destruct e as [s1 s2 | j1 j2 | rt ri rv | tt jj ww | lt ll | ut ul | stt | ett | it0];
      simpls; tryfalse.
    subst jj. exists lw tt ww. exact Hsnoc.
Qed.

(* [9] Each graph write has a feeding flush: the commit [cx] is created by a
   commit event in the log flushing a delta whose last write of [x] is [v]. *)
Lemma graph_writes_flush :
  forall log D TC G g CH cx x v,
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    graph_writes G cx x v ->
    exists f' ef' tw' kw',
      LibList.Nth f' CH cx /\ LibList.Nth f' log ef' /\ get_thread ef' = tw' /\
      is_commit_event ef' /\ kw' < f' /\ LibList.Nth kw' log (event_write tw' x v) /\
      (forall p ep, kw' <= p -> p < f' -> LibList.Nth p log ep -> get_thread ep = tw' ->
                    ~ is_commit_event ep).
Proof.
  introv Hplay. gen cx x v. inductions Hplay; introv Hgw.
  - destruct Hgw as (dd & Hgb & Hbd). simpls. exfalso. applys binds_empty_false Hgb; typeclass.
  - rename H into Hpe.
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
    (* PlayRead/Write/Start/Join/Lock: graph unchanged *)
    1,2,3,6,7: (applys Hlift; forwards* (f' & ef' & tw' & kw' & R): IHHplay; exists f' ef' tw' kw'; exact R).
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
    + (* PlayInit: graph_root *)
      asserts Hneq: (cx <> root_commit).
      { intros contra. subst. forwards*: graph_writes_graph_root_same_false. }
      forwards*: graph_writes_graph_root_inv.
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
    | destruct G' as (C0 & P0); unfolds graph_indom, graph_root;
      apply indom_update_of_indom; (typeclass || exact Hin) ].
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
  (* Read/Write/Start/Join/Lock: graph unchanged *)
  1,2,3,6,7: (split;
    [ exact Hedge
    | destruct Hdisj as [HDe | Hgi];
      [ try (left; assumption);
        subst Dp; exfalso;
        match goal with HbD : binds empty _ _ |- _ => applys binds_empty_false HbD; typeclass end
      | right; exact Hgi ] ]).
  (* End/Spawn/Unlock: graph_commit *)
  1,2,3: (
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
  (* Init: graph_root, the only remaining goal *)
  destruct Gp as (C0 & P0).
  split.
  - introv He. unfold graph_edge, graph_root in He.
    forwards (Ha & Hb): Hedge He.
    split; (unfolds graph_indom, graph_root; apply indom_update_of_indom; (typeclass || assumption)).
  - right. unfolds graph_indom, graph_root. apply indom_update_same; typeclass.
Qed.

Lemma play_log_graph_wf :
  forall log D TC G g CH,
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    play_graph_wf D G g.
Proof.
  introv Hplay. inductions Hplay.
  - split.
    + introv He. unfold graph_edge, empty_graph in He. rew_set in He. false.
    + left. reflexivity.
  - forwards Hwf': (>> IHHplay D' TC' G' g'); [ apply JMeq.JMeq_refl | reflexivity | ].
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
      forwards Hanc: (>> IHHplay Hwf0 (@JMeq.JMeq_refl (deltas * commits * graph * commit)%type (empty, empty, (empty, empty), 0)) (eq_refl : (D', TC', G', g') = (D', TC', G', g')) HNm0 Hgtm HNn0 Hgtn Hle HNchm0 HNchn0).
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
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
      forwards Hanc: (>> IHHplay Hwf0 (@JMeq.JMeq_refl (deltas * commits * graph * commit)%type (empty, empty, (empty, empty), 0)) (eq_refl : (D', TC', G', g') = (D', TC', G', g')) HNm0 HNn0 Hlt HNchm0 HNchn0).
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
      forwards Hinv: play_log_inv Hwf0 Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

Lemma hb_spawn_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
      forwards Hanc: (>> IHHplay Hwf0 (@JMeq.JMeq_refl (deltas * commits * graph * commit)%type (empty, empty, (empty, empty), 0)) (eq_refl : (D', TC', G', g') = (D', TC', G', g')) HNm0 HNn0 Hlt HNchm0 HNchn0).
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
      forwards Hinv: play_log_inv Hwf0 Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

Lemma hb_join_pointer_ancestor :
  forall log D TC G g CH m n t1 t2 cm cn,
    wf_log log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
      forwards Hanc: (>> IHHplay Hwf0 (@JMeq.JMeq_refl (deltas * commits * graph * commit)%type (empty, empty, (empty, empty), 0)) (eq_refl : (D', TC', G', g') = (D', TC', G', g')) HNm0 HNn0 Hlt HNchm0 HNchn0).
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
      forwards Hinv: play_log_inv Hwf0 Hplay. destruct Hinv as (_ & Hmax & _).
      applys Hmax Hcmdom.
Qed.

(* [6] A happens-before edge maps to graph ancestry between the recorded pointers. *)
Lemma hb_pointer_ancestor :
  forall log D TC G g CH m n cm cn,
    wf_log log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
  - asserts Hle: (m <= n). { nat_math. }
    applys (>> CH_thread_monotone Hwf Hplay HN1 Hg1 HN2 Hg2 Hle HNchm HNchn).
  - applys (>> hb_lock_pointer_ancestor Hwf Hplay HNu HNl Hlt HNchm HNchn).
  - applys (>> hb_spawn_pointer_ancestor Hwf Hplay HNs HNst Hlt HNchm HNchn).
  - applys (>> hb_join_pointer_ancestor Hwf Hplay HNe HNj Hlt HNchm HNchn).
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
    conflict_free log ->
    wf_log log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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
    | apply graph_writes_graph_root];
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
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett | t0];
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
      * (* read *) left; split.
        -- split; assumption.
        -- introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
           { applys Hnc Hg HNg0 Hgg. } { subst; simpl; auto. }
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
                 { applys Hnc Hg HNg0 Hgg. }
                 { subst ep; simpl; auto. }
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
      * (* init t0: by wf_log the init event must be first, so [log = nil],
           contradicting the prefix write of [x] *)
        destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hinit & _).
        asserts Heq: ((log & event_init t0) = log ++ event_init t0 :: nil).
        { rew_list~. }
        forwards (Heqt & Hnil): Hinit Heq.
        rewrite Hnil in HN0. inverts HN0.
    + (* the write is the last (appended) event *)
      subst E. inverts H.
      left. split.
      * split.
        -- rewrite read_update_same. apply indom_update_same; typeclass.
        -- rewrite read_update_same. rewrite read_update_same. reflexivity.
      * introv Hg HNg Hgg. forwards [HNg0 | (HgN & HgE)]: Nth_last_inv HNg.
        { forwards Hglt: Nth_inbound HNg0. nat_math. }
        { subst ep; simpl; auto. }
Qed.

(* [13] The value a reader sees ([is_latest_value] at its pointer) is the last
   write of [x] in the log. *)
Lemma last_write_visible_commit :
  forall log D TC G g CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
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

(* [14] Wrapper around [last_write_visible_commit]. *)
Lemma hb_last_write_visible :
  forall log D TC G g CH m n tm x vm en,
    wf_log log ->
    conflict_free log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    LibList.Nth m log (event_write tm x vm) ->
    (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m) ->
    x \notindom (D[tm]) ->
    LibList.Nth n log en ->
    hb log m n ->
    is_latest_value G (TC[get_thread en]) x vm.
Proof.
  introv Hwf Hcf Hplay HNm Hlast Hndom HNn Hhb.
  applys* last_write_visible_commit.
Qed.

(* [15] GOAL: the value a thread reads globally is the last write of [x] in the
   log.  Linear drops Branching's [conflict_free_graph G] premise: it follows
   from [play_log_inv] (total order) via [total_order_conflict_free_graph]. *)
Lemma conflict_free_last_global_write :
  forall log D TC G g CH t x v c,
    conflict_free (log & event_read t x v) ->
    wf_log (log & event_read t x v) ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    x \notindom (D[t]) ->
    t \indom TC ->
    TC[t] = c ->
    is_latest_value G c x v ->
    exists t' log', LibList.filter (fun e => writes_variable x e) log = log' & event_write t' x v.
Proof.
  introv Hcf Hwf Hplay Hndom Hdom HTC Hval.
  forwards Hwf': wf_log_last_inv Hwf.
  forwards Hinv: play_log_inv Hwf' Hplay.
  destruct Hinv as (Htot & _ & _).
  forwards Hcfg: total_order_conflict_free_graph Htot.
  forwards (lw & tL & vL & Hfilter): is_latest_value_log_write Hplay Hval.
  forwards (L & HNL & Hlast): last_write_position Hfilter.
  forwards HLlt: Nth_inbound HNL.
  asserts Hplayf: (exists CHf, play_log (log & event_read t x v)
                     (empty, empty, empty_graph, root_commit) (D, TC, G, g) CHf).
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
  asserts Hacc: (accesses_variable x (event_read t x v)). { reflexivity. }
  forwards Hhb: Hcf HNLf HNread Hacc HLlt.
  asserts HndomL: (x \notindom (D[tL])).
  { destruct (classic (tL = t)) as [-> | Hne].
    - exact Hndom.
    - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb.
      simpl. congruence. }
  forwards Hlv: (>> hb_last_write_visible Hwf Hcf Hplayf HNLf Hlastf HndomL HNread Hhb).
  simpl in Hlv. rewrite HTC in Hlv.
  forwards ->: is_latest_value_inj Hcfg Hlv Hval.
  exists tL lw. exact Hfilter.
Qed.

(* ============================================================================
   Completeness ingredient 1: a thread's pending delta is always conflict-free
   to push onto the global head, when the log is conflict-free.
   ============================================================================ *)

(* Any committed graph write of [j] is an ancestor of [t]'s pointer, when [t]
   has a pending (uncommitted) write of [j].  [t]'s pending write is the last
   one (conflict-freedom), so every committed [j]-writer precedes it. *)
Lemma delta_writer_ancestor :
  forall log D TC G g CH t j vt c vc,
    wf_log log ->
    conflict_free log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    t \indom D ->
    binds (D[t]) j vt ->
    graph_writes G c j vc ->
    ancestor G c (TC[t]).
Proof.
  introv Hwf Hcf Hplay Htdom Hbd Hgw.
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
      forwards Hhb: (>> Hcf HNkt HNkc Hacc Hlt).
      asserts Hgtcne: (get_thread (event_write tc j vc) <> t). { simpl. exact Htne. }
      forwards (f'' & ef'' & Hktf'' & HNf'' & Hgf'' & Hcef'' & Hhbf''):
        hb_cross_thread_flush Hhb HNkt Hgtt HNkc Hgtcne.
      applys Hns Hktf'' HNf'' Hgf'' Hcef''.
    + asserts Hltba: (kc < kt). nat_math.
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

(* When replaying a conflict-free log, a thread's pending delta is disjoint from
   the changes between its pointer and the head: pushing [D[t]] onto the head [g]
   is conflict-free.  (This is the [dom (D[t])] half of Branching's
   [conflict_free_merge_holds]; Linear needs no merge, so the change-set/
   change-set half is unnecessary.) *)
Lemma lin_conflict_free_holds :
  forall log D TC G g CH t,
    wf_log log ->
    conflict_free log ->
    play_log log (empty, empty, empty_graph, root_commit) (D, TC, G, g) CH ->
    t \indom D ->
    t \indom TC ->
    graph_indom G g ->
    lin_conflict_free (D[t]) (TC[t]) g G.
Proof.
  introv Hwf Hcf Hplay Htd Htc Hg.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct G as (C & P). destruct Hpgwf as (Hedge & _).
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
  applys Hnanc. applys (>> delta_writer_ancestor Hwf Hcf Hplay Htd Hbdj Hgwc).
Qed.
