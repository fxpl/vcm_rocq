From Vcm Require Import Common.
From Vcm Require Import Graph.

Lemma graph_binds_inj :
  forall G h d1 d2,
    graph_binds G h d1 ->
    graph_binds G h d2 ->
    d1 = d2.
Proof.
  introv Hbinds1 Hbinds2.
  destruct G as (C & P).
  unfolds graph_binds.
  applys* binds_inj.
  typeclass.
Qed.

Lemma graph_binds_to_indom :
  forall G h d,
    graph_binds G h d ->
    graph_indom G h.
Proof.
  introv Hbinds.
  destruct* G as (C & P).
Qed.

Hint Resolve graph_binds_to_indom : vcm.

Lemma ancestor_refl :
  forall G h,
    ancestor G h h.
Proof.
  apply AncestorRefl.
Qed.

Hint Resolve ancestor_refl : vcm.

Lemma ancestor_trans :
  forall G h h' h'',
    ancestor G h h' ->
    ancestor G h' h'' ->
    ancestor G h h''.
Proof.
  introv Hanc1 Hanc2.
  gen h.
  induction~ Hanc2.
  introv Hanc1.
  apply AncestorTrans with (h2 := h2); auto_star.
Qed.

Hint Resolve ancestor_trans : vcm.

Lemma commit_fresh_not_indom :
  forall G c,
    commit_fresh G c ->
    ~ graph_indom G c.
Proof.
  introv Hfresh Hin. destruct G as (C & P). applys Hfresh Hin.
Qed.

(* In a well-formed graph, a commit with no data has no proper descendants:
   it is not an edge endpoint, so no ancestry path can leave it. This subsumes
   the explicit "fresh leaf" hypothesis previously needed for graph lemmas. *)
Lemma ancestor_commit_fresh_eq :
  forall G a z,
    wf_graph G ->
    ancestor G a z ->
    commit_fresh G a ->
    z = a.
Proof.
  introv Hwf Hanc.
  destruct Hwf as (_ & _ & Hedge_wf).
  induction Hanc as [h | h1 h2 h3 Hsub IH Hedge]; introv Hfresh.
  - reflexivity.
  - forwards ->: IH Hfresh.
    forwards (Hin & _): Hedge_wf Hedge.
    false. applys commit_fresh_not_indom Hfresh Hin.
Qed.

Lemma mem_le_sum : forall (n : nat) (l : list nat),
  mem n l -> n <= fold_right plus 0 l.
Proof.
  introv Hmem. induction Hmem; rewrite fold_right_cons; nat_math.
Qed.

Lemma exists_commit_fresh :
  forall G,
    wf_graph G ->
    exists h, commit_fresh G h.
Proof.
  introv [Hfin _]. destruct G as [C P].
  simpl in Hfin.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  exists (1 + fold_right plus 0 l).
  unfolds commit_fresh. simpl.
  introv Hindom.
  forwards Hmem: Hcov Hindom.
  forwards Hle: mem_le_sum Hmem.
  nat_math.
Qed.

Lemma change_set_eq_empty :
  forall G h,
    change_set G h h = empty.
Proof.
  intros. apply is_empty_prove.
  introv Hmem. unfolds change_set.
  destruct G as (C & P).
  destruct* Hmem as (h' & Hdom & Hanc & Hnanc).
Qed.

Example id_parent_merge :
  forall G h,
    conflict_free_merge empty h h G.
Proof.
  introv.
  unfolds conflict_free_merge. rew_set.
  introv Hmem1 Hmem2.
  rewrite change_set_eq_empty in Hmem2.
  inverts Hmem2.
Qed.

Lemma graph_writes_to_indom :
  forall G c i v,
    graph_writes G c i v ->
    graph_indom G c.
Proof.
  introv (d & Hbinds & _). eauto with vcm.
Qed.

Hint Resolve graph_writes_to_indom : vcm.

(* With the maximal-writer definition we can only expose the witnessing writer's
   membership in the graph, not [h]'s (ancestry does not imply domain
   membership). This is the fact the injectivity proof actually needs. *)
Lemma is_latest_value_writer_indom :
  forall G i v h,
    is_latest_value G h i v ->
    exists c, graph_writes G c i v /\ graph_indom G c /\ ancestor G c h.
Proof.
  introv (c & Hwrites & Hanc & _). exists c. splits*.
Qed.

Hint Resolve is_latest_value_writer_indom : vcm.

Lemma is_latest_value_inj :
  forall G i v1 v2 h,
    conflict_free_graph G ->
    is_latest_value G h i v1 ->
    is_latest_value G h i v2 ->
    v1 = v2.
Proof.
  introv Hcf (c1 & Hw1 & Hanc1 & Hmax1) (c2 & Hw2 & Hanc2 & Hmax2).
  (* Both [c1] and [c2] write [i] and are ancestors of [h]; show they are
     comparable, then maximality collapses them to a single writer. *)
  asserts Hcmp: (ancestor G c1 c2 \/ ancestor G c2 c1).
  { (* Otherwise [i] would lie in both [change_set G c1 c2] and
       [change_set G c2 c1], contradicting conflict-freedom. *)
    destruct (classic (ancestor G c1 c2)) as [|Hn12]; auto.
    destruct (classic (ancestor G c2 c1)) as [|Hn21]; auto.
    false.
    destruct Hw1 as (d1 & Hb1 & Hbd1).
    destruct Hw2 as (d2 & Hb2 & Hbd2).
    asserts Hdom1: (graph_indom G c1). { eauto with vcm. }
    asserts Hdom2: (graph_indom G c2). { eauto with vcm. }
    forwards~ Hcfm: Hcf Hdom1 Hdom2.
    unfold conflict_free_merge in Hcfm. rew_set in Hcfm.
    (* [i] is in [change_set G c2 c1]: witness [c1], which writes [i], is an
       ancestor of [c1] but (by [Hn12]) not of [c2]. *)
    asserts Hin_c2c1: (i \in change_set G c2 c1).
    { destruct G as (C & P). unfold change_set. exists c1.
      forwards Hr: read_of_binds Hb1.
      unfold commit_data, staging_area in *.
      splits.
      - rewrite Hr. applys indom_of_binds Hbd1. typeclass.
      - apply ancestor_refl.
      - auto. }
    (* ... and in [change_set G c1 c2]: witness [c2], not an ancestor of [c1]
       by [Hn21]. *)
    asserts Hin_c1c2: (i \in change_set G c1 c2).
    { destruct G as (C & P). unfold change_set. exists c2.
      forwards Hr: read_of_binds Hb2.
      unfold commit_data, staging_area in *.
      splits.
      - rewrite Hr. applys indom_of_binds Hbd2. typeclass.
      - apply ancestor_refl.
      - auto. }
    applys Hcfm i; rew_set; auto_star. }
  (* Comparable + maximal ==> same writer ==> same value. *)
  destruct Hcmp as [H12 | H21].
  - forwards ->: Hmax1 Hw2 H12 Hanc2.
    destruct Hw1 as (d1 & Hb1 & Hbd1).
    destruct Hw2 as (d2 & Hb2 & Hbd2).
    forwards ->: graph_binds_inj Hb1 Hb2.
    applys binds_inj Hbd1 Hbd2. typeclass.
  - forwards ->: Hmax2 Hw1 H21 Hanc1.
    destruct Hw1 as (d1 & Hb1 & Hbd1).
    destruct Hw2 as (d2 & Hb2 & Hbd2).
    forwards ->: graph_binds_inj Hb1 Hb2.
    applys binds_inj Hbd1 Hbd2. typeclass.
Qed.

(* TODO: Add these as hints *)

(* Ancestry ignores the data component and only grows when edges are added, so
   committing [c'] (which only adds the edge [(c, c')]) preserves all existing
   ancestry. *)
Lemma ancestor_graph_commit :
  forall G c c' d x y,
    ancestor G x y ->
    ancestor (graph_commit G c c' d) x y.
Proof.
  introv Hanc. destruct G as (C & P). unfold graph_commit.
  induction Hanc.
  - apply ancestor_refl.
  - applys AncestorTrans IHHanc. rew_set; auto_star.
Qed.

(* Conversely, if [c'] is a fresh leaf in [G] (it has no proper descendants),
   then committing it cannot create any new ancestry into a commit other than
   [c'] itself: the only new edge [(c, c')] points *into* [c'], and [c'] has no
   outgoing edges to extend a path through. *)
Lemma ancestor_graph_commit_inv :
  forall G c c' d x y,
    (forall z, ancestor G c' z -> z = c') ->
    y <> c' ->
    ancestor (graph_commit G c c' d) x y ->
    ancestor G x y.
Proof.
  introv Hsink. intros Hneq Hanc.
  destruct G as (C & P). unfold graph_commit in Hanc.
  gen Hneq. induction Hanc; introv Hneq.
  - apply ancestor_refl.
  - rew_set in H. destruct H as [Heq | Hedge].
    + (* edge is the new (c, c'): forces h3 = c', contradicting [Hneq] *)
      inverts Heq. congruence.
    + (* edge already in P; its source [h2] cannot be [c'] (else [Hsink] would
         force h3 = c') *)
      asserts Hh2: (h2 <> c').
      { intro Heqh2. subst h2.
        asserts Hanc_c': (ancestor (C, P) c' h3).
        { apply AncestorTrans with (h2 := c'). apply ancestor_refl. exact Hedge. }
        forwards: Hsink Hanc_c'. congruence. }
      apply AncestorTrans with (h2 := h2).
      * applys~ IHHanc.
      * exact Hedge.
Qed.

(* Writes by commits other than [c'] are unaffected by committing [c']. *)
Lemma graph_writes_graph_commit :
  forall G c c' d x i v,
    x <> c' ->
    graph_writes G x i v ->
    graph_writes (graph_commit G c c' d) x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_commit.
  exists dd. split~. applys~ binds_update_neq.
Qed.

Lemma graph_writes_graph_commit_inv :
  forall G c c' d x i v,
    x <> c' ->
    graph_writes (graph_commit G c c' d) x i v ->
    graph_writes G x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_commit.
  exists dd. split~. applys~ binds_update_neq_inv Hb.
Qed.

(* Committing a fresh commit [c'] does not change the latest value visible at
   any pre-existing commit [h <> c']. The [commit_fresh] hypothesis (no data) is
   not enough on its own: a data-less [c'] sitting on a path to [h] would become
   the maximal writer once given data [d]. In a well-formed graph this cannot
   happen — [wf_graph] forces [c'] to be a leaf (see [ancestor_commit_fresh_eq]). *)
Lemma is_latest_value_commit_fresh :
  forall G c c' d h i v,
    wf_graph G ->
    commit_fresh G c' ->
    h <> c' ->
    is_latest_value (graph_commit G c c' d) h i v ->
    is_latest_value G h i v.
Proof.
  introv Hwf Hfresh Hneq (cc & Hw & Hanc & Hmax).
  asserts Hsink: (forall z, ancestor G c' z -> z = c').
  { introv Hz. applys ancestor_commit_fresh_eq Hwf Hz Hfresh. }
  forwards Hanc_G: ancestor_graph_commit_inv Hsink Hneq Hanc.
  asserts Hcc_neq: (cc <> c').
  { intro. subst. forwards: Hsink Hanc_G. congruence. }
  forwards Hw_G: graph_writes_graph_commit_inv Hcc_neq Hw.
  exists cc. splits~.
  intros cc' v' Hw' Hanc1 Hanc2.
  (* a writer in [G] lives in [dom C], so it cannot be the fresh [c'] *)
  asserts Hcc'_neq: (cc' <> c').
  { intro Heq. subst. forwards Hdom: graph_writes_to_indom Hw'.
    applys commit_fresh_not_indom Hfresh Hdom. }
  applys Hmax cc' v'.
  - applys~ graph_writes_graph_commit.
  - applys~ ancestor_graph_commit.
  - applys~ ancestor_graph_commit.
Qed.

(* The merge counterparts of the [graph_commit] helpers above. A merge adds the
   fresh commit [h] with two edges [(p2, h)] and [(p1, h)] pointing into it, so
   like a commit it only grows ancestry and the new node is a leaf. *)
Lemma ancestor_graph_merge :
  forall G p1 p2 h x y,
    ancestor G x y ->
    ancestor (graph_merge G p1 p2 h) x y.
Proof.
  introv Hanc. destruct G as (C & P). unfold graph_merge.
  induction Hanc as [a | a mid b Hsub IH Hedge].
  - apply ancestor_refl.
  - applys AncestorTrans IH. rew_set; auto_star.
Qed.

Lemma ancestor_graph_merge_inv :
  forall G p1 p2 h x y,
    (forall z, ancestor G h z -> z = h) ->
    y <> h ->
    ancestor (graph_merge G p1 p2 h) x y ->
    ancestor G x y.
Proof.
  introv Hsink. intros Hneq Hanc.
  destruct G as (C & P). unfold graph_merge in Hanc.
  gen Hneq. induction Hanc as [a | a mid b Hsub IH Hedge]; introv Hneq.
  - apply ancestor_refl.
  - rew_set in Hedge. destruct Hedge as [Heq | [Heq | HedgeP]].
    + (* edge is (p2, h): forces b = h, contradicting [Hneq] *)
      inverts Heq. congruence.
    + (* edge is (p1, h): likewise forces b = h *)
      inverts Heq. congruence.
    + (* edge already in P; its source [mid] cannot be [h] (else [Hsink]) *)
      asserts Hmid: (mid <> h).
      { intro Heqm. subst mid.
        asserts Hanc_h: (ancestor (C, P) h b).
        { apply AncestorTrans with (h2 := h). apply ancestor_refl. exact HedgeP. }
        forwards: Hsink Hanc_h. congruence. }
      apply AncestorTrans with (h2 := mid).
      * applys~ IH.
      * exact HedgeP.
Qed.

Lemma graph_writes_graph_merge :
  forall G p1 p2 h x i v,
    x <> h ->
    graph_writes G x i v ->
    graph_writes (graph_merge G p1 p2 h) x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_merge.
  exists dd. split~. applys~ binds_update_neq.
Qed.

Lemma graph_writes_graph_merge_inv :
  forall G p1 p2 h x i v,
    x <> h ->
    graph_writes (graph_merge G p1 p2 h) x i v ->
    graph_writes G x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_merge.
  exists dd. split~. applys~ binds_update_neq_inv Hb.
Qed.

(* Merging into a fresh commit [h] preserves the latest value visible at any
   pre-existing commit [h' <> h]. The merge commit carries empty staging, so it
   writes nothing; [wf_graph] forces it to be a leaf, so it adds no ancestry into
   existing commits. Mirrors [is_latest_value_commit_fresh]. *)
Lemma is_latest_value_graph_merge :
  forall G p1 p2 h h' i v,
    wf_graph G ->
    commit_fresh G h ->
    h' <> h ->
    is_latest_value (graph_merge G p1 p2 h) h' i v ->
    is_latest_value G h' i v.
Proof.
  introv Hwf Hfresh Hneq (cc & Hw & Hanc & Hmax).
  asserts Hsink: (forall z, ancestor G h z -> z = h).
  { introv Hz. applys ancestor_commit_fresh_eq Hwf Hz Hfresh. }
  forwards Hanc_G: ancestor_graph_merge_inv Hsink Hneq Hanc.
  asserts Hcc_neq: (cc <> h).
  { intro. subst. forwards: Hsink Hanc_G. congruence. }
  forwards Hw_G: graph_writes_graph_merge_inv Hcc_neq Hw.
  exists cc. splits~.
  intros cc' v' Hw' Hanc1 Hanc2.
  asserts Hcc'_neq: (cc' <> h).
  { intro Heq. subst. forwards Hdom: graph_writes_to_indom Hw'.
    applys commit_fresh_not_indom Hfresh Hdom. }
  applys Hmax cc' v'.
  - applys~ graph_writes_graph_merge.
  - applys~ ancestor_graph_merge.
  - applys~ ancestor_graph_merge.
Qed.

Lemma ancestor_graph_root :
  forall G c x y,
    ancestor G x y ->
    commit_fresh G c ->
    ancestor (graph_root G c) x y.
Proof.
  introv Hanc Hfresh. destruct G as (C & P). unfold graph_root.
  induction Hanc.
  - apply ancestor_refl.
  - applys AncestorTrans IHHanc. rew_set; auto_star.
Qed.

Lemma ancestor_graph_root_inv :
  forall G c x y,
    (forall z, ancestor G c z -> z = c) ->
    y <> c ->
    ancestor (graph_root G c ) x y ->
    ancestor G x y.
Proof.
  introv Hsink Hneq Hanc.
  destruct G as (C & P). unfolds graph_root.
  gen Hneq. induction Hanc; introv Hneq.
  - apply ancestor_refl.
  - asserts Hh2: (h2 <> c).
    { intro Heqh2. subst h2.
      asserts Hanc_c': (ancestor (C, P) c h3).
      { apply AncestorTrans with (h2 := c); auto. apply ancestor_refl. }
      forwards: Hsink Hanc_c'. congruence. }
    apply AncestorTrans with (h2 := h2); auto.
Qed.

Lemma graph_writes_graph_root :
  forall G c x i v,
    x <> c ->
    graph_writes G x i v ->
    graph_writes (graph_root G c) x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_commit.
  exists dd. split~. applys~ binds_update_neq.
Qed.

Lemma graph_writes_graph_root_inv :
  forall G c x i v,
    x <> c ->
    graph_writes (graph_root G c) x i v ->
    graph_writes G x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_commit.
  exists dd. split~. applys~ binds_update_neq_inv Hb.
Qed.


(* ---------------------------------------------------------------------- *)
(* Lemmas relocated here from BranchingEquiv.v (organization pass).          *)
(* ---------------------------------------------------------------------- *)

(* The new commit created by a commit/merge is a descendant of its parent(s). *)
Lemma ancestor_graph_commit_edge :
  forall G c c' d, ancestor (graph_commit G c c' d) c c'.
Proof.
  intros. destruct G as (C & P). unfold graph_commit.
  apply AncestorTrans with (h2 := c). apply ancestor_refl. rew_set; auto_star.
Qed.

Lemma ancestor_graph_merge_edge_l :
  forall G c1 c2 c', ancestor (graph_merge G c1 c2 c') c2 c'.
Proof.
  intros. destruct G as (C & P). unfold graph_merge.
  apply AncestorTrans with (h2 := c2). apply ancestor_refl. rew_set; auto_star.
Qed.

Lemma ancestor_graph_merge_edge_r :
  forall G c1 c2 c', ancestor (graph_merge G c1 c2 c') c1 c'.
Proof.
  intros. destruct G as (C & P). unfold graph_merge.
  apply AncestorTrans with (h2 := c1). apply ancestor_refl. rew_set; auto_star.
Qed.

(* A binding in the empty map is impossible. *)
Lemma binds_empty_false :
  forall A B {IB : Inhab B} (x : A) (v : B), binds (\{} : map A B) x v -> False.
Proof.
  intros A B IB x v Hb. lets Hin: (indom_of_binds Hb). applys indom_empty_inv Hin.
Qed.

(* The freshly committed commit carries exactly the flushed staging area. *)
Lemma graph_writes_graph_commit_same :
  forall G c c' d i v,
    graph_writes (graph_commit G c c' d) c' i v -> binds d i v.
Proof.
  introv (dd & Hgb & Hbd). destruct G as (C & P).
  unfolds graph_commit, graph_binds.
  asserts Hdd: (dd = d). { applys binds_inj Hgb; (apply binds_update_same || typeclass). }
  subst dd. exact Hbd.
Qed.

(* The merge commit carries empty staging, so it writes nothing. *)
Lemma graph_writes_graph_merge_same_false :
  forall G p1 p2 h i v,
    graph_writes (graph_merge G p1 p2 h) h i v -> False.
Proof.
  introv (dd & Hgb & Hbd). destruct G as (C & P).
  unfolds graph_merge, graph_binds.
  asserts Hdd: (dd = empty). { applys binds_inj Hgb; (apply binds_update_same || typeclass). }
  subst dd. applys binds_empty_false Hbd; typeclass.
Qed.

(* The freshly committed commit writes whatever its flushed staging holds. *)
Lemma graph_writes_graph_commit_new :
  forall G c c' d i v, binds d i v -> graph_writes (graph_commit G c c' d) c' i v.
Proof.
  introv Hbd. exists d. split; [ | exact Hbd ].
  destruct G as (C & P). unfold graph_commit, graph_binds. apply binds_update_same.
Qed.

Lemma graph_writes_graph_root_same_false :
  forall G c i v,
    graph_writes (graph_root G c) c i v -> False.
Proof.
  introv (dd & Hgb & Hbd). destruct G as (C & P).
  unfolds graph_root, graph_binds.
  forwards: binds_update_same_inv Hgb.
  subst.
  applys binds_empty_false Hbd; typeclass.
Qed.

(* A commit with no outgoing edge has no proper descendants. *)
Lemma ancestor_no_out_edge :
  forall G a z,
    ancestor G a z ->
    (forall y, ~ graph_edge G a y) ->
    z = a.
Proof.
  introv Hanc. induction Hanc as [h | h1 h2 h3 Hsub IH Hedge]; introv Hno.
  - reflexivity.
  - forwards Heq: IH Hno. subst h2. false. applys Hno. exact Hedge.
Qed.

(* The commit a pointer-map binds lives in the graph domain, given that all the
   map's pointers do. *)
Lemma binds_graph_indom :
  forall (M : map nat commit) (C : commit_data) (P : commit_rels) t c,
    binds M t c ->
    (forall t', t' \indom M -> graph_indom (C, P) (M[t'])) ->
    graph_indom (C, P) c.
Proof.
  introv Hb HM. lets Hrd: read_of_binds Hb. lets Hin: (indom_of_binds Hb).
  rewrite <- Hrd. applys HM Hin.
Qed.

(* The source of an ancestry edge in a play_log graph is in the domain (edges
   connect domain commits), unless the path is empty. *)
Lemma ancestor_src_indom :
  forall G h k,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    ancestor G h k ->
    graph_indom G h \/ h = k.
Proof.
  introv Hedge Hanc. induction Hanc as [h | h1 h2 h3 Hsub IH Hstep].
  - right. reflexivity.
  - destruct IH as [Hin | Heq].
    + left. exact Hin.
    + subst h2. left.
      asserts Hed: (graph_edge G h1 h3). { destruct G as (C & P). exact Hstep. }
      forwards (Ha & _): Hedge Hed. exact Ha.
Qed.

(* A fresh commit (not in the graph, all edges connecting domain commits) is a
   sink: it has no proper descendants. *)
Lemma commit_fresh_sink :
  forall G c',
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G c' ->
    forall z, ancestor G c' z -> z = c'.
Proof.
  introv Hedge Hfresh Hanc. applys ancestor_no_out_edge Hanc.
  introv He. forwards (Ha & _): Hedge He.
  destruct G as (C0 & P0). applys Hfresh Ha.
Qed.
