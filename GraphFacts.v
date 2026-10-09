From Vcm Require Import Common.
From Vcm Require Import Graph.

Theorem init_graph_wf :
  wf_graph (graph_root root_commit).
Proof.
  unfolds graph_root.
  splits.
  - unfolds finite. rewrite dom_update.
    rewrite dom_empty.
    apply LibSet.finite_union;
      auto using LibSet.finite_empty, LibSet.finite_single.
  - introv Hanc. inverts~ Hanc.
    rew_set in *. false.
  - introv He. inverts He.
Qed.

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

(* A commit's data pins the value of any variable it writes: two [graph_writes]
   facts about the SAME commit agree on the value. *)
Lemma graph_writes_inj :
  forall G c x v1 v2,
    graph_writes G c x v1 ->
    graph_writes G c x v2 ->
    v1 = v2.
Proof.
  introv (d1 & Hb1 & Hbd1) (d2 & Hb2 & Hbd2).
  forwards ->: graph_binds_inj Hb1 Hb2.
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
  forall G c c' c'',
    ancestor G c c' ->
    ancestor G c' c'' ->
    ancestor G c c''.
Proof.
  introv Hanc1 Hanc2.
  gen c.
  induction~ Hanc2.
  introv Hanc1.
  apply AncestorTrans with (c2 := c2); auto_star.
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
   the explicit "fresh leaf" hypothesis needed by other graph lemmas. *)
Lemma ancestor_commit_fresh_eq :
  forall G a z,
    wf_graph G ->
    ancestor G a z ->
    commit_fresh G a ->
    z = a.
Proof.
  introv Hwf Hanc.
  destruct Hwf as (_ & _ & Hedge_wf).
  induction Hanc as [c | c1 c2 c3 Hsub IH Hedge]; introv Hfresh.
  - reflexivity.
  - forwards ->: IH Hfresh.
    forwards (Hin & _): Hedge_wf Hedge.
    false. applys commit_fresh_not_indom Hfresh Hin.
Qed.

Lemma exists_commit_fresh :
  forall G,
    wf_graph G ->
    exists c, commit_fresh G c.
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
  forall G c,
    change_set G c c = empty.
Proof.
  intros. apply is_empty_prove.
  introv Hmem. unfolds change_set.
  destruct G as (C & P).
  destruct* Hmem as (_ & c' & Hdom & Hanc & Hnanc).
Qed.

Example id_parent_merge :
  forall G c,
    conflict_free_merge empty c c G.
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
   membership in the graph, not [c]'s (ancestry does not imply domain
   membership). This is the fact the injectivity proof actually needs. *)
Lemma is_latest_value_writer_indom :
  forall G i v c,
    is_latest_value G c i v ->
    exists c', graph_writes G c' i v /\ graph_indom G c' /\ ancestor G c' c.
Proof.
  introv (c' & Hwrites & Hanc & _). exists c'. splits*.
Qed.

Hint Resolve is_latest_value_writer_indom : vcm.

(* Core of the uniqueness of the latest value: if any two writers of [i] below
   [c] that could be latest are comparable, maximality collapses them to one
   commit. *)
Lemma is_latest_value_inj_comparable :
  forall G i v1 v2 c,
    (forall c1 c2,
       graph_writes G c1 i v1 -> graph_writes G c2 i v2 ->
       ancestor G c1 c -> ancestor G c2 c ->
       ancestor G c1 c2 \/ ancestor G c2 c1) ->
    is_latest_value G c i v1 ->
    is_latest_value G c i v2 ->
    v1 = v2.
Proof.
  introv Hcmp (c1 & Hw1 & Hanc1 & Hmax1) (c2 & Hw2 & Hanc2 & Hmax2).
  destruct (Hcmp c1 c2 Hw1 Hw2 Hanc1 Hanc2) as [H12 | H21].
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

(* Two writers of the same non-volatile variable that merge conflict-free are
   comparable: otherwise the variable would lie in both [change_set G c1 c2] and
   [change_set G c2 c1], contradicting conflict-freedom. (Volatiles are ignored
   by conflict checking, so this does not cover them.) *)
Lemma conflict_free_merge_writers_comparable :
  forall G i v1 v2 c1 c2,
    i \notin Volatiles ->
    graph_writes G c1 i v1 ->
    graph_writes G c2 i v2 ->
    conflict_free_merge empty c1 c2 G ->
    ancestor G c1 c2 \/ ancestor G c2 c1.
Proof.
  introv Hnv Hw1 Hw2 Hcfm.
  destruct (classic (ancestor G c1 c2)) as [|Hn12]; auto.
  destruct (classic (ancestor G c2 c1)) as [|Hn21]; auto.
  false.
  destruct Hw1 as (d1 & Hb1 & Hbd1).
  destruct Hw2 as (d2 & Hb2 & Hbd2).
  unfold conflict_free_merge in Hcfm. rew_set in Hcfm.
  asserts Hin_c2c1: (i \in change_set G c2 c1).
  { destruct G as (C & P). unfold change_set. split; [exact Hnv | ]. exists c1.
    forwards Hr: read_of_binds Hb1.
    unfold commit_data, diff in *.
    splits.
    - rewrite Hr. applys indom_of_binds Hbd1. typeclass.
    - apply ancestor_refl.
    - auto. }
  asserts Hin_c1c2: (i \in change_set G c1 c2).
  { destruct G as (C & P). unfold change_set. split; [exact Hnv | ]. exists c2.
    forwards Hr: read_of_binds Hb2.
    unfold commit_data, diff in *.
    splits.
    - rewrite Hr. applys indom_of_binds Hbd2. typeclass.
    - apply ancestor_refl.
    - auto. }
  applys Hcfm i; rew_set; auto_star.
Qed.

(* In a conflict-free graph the latest value of a NON-volatile variable is
   unique (volatiles are ignored by conflict checking, so this does not cover
   them). *)
Lemma is_latest_value_inj :
  forall G i v1 v2 c,
    i \notin Volatiles ->
    conflict_free_graph G ->
    is_latest_value G c i v1 ->
    is_latest_value G c i v2 ->
    v1 = v2.
Proof.
  introv Hnv Hcf Hl1 Hl2.
  applys is_latest_value_inj_comparable Hl1 Hl2.
  introv Hw1 Hw2 _ _.
  asserts Hdom1: (graph_indom G c1). { eauto with vcm. }
  asserts Hdom2: (graph_indom G c2). { eauto with vcm. }
  applys conflict_free_merge_writers_comparable Hnv Hw1 Hw2.
  applys Hcf Hdom1 Hdom2.
Qed.

(* The latest value of a non-volatile [i] at [c] is unique when the history
   reachable from [c] has no conflicting fork. This is the per-view analogue of
   [is_latest_value_inj]: it does not require the whole graph to be
   conflict-free. *)
Lemma is_latest_value_inj_view :
  forall G i v1 v2 c,
    i \notin Volatiles ->
    view_conflict_free G c ->
    is_latest_value G c i v1 ->
    is_latest_value G c i v2 ->
    v1 = v2.
Proof.
  introv Hnv Hview Hl1 Hl2.
  applys is_latest_value_inj_comparable Hl1 Hl2.
  introv Hw1 Hw2 Hanc1 Hanc2.
  applys conflict_free_merge_writers_comparable Hnv Hw1 Hw2.
  applys Hview Hanc1 Hanc2.
Qed.

(* In a totally ordered graph (the Linear model) the latest value of ANY
   variable is unique, since any two writers are comparable. *)
Lemma is_latest_value_inj_total :
  forall G i v1 v2 c,
    total_order G ->
    is_latest_value G c i v1 ->
    is_latest_value G c i v2 ->
    v1 = v2.
Proof.
  introv Htot Hl1 Hl2.
  applys is_latest_value_inj_comparable Hl1 Hl2.
  introv Hw1 Hw2 _ _.
  applys Htot; eauto with vcm.
Qed.

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
    + (* edge is the new (c, c'): forces c3 = c', contradicting [Hneq] *)
      inverts Heq. congruence.
    + (* edge already in P; its source [c2] cannot be [c'] (else [Hsink] would
         force c3 = c') *)
      asserts Hc2: (c2 <> c').
      { intro Heqc2. subst c2.
        asserts Hanc_c': (ancestor (C, P) c' c3).
        { apply AncestorTrans with (c2 := c'). apply ancestor_refl. exact Hedge. }
        forwards: Hsink Hanc_c'. congruence. }
      apply AncestorTrans with (c2 := c2).
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
   any pre-existing commit [c <> c']. The [commit_fresh] hypothesis (no data) is
   not enough on its own: a data-less [c'] sitting on a path to [c] would become
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
        { apply AncestorTrans with (c2 := h). apply ancestor_refl. exact HedgeP. }
        forwards: Hsink Hanc_h. congruence. }
      apply AncestorTrans with (c2 := mid).
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

(* ---------------------------------------------------------------------- *)
(* Basic ancestry facts about freshly created commits.                    *)
(* ---------------------------------------------------------------------- *)

(* The new commit created by a commit/merge is a descendant of its parent(s). *)
Lemma ancestor_graph_commit_edge :
  forall G c c' d, ancestor (graph_commit G c c' d) c c'.
Proof.
  intros. destruct G as (C & P). unfold graph_commit.
  apply AncestorTrans with (c2 := c). apply ancestor_refl. rew_set; auto_star.
Qed.

Lemma ancestor_graph_merge_edge_l :
  forall G c1 c2 c', ancestor (graph_merge G c1 c2 c') c2 c'.
Proof.
  intros. destruct G as (C & P). unfold graph_merge.
  apply AncestorTrans with (c2 := c2). apply ancestor_refl. rew_set; auto_star.
Qed.

Lemma ancestor_graph_merge_edge_r :
  forall G c1 c2 c', ancestor (graph_merge G c1 c2 c') c1 c'.
Proof.
  intros. destruct G as (C & P). unfold graph_merge.
  apply AncestorTrans with (c2 := c1). apply ancestor_refl. rew_set; auto_star.
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

(* A commit with no outgoing edge has no proper descendants. *)
Lemma ancestor_no_out_edge :
  forall G a z,
    ancestor G a z ->
    (forall y, ~ graph_edge G a y) ->
    z = a.
Proof.
  introv Hanc. induction Hanc as [h | c1 c2 c3 Hsub IH Hedge]; introv Hno.
  - reflexivity.
  - forwards Heq: IH Hno. subst c2. false. applys Hno. exact Hedge.
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
  introv Hedge Hanc. induction Hanc as [h | c1 c2 c3 Hsub IH Hstep].
  - right. reflexivity.
  - destruct IH as [Hin | Heq].
    + left. exact Hin.
    + subst c2. left.
      asserts Hed: (graph_edge G c1 c3). { destruct G as (C & P). exact Hstep. }
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

(* Committing a fresh commit [c'] onto a parent [c] already in the graph
   preserves well-formedness. Freshness of [c'] keeps it a sink, so the new
   edge [(c, c')] cannot close a cycle; [c \indom G] is what ties the new edge's
   source into the data domain. *)
Lemma graph_commit_wf :
  forall G c c' d,
    wf_graph G ->
    commit_fresh G c' ->
    graph_indom G c ->
    wf_graph (graph_commit G c c' d).
Proof.
  introv Hwf Hfresh Hin.
  lets (Hfin & Hantisym & Hedge_wf): Hwf.
  asserts Hneq: (c <> c').
  {
    intro Heq. subst c'. applys commit_fresh_not_indom Hfresh Hin.
  }
  destruct G as (C & P). unfolds graph_indom.
  splits.
  - simpl. unfolds finite. rew_dom.
    applys~ LibSet.finite_union.
    applys~ LibSet.finite_single.
  - introv Hab Hba.
    asserts Hsink: (forall z, ancestor (graph_commit (C, P) c c' d) c' z -> z = c').
    {
      introv Hz. applys ancestor_no_out_edge Hz.
      introv He. unfolds graph_commit, graph_edge.
      rew_set in He. destruct~ He as [Heq | HeP].
      forwards (Hin' & _): Hedge_wf HeP.
      applys commit_fresh_not_indom Hfresh Hin'.
    }
    destruct (classic (c1 = c')) as [-> | Hane].
    + symmetry. applys Hsink Hab.
    + destruct (classic (c2 = c')) as [-> | Hbne].
      * applys Hsink Hba.
      * asserts Hsink': (forall z, ancestor (C, P) c' z -> z = c').
        {
          introv Hanc.
          forwards*: ancestor_commit_fresh_eq.
        }
        forwards~ Hab': ancestor_graph_commit_inv Hab.
        forwards~ Hba': ancestor_graph_commit_inv Hba.
  - introv He. unfolds graph_commit, graph_edge.
    rew_set in He. destruct He as [Heq | Hin'].
    + inverts Heq. split.
      * applys~ indom_update_of_indom. typeclass.
      * applys indom_update_same. typeclass.
    + forwards (Ha & Hb): Hedge_wf Hin'. unfolds graph_indom.
      split; applys~ indom_update_of_indom; typeclass.
Qed.

(* Merging two parents [p1], [p2] (both already in the graph) into a fresh commit
   [h] preserves well-formedness: [h] is a sink, so the two new edges into it
   cannot create a cycle. *)
Lemma graph_merge_wf :
  forall G p1 p2 h,
    wf_graph G ->
    commit_fresh G h ->
    graph_indom G p1 ->
    graph_indom G p2 ->
    wf_graph (graph_merge G p1 p2 h).
Proof.
  introv Hwf Hfresh Hin1 Hin2.
  lets (Hfin & Hantisym & Hedge_wf): Hwf.
  asserts Hneq1: (p1 <> h). { intro Heq. subst h. applys commit_fresh_not_indom Hfresh Hin1. }
  asserts Hneq2: (p2 <> h). { intro Heq. subst h. applys commit_fresh_not_indom Hfresh Hin2. }
  destruct G as (C & P). unfolds graph_indom, graph_indom.
  splits.
  - simpl. unfolds finite. rew_dom. applys~ LibSet.finite_union.
    applys LibSet.finite_single.
  - introv Hab Hba.
    asserts Hsink: (forall z, ancestor (graph_merge (C, P) p1 p2 h) h z -> z = h).
    {
      introv Hz. applys ancestor_no_out_edge Hz.
      introv He. unfolds graph_merge, graph_edge. rew_set in He.
      destruct~ He as [Heq | [Heq | HeP]].
      forwards (Hin' & _): Hedge_wf HeP. applys commit_fresh_not_indom Hfresh Hin'.
    }
    destruct (classic (c1 = h)) as [-> | Hane].
    + symmetry. applys Hsink Hab.
    + destruct (classic (c2 = h)) as [-> | Hbne].
      * applys Hsink Hba.
      * asserts Hsink': (forall z, ancestor (C, P) h z -> z = h).
        {
          introv Hanc.
          forwards*: ancestor_commit_fresh_eq.
        }
        forwards~ Hab': ancestor_graph_merge_inv Hab.
        forwards~ Hba': ancestor_graph_merge_inv Hba.
  - introv He. unfolds graph_merge, graph_edge, graph_indom.
    rew_set in He.
    destruct He as [Heq | [Heq | HeP]].
    + inverts Heq. split.
      * applys~ indom_update_of_indom. typeclass.
      * applys indom_update_same. typeclass.
    + inverts Heq. split.
      * applys~ indom_update_of_indom. typeclass.
      * applys indom_update_same. typeclass.
    + forwards (Ha & Hb): Hedge_wf HeP.
      split; applys~ indom_update_of_indom; typeclass.
Qed.

Lemma graph_commit_indom :
  forall G c c' c'' d,
    graph_indom G c ->
    graph_indom (graph_commit G c' c'' d) c.
Proof.
  introv Hdom. unfolds graph_indom, graph_commit.
  destruct G as (C & P).
  rew_dom. rew_set. auto.
Qed.

Hint Resolve graph_commit_indom : vcm.

Lemma graph_commit_indom_same :
  forall G c c' d,
    graph_indom (graph_commit G c c' d) c'.
Proof.
  introv. unfolds graph_indom, graph_commit.
  destruct G as (C & P).
  rew_dom. rew_set. auto.
Qed.

Hint Resolve graph_commit_indom_same : vcm.

Lemma graph_commit_indom_inv :
  forall G c c' c'' d,
    graph_indom (graph_commit G c' c'' d) c ->
    graph_indom G c \/ c = c''.
Proof.
  introv Hdom. unfolds graph_indom, graph_commit.
  destruct G as (C & P).
  rew_dom. rew_set in Hdom. auto.
Qed.

Lemma graph_merge_indom :
  forall G c c' c'' m,
    graph_indom G c ->
    graph_indom (graph_merge G c' c'' m) c.
Proof.
  introv Hdom. unfolds graph_indom, graph_merge.
  destruct G as (C & P).
  rew_dom. rew_set. auto.
Qed.

Hint Resolve graph_merge_indom : vcm.

Lemma graph_merge_indom_same :
  forall G c c' m,
    graph_indom (graph_merge G c c' m) m.
Proof.
  introv. unfolds graph_indom, graph_merge.
  destruct G as (C & P).
  rew_dom. rew_set. auto.
Qed.

Hint Resolve graph_merge_indom_same : vcm.

Lemma graph_root_indom_same :
  forall c,
    graph_indom (graph_root c) c.
Proof.
  introv. unfolds graph_indom, graph_root.
  rew_dom. rew_set. auto.
Qed.

Hint Resolve graph_merge_indom_same : vcm.

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

(* Committing onto the current global head produces the new one: bundles
   [total_order_commit] (the chain stays totally ordered) with
   [graph_commit_indom_same] + [max_ancestor_commit] (the fresh commit [g']
   is indom and every graph-indom commit is now its ancestor, i.e.
   [is_global_head]). *)
Lemma is_global_head_commit :
  forall G g g' d,
    total_order G ->
    is_global_head G g ->
    commit_fresh G g' ->
    total_order (graph_commit G g g' d) /\ is_global_head (graph_commit G g g' d) g'.
Proof.
  introv Htot (Hgdom & Hmax) Hfresh. split.
  - applys total_order_commit Htot Hmax Hfresh.
  - split.
    + applys graph_commit_indom_same.
    + introv Hindom. applys max_ancestor_commit Hmax Hfresh Hindom.
Qed.

(* The global head is unique: two commits that both dominate the whole graph
   must dominate EACH OTHER, and [wf_graph]'s antisymmetry then collapses
   them. *)
Lemma is_global_head_unique :
  forall G g1 g2,
    wf_graph G ->
    is_global_head G g1 ->
    is_global_head G g2 ->
    g1 = g2.
Proof.
  introv Hwf (Hdom1 & Hmax1) (Hdom2 & Hmax2).
  destruct Hwf as (_ & Hantisym & _).
  applys Hantisym (Hmax2 g1 Hdom1) (Hmax1 g2 Hdom2).
Qed.

(* Helper for [total_order_max_commit]: within a totally ordered graph, any
   list containing at least one graph-indom commit has a *maximum* among its
   graph-indom members -- one that every graph-indom member of the list is an
   ancestor of. Induction on the list, comparing the head against the
   tail's champion (if any) via [total_order] and keeping whichever wins;
   [ancestor_trans] carries the losing side's dominion over to the winner. *)
Lemma total_order_list_max_indom :
  forall G l,
    total_order G ->
    (exists c, mem c l /\ graph_indom G c) ->
    exists m,
      graph_indom G m /\ mem m l /\
      (forall c, mem c l -> graph_indom G c -> ancestor G c m).
Proof.
  introv Htot. induction l as [| y l' IH]; introv (c & Hmemc & Hindomc).
  - false; applys mem_nil_inv Hmemc.
  - destruct (classic (y = c)) as [-> | Hyc].
    + (* the head [y] is itself graph-indom *)
      destruct (classic (exists c', mem c' l' /\ graph_indom G c')) as [Hex | Hnex].
      * forwards (m' & Hm'indom & Hm'mem & Hm'max): IH Hex.
        forwards [Hym' | Hm'y]: Htot Hindomc Hm'indom.
        -- exists m'. splits~.
           intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
           ++ exact Hym'.
           ++ applys Hm'max Hmem' Hindom.
        -- exists c. splits~.
           intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
           ++ apply ancestor_refl.
           ++ applys ancestor_trans (Hm'max _ Hmem' Hindom) Hm'y.
      * exists c. splits~.
        intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
        -- apply ancestor_refl.
        -- false; applys Hnex; exists* cc.
    + (* the witness [c] lives in the tail, whether or not [y] is graph-indom *)
      forwards [-> | Hmemc']: mem_cons_inv Hmemc; [false; applys Hyc; reflexivity |].
      forwards (m' & Hm'indom & Hm'mem & Hm'max): IH.
      { exists c. splits~. }
      destruct (classic (graph_indom G y)) as [Hyindom | Hynindom].
      * forwards [Hym' | Hm'y]: Htot Hyindom Hm'indom.
        -- exists m'. splits~.
           intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
           ++ exact Hym'.
           ++ applys Hm'max Hmem' Hindom.
        -- exists y. splits~.
           intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
           ++ apply ancestor_refl.
           ++ applys ancestor_trans (Hm'max _ Hmem' Hindom) Hm'y.
      * exists m'. splits~.
        intros cc Hmem Hindom. forwards [-> | Hmem']: mem_cons_inv Hmem.
        -- false; applys Hynindom Hindom.
        -- applys Hm'max Hmem' Hindom.
Qed.

(* A totally ordered, well-formed graph has a maximum commit: given any
   witness [c0] showing the graph is nonempty, there is a commit [m] that
   every graph-indom commit is an ancestor of. *)
Lemma total_order_max_commit :
  forall G c0,
    wf_graph G ->
    total_order G ->
    graph_indom G c0 ->
    exists m, graph_indom G m /\ forall c, graph_indom G c -> ancestor G c m.
Proof.
  introv Hwf Htot Hindom0.
  destruct Hwf as (Hfin & _ & _).
  destruct G as (C & P).
  simpl in Hfin, Hindom0.
  forwards (l & Hcov): finite_inv_list_covers Hfin.
  forwards (m & Hmindom & _ & Hmax): total_order_list_max_indom Htot.
  { exists c0. splits~. }
  exists m. splits~.
Qed.

(* Inverting an ancestry path that lands exactly on the fresh merge commit [h]:
   its only incoming edges are [(p2,h)] and [(p1,h)] ([wf_graph]/[commit_fresh]
   rule out any pre-existing edge into [h]), so any path into [h] other than the
   trivial [x = h] must pass through [p1] or [p2]. Companion to
   [ancestor_graph_merge_inv], which instead handles targets *other* than [h]. *)
Lemma ancestor_graph_merge_into_fresh_inv :
  forall G p1 p2 h x,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G h ->
    graph_indom G p1 ->
    graph_indom G p2 ->
    ancestor (graph_merge G p1 p2 h) x h ->
    x = h \/ ancestor G x p1 \/ ancestor G x p2.
Proof.
  introv Hedge Hfresh Hp1dom Hp2dom Hanc.
  inverts Hanc as Hsub Hstep.
  - left. reflexivity.
  - right. destruct G as (C & P). unfold graph_merge in Hstep. rew_set in Hstep.
    asserts Hsink: (forall z, ancestor (C, P) h z -> z = h).
    { introv Hz. applys commit_fresh_sink Hedge Hfresh Hz. }
    asserts Hp1neq: (p1 <> h). { intro Heqp. subst p1. applys commit_fresh_not_indom Hfresh Hp1dom. }
    asserts Hp2neq: (p2 <> h). { intro Heqp. subst p2. applys commit_fresh_not_indom Hfresh Hp2dom. }
    destruct Hstep as [Heq | [Heq | HstepP]].
    + inverts Heq. right. applys ancestor_graph_merge_inv Hsink Hp2neq Hsub.
    + inverts Heq. left. applys ancestor_graph_merge_inv Hsink Hp1neq Hsub.
    + exfalso. forwards (_ & Hhindom): Hedge HstepP. applys commit_fresh_not_indom Hfresh Hhindom.
Qed.

(* Merging a fresh commit [h] between [p1] (the current maximal-writer location
   of [i]) and [p2] cannot introduce or hide a more recent [i]-write, PROVIDED
   every [i]-writer in [G] is already an ancestor of [p1] -- so [is_latest_value]
   transfers from [p1] onto [h] itself (not just onto old, off-to-the-side
   commits, as [is_latest_value_graph_merge_mono] does). *)
Lemma is_latest_value_graph_merge_fresh :
  forall G p1 p2 h i v,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G h ->
    graph_indom G p1 ->
    graph_indom G p2 ->
    is_latest_value G p1 i v ->
    (forall c v', graph_writes G c i v' -> ancestor G c p1) ->
    is_latest_value (graph_merge G p1 p2 h) h i v.
Proof.
  introv Hedge Hfresh Hp1dom Hp2dom Hval Hdom.
  destruct Hval as (cw & Hgw & Hancw1 & Hmax).
  asserts Hcwdom: (graph_indom G cw). { applys graph_writes_to_indom Hgw. }
  asserts Hsink: (forall z, ancestor G h z -> z = h).
  { introv Hz. applys commit_fresh_sink Hedge Hfresh Hz. }
  asserts Hcwneq: (cw <> h). { intro Heq. subst cw. applys commit_fresh_not_indom Hfresh Hcwdom. }
  exists cw. splits.
  - applys~ graph_writes_graph_merge.
  - apply ancestor_trans with (c' := p1).
    + applys~ ancestor_graph_merge.
    + applys ancestor_graph_merge_edge_r.
  - introv Hw3 Hanc1 Hanc2.
    destruct (classic (c'' = h)) as [-> | Hc3neq].
    { false; applys graph_writes_graph_merge_same_false Hw3. }
    forwards Hw3G: graph_writes_graph_merge_inv Hc3neq Hw3.
    forwards Hanc1G: ancestor_graph_merge_inv Hsink Hc3neq Hanc1.
    forwards Hdisj: ancestor_graph_merge_into_fresh_inv Hedge Hfresh Hp1dom Hp2dom Hanc2.
    destruct Hdisj as [Heq | [Hancp1 | Hancp2]].
    + false; applys Hc3neq Heq.
    + applys Hmax Hw3G Hanc1G Hancp1.
    + forwards Hancp1': Hdom Hw3G.
      applys Hmax Hw3G Hanc1G Hancp1'.
Qed.

(* Forward preservation of [is_latest_value] at an OLD commit [h] across a
   single [graph_commit] onto a fresh commit [cf], PROVIDED the freshly
   committed diff [d] does not write [i] (so [cf] cannot become a competing
   [i]-writer). Since [cf] is fresh, it is a sink in [G] ([commit_fresh_sink]):
   any new-graph ancestry into (or out of, past) an old commit [<> cf] already
   existed in [G], so both the witness and maximality transfer unchanged. *)
Lemma is_latest_value_graph_commit_mono :
  forall G c cf d h i v,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    h <> cf ->
    (forall v', ~ binds d i v') ->
    is_latest_value G h i v ->
    is_latest_value (graph_commit G c cf d) h i v.
Proof.
  introv Hedge Hfresh Hneq Hnw (cc & Hw & Hanc & Hmax).
  asserts Hccneq: (cc <> cf).
  { intro Heq. subst cc. forwards Hdom: graph_writes_to_indom Hw.
    applys commit_fresh_not_indom Hfresh Hdom. }
  asserts Hsink: (forall z, ancestor G cf z -> z = cf).
  { applys commit_fresh_sink Hedge Hfresh. }
  exists cc. splits.
  { applys~ graph_writes_graph_commit. }
  { applys~ ancestor_graph_commit. }
  { intros cc2 v2 Hw2 Hanc1 Hanc2.
    asserts Hcc2neq: (cc2 <> cf).
    { intro Heq. subst cc2.
      forwards Hbd: graph_writes_graph_commit_same Hw2.
      applys Hnw Hbd. }
    forwards Hw2_G: graph_writes_graph_commit_inv Hcc2neq Hw2.
    forwards Hanc1_G: ancestor_graph_commit_inv Hsink Hcc2neq Hanc1.
    forwards Hanc2_G: ancestor_graph_commit_inv Hsink Hneq Hanc2.
    applys Hmax Hw2_G Hanc1_G Hanc2_G. }
Qed.

(* The [graph_merge] counterpart: a merge commit carries no data at all, so it
   is unconditionally not an [i]-writer ([graph_writes_graph_merge_same_false]) --
   no side-condition on a diff is needed. *)
Lemma is_latest_value_graph_merge_mono :
  forall G p1 p2 cf h i v,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    h <> cf ->
    is_latest_value G h i v ->
    is_latest_value (graph_merge G p1 p2 cf) h i v.
Proof.
  introv Hedge Hfresh Hneq (cc & Hw & Hanc & Hmax).
  asserts Hccneq: (cc <> cf).
  { intro Heq. subst cc. forwards Hdom: graph_writes_to_indom Hw.
    applys commit_fresh_not_indom Hfresh Hdom. }
  asserts Hsink: (forall z, ancestor G cf z -> z = cf).
  { applys commit_fresh_sink Hedge Hfresh. }
  exists cc. splits.
  { applys~ graph_writes_graph_merge. }
  { applys~ ancestor_graph_merge. }
  { intros cc2 v2 Hw2 Hanc1 Hanc2.
    asserts Hcc2neq: (cc2 <> cf).
    { intro Heq. subst cc2.
      forwards: graph_writes_graph_merge_same_false Hw2. false. }
    forwards Hw2_G: graph_writes_graph_merge_inv Hcc2neq Hw2.
    forwards Hanc1_G: ancestor_graph_merge_inv Hsink Hcc2neq Hanc1.
    forwards Hanc2_G: ancestor_graph_merge_inv Hsink Hneq Hanc2.
    applys Hmax Hw2_G Hanc1_G Hanc2_G. }
Qed.

(* A freshly committed commit [cf], carrying diff [d] with [binds d i v], is
   immediately the latest [i]-value: it is a sink in the NEW graph (all of
   [graph_commit]'s new edges point INTO [cf] -- the only one, [(c, cf)], has
   [cf] as its TARGET, not its source -- and [cf]'s old edges are none, since
   it was fresh), so no candidate writer can be both its ancestor and its
   proper descendant unless it equals [cf] itself. *)
Lemma is_latest_value_graph_commit_fresh_writer :
  forall G c cf d i v,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    graph_indom G c ->
    binds d i v ->
    is_latest_value (graph_commit G c cf d) cf i v.
Proof.
  introv Hedge Hfresh Hcdom Hbd.
  exists cf. splits.
  { exists d. split.
    { unfold graph_binds, graph_commit. destruct G as (C & P). apply binds_update_same. }
    { exact Hbd. } }
  { apply ancestor_refl. }
  { intros cc2 v2 Hw2 Hanc1 Hanc2.
    forwards Heqcc: ancestor_no_out_edge Hanc1.
    { intros y Hey. destruct G as (C & P). unfolds graph_edge, graph_commit.
      rew_set in Hey.
      destruct Hey as [Heq | HeP].
      { inverts Heq. applys commit_fresh_not_indom Hfresh Hcdom. }
      { forwards (Ha & _): Hedge HeP. applys commit_fresh_not_indom Hfresh Ha. } }
    exact Heqcc. }
Qed.

(* The freshly committed commit is a sink in the new graph. *)
Lemma graph_commit_new_sink :
  forall G c cf d,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G cf ->
    graph_indom G c ->
    forall z, ancestor (graph_commit G c cf d) cf z -> z = cf.
Proof.
  introv Hedge Hfresh Hcdom Hanc.
  applys ancestor_no_out_edge Hanc.
  intros y Hey. destruct G as (C & P). unfolds graph_edge, graph_commit.
  rew_set in Hey.
  destruct Hey as [Heq | HeP].
  { inverts Heq. applys commit_fresh_not_indom Hfresh Hcdom. }
  { forwards (Ha & _): Hedge HeP. applys commit_fresh_not_indom Hfresh Ha. }
Qed.

(* Merging a fresh commit [h] between any [p1] and a SINK writer [c] of [i] makes
   [c] the latest [i]-value at [h]: nothing can sit strictly between [c] and [h]
   (an [i]-writer there would be a proper descendant of the sink [c]). [p1] may
   hold any number of incomparable earlier [i]-writers; this is the push-only
   volatile write, where racing writes are not ordered. *)
Lemma is_latest_value_graph_merge_fresh_writer :
  forall G p1 c h i v,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G h ->
    graph_indom G c ->
    graph_writes G c i v ->
    (forall z, ancestor G c z -> z = c) ->
    is_latest_value (graph_merge G p1 c h) h i v.
Proof.
  introv Hedge Hfresh Hcdom Hw Hsinkc.
  exists c. splits.
  { applys graph_writes_graph_merge; [ | exact Hw ].
    intro Heq. subst c. applys commit_fresh_not_indom Hfresh Hcdom. }
  { apply ancestor_graph_merge_edge_l. }
  { intros y v' Hw' Hanc1 Hanc2.
    asserts Hsinkh: (forall z, ancestor G h z -> z = h).
    { applys commit_fresh_sink Hedge Hfresh. }
    destruct (classic (y = h)) as [-> | Hyh].
    { false. applys graph_writes_graph_merge_same_false Hw'. }
    forwards Hanc1': ancestor_graph_merge_inv Hsinkh Hyh Hanc1.
    applys Hsinkc Hanc1'. }
Qed.

(* A conflict-free graph has conflict-free views: every commit reachable from
   [c] lies in the graph, so [view_conflict_free] is just [conflict_free_graph]
   restricted to the ancestors of [c]. *)
Lemma conflict_free_graph_view :
  forall G c,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    graph_indom G c ->
    conflict_free_graph G ->
    view_conflict_free G c.
Proof.
  introv Hedge Hc Hcf. introv Ha Hb.
  asserts Hina: (graph_indom G a).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Ha; [ exact Hin | subst a; exact Hc ]. }
  asserts Hinb: (graph_indom G b).
  { forwards [Hin | Heq]: ancestor_src_indom Hedge Hb; [ exact Hin | subst b; exact Hc ]. }
  applys Hcf Hina Hinb.
Qed.

(* ---------------------------------------------------------------------- *)
(* [graph_merge_with]: a merge whose fresh commit carries a diff.          *)
(* It has exactly the edges (hence the ancestry) of [graph_merge]; only    *)
(* the data of the fresh commit differs.                                   *)
(* ---------------------------------------------------------------------- *)

Lemma ancestor_data_irrel :
  forall (C1 C2 : commit_data) P a b,
    ancestor (C1, P) a b -> ancestor (C2, P) a b.
Proof.
  introv H. induction H.
  - apply AncestorRefl.
  - applys AncestorTrans IHancestor. assumption.
Qed.

Lemma ancestor_graph_merge_with_iff :
  forall G c1 c2 c d a b,
    ancestor (graph_merge_with G c1 c2 c d) a b <->
    ancestor (graph_merge G c1 c2 c) a b.
Proof.
  intros. destruct G as (C & P). unfold graph_merge_with, graph_merge.
  split; apply ancestor_data_irrel.
Qed.

Lemma ancestor_graph_merge_with :
  forall G p1 p2 h d x y,
    ancestor G x y ->
    ancestor (graph_merge_with G p1 p2 h d) x y.
Proof.
  introv Hanc. apply ancestor_graph_merge_with_iff. applys ancestor_graph_merge Hanc.
Qed.

Lemma ancestor_graph_merge_with_inv :
  forall G p1 p2 h d x y,
    (forall z, ancestor G h z -> z = h) ->
    y <> h ->
    ancestor (graph_merge_with G p1 p2 h d) x y ->
    ancestor G x y.
Proof.
  introv Hsink Hneq Hanc. apply ancestor_graph_merge_with_iff in Hanc.
  applys ancestor_graph_merge_inv Hsink Hneq Hanc.
Qed.

Lemma ancestor_graph_merge_with_edge_l :
  forall G c1 c2 c' d, ancestor (graph_merge_with G c1 c2 c' d) c2 c'.
Proof.
  intros. apply ancestor_graph_merge_with_iff. apply ancestor_graph_merge_edge_l.
Qed.

Lemma ancestor_graph_merge_with_edge_r :
  forall G c1 c2 c' d, ancestor (graph_merge_with G c1 c2 c' d) c1 c'.
Proof.
  intros. apply ancestor_graph_merge_with_iff. apply ancestor_graph_merge_edge_r.
Qed.

Lemma ancestor_graph_merge_with_into_fresh_inv :
  forall G p1 p2 h d x,
    (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b) ->
    commit_fresh G h ->
    graph_indom G p1 ->
    graph_indom G p2 ->
    ancestor (graph_merge_with G p1 p2 h d) x h ->
    x = h \/ ancestor G x p1 \/ ancestor G x p2.
Proof.
  introv Hedge Hfresh Hp1 Hp2 Hanc. apply ancestor_graph_merge_with_iff in Hanc.
  applys ancestor_graph_merge_into_fresh_inv Hedge Hfresh Hp1 Hp2 Hanc.
Qed.

Lemma graph_merge_with_indom :
  forall G c c' c'' m d,
    graph_indom G c ->
    graph_indom (graph_merge_with G c' c'' m d) c.
Proof.
  introv Hdom. unfolds graph_indom, graph_merge_with.
  destruct G as (C & P). rew_dom. rew_set. auto.
Qed.

Lemma graph_merge_with_indom_same :
  forall G c c' m d,
    graph_indom (graph_merge_with G c c' m d) m.
Proof.
  introv. unfolds graph_indom, graph_merge_with.
  destruct G as (C & P). rew_dom. rew_set. auto.
Qed.

Lemma graph_merge_with_wf :
  forall G p1 p2 h d,
    wf_graph G ->
    commit_fresh G h ->
    graph_indom G p1 ->
    graph_indom G p2 ->
    wf_graph (graph_merge_with G p1 p2 h d).
Proof.
  introv Hwf Hfresh Hin1 Hin2.
  forwards Hwfm: graph_merge_wf Hwf Hfresh Hin1 Hin2.
  destruct Hwfm as (_ & Hanti & _).
  lets (Hfin & _ & Hedge_wf): Hwf.
  destruct G as (C & P). unfolds graph_indom, graph_merge, graph_merge_with.
  splits.
  - simpl. unfolds finite. rew_dom. applys~ LibSet.finite_union.
    applys LibSet.finite_single.
  - introv Hab Hba. applys Hanti.
    + applys ancestor_data_irrel Hab.
    + applys ancestor_data_irrel Hba.
  - introv He. unfolds graph_edge, graph_indom.
    rew_set in He. destruct He as [Heq | [Heq | HeP]].
    + inverts Heq. split.
      * applys~ indom_update_of_indom. typeclass.
      * applys indom_update_same. typeclass.
    + inverts Heq. split.
      * applys~ indom_update_of_indom. typeclass.
      * applys indom_update_same. typeclass.
    + forwards (Ha & Hb): Hedge_wf HeP.
      split; applys~ indom_update_of_indom; typeclass.
Qed.

Lemma graph_writes_graph_merge_with :
  forall G p1 p2 h d x i v,
    x <> h ->
    graph_writes G x i v ->
    graph_writes (graph_merge_with G p1 p2 h d) x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_merge_with.
  exists dd. split~. applys~ binds_update_neq.
Qed.

Lemma graph_writes_graph_merge_with_inv :
  forall G p1 p2 h d x i v,
    x <> h ->
    graph_writes (graph_merge_with G p1 p2 h d) x i v ->
    graph_writes G x i v.
Proof.
  introv Hneq (dd & Hb & Hbd). destruct G as (C & P).
  unfolds graph_binds, graph_writes, graph_merge_with.
  exists dd. split~. applys~ binds_update_neq_inv Hb.
Qed.

(* The merge commit carries exactly the diff it was given. *)
Lemma graph_writes_graph_merge_with_same :
  forall G p1 p2 h d i v,
    graph_writes (graph_merge_with G p1 p2 h d) h i v -> binds d i v.
Proof.
  introv (dd & Hgb & Hbd). destruct G as (C & P).
  unfolds graph_merge_with, graph_binds.
  asserts Hdd: (dd = d). { applys binds_inj Hgb; (apply binds_update_same || typeclass). }
  subst dd. exact Hbd.
Qed.

Lemma graph_writes_graph_merge_with_new :
  forall G p1 p2 h d i v,
    binds d i v -> graph_writes (graph_merge_with G p1 p2 h d) h i v.
Proof.
  introv Hbd. exists d. split; [ | exact Hbd ].
  destruct G as (C & P). unfold graph_merge_with, graph_binds. apply binds_update_same.
Qed.
