From Vcm Require Import Common.

Definition commit := nat.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition staging_area := map loc val.

Definition empty_staging_area : staging_area := empty.

Instance inhab_staging_area : Inhab staging_area.
  constructor. exists empty_staging_area. tauto.
Qed.

Definition thread := (thread_state * thread_exp * staging_area * commit)%type.

Instance inhab_thread : Inhab thread.
  forwards* Hexp: inhab_exp.
  destruct Hexp as [[e _]].
  constructor. exists* (state_new, te_exp e, (empty : staging_area), 0).
Qed.

Definition threads := map tid thread.

(* TODO: unify staging_areas to something more general *)
Definition commit_data := map commit staging_area.

Definition commit_rels := set (commit * commit).

Instance commit_rels_in_inst : BagIn (commit * commit) commit_rels.
  apply LibSet.in_inst.
Defined.

Definition graph : Type := commit_data * commit_rels.

Definition empty_graph : graph := (empty, empty).

Definition graph_indom (G : graph) (h : commit) :=
  match G with
  | (C, _) => h \indom C
  end.

Definition graph_binds (G : graph) (h : commit) (d : staging_area) :=
  match G with
  | (C, _) => binds C h d
  end.

Definition graph_edge (G : graph) (a b : commit) : Prop :=
  match G with
  | (_, P) => (a, b) \in P
  end.

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

Definition commit_fresh (G : graph) (h : commit) : Prop :=
  match G with
  | (C, _) => h \notindom C
  end.

Definition get_staging_area (G : graph) (h : commit) : staging_area :=
  match G with
  | (C, _) => C[h]
  end.

(* The paper defines it as a closure of a direct relation, but
only uses the closure so we define it as such *)
Inductive ancestor (G : graph) : commit -> commit -> Prop :=
| AncestorRefl : forall h,
    (* TODO: Should we require h to be in P? *)
    ancestor G h h
| AncestorTrans : forall h1 h2 h3,
    ancestor G h1 h2 ->
    match G with
    | (_, P) => (h2, h3) \in P
    end ->
    ancestor G h1 h3
.

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

Definition wf_graph (G : graph) :=
  (let '(C, _) := G in LibMap.finite C) /\
  (forall h1 h2,
    ancestor G h1 h2 ->
    ancestor G h2 h1 ->
    h1 = h2) /\
  (* Every commit appearing in the ancestry relation has data (possibly empty).
     This ties the ancestry component [P] to the data component [C]: a commit
     that is fresh in the data is genuinely new and cannot already be an edge
     endpoint. *)
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b).

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

Definition change_set (G : graph) (h1 h2 : commit) : set loc :=
  fun i =>
  match G with
  | (C, _) =>
      exists h,
        i \indom C[h] /\
        ancestor G h h2 /\ ~ancestor G h h1
  end.

Lemma change_set_eq_empty :
  forall G h,
    change_set G h h = empty.
Proof.
  intros. apply is_empty_prove.
  introv Hmem. unfolds change_set.
  destruct G as (C & P).
  destruct* Hmem as (h' & Hdom & Hanc & Hnanc).
Qed.

Definition conflict_free_merge (d : staging_area) (h1 h2 : commit) (G : graph) :=
  (dom d \u change_set G h2 h1) \# (change_set G h1 h2).

Definition conflict_free_graph (G : graph) :=
  forall h1 h2,
    graph_indom G h1 ->
    graph_indom G h2 ->
    conflict_free_merge empty h1 h2 G.

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

Definition graph_commit (G : graph) (h1 h2 : commit) (d : staging_area) :=
  match G with
  | (C, P) => (C[h2 := d], \{(h1, h2)} \u P)
  end
.

Definition graph_merge (G : graph) (h1 h2 h : commit) :=
  match G with
  | (C, P) => (C[h := empty], \{(h2, h)} \u \{(h1, h)} \u P)
  end
.


Definition graph_writes (G : graph) (c : commit) (i : loc) (v : val) : Prop :=
  exists d, graph_binds G c d /\ binds d i v.

Lemma graph_writes_to_indom :
  forall G c i v,
    graph_writes G c i v ->
    graph_indom G c.
Proof.
  introv (d & Hbinds & _). eauto with vcm.
Qed.

Hint Resolve graph_writes_to_indom : vcm.

(* The latest value of [i] visible at commit [h] is the value written by some
   commit [c] that is an ancestor of [h] and is *maximal* among the i-writing
   ancestors of [h] (no other i-writer sits strictly between [c] and [h]).
   The maximality clause is what makes this single-valued; dropping it (as the
   previous inductive formulation did) makes the relation multivalued at
   conflict-free "inherit vs. overwrite" merges. *)
Definition is_latest_value (G : graph) (h : commit) (i : loc) (v : val) : Prop :=
  exists c,
    graph_writes G c i v /\
    ancestor G c h /\
    (forall c' v',
       graph_writes G c' i v' ->
       ancestor G c c' ->
       ancestor G c' h ->
       c' = c).

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

Definition locks := map lid (lock_state * commit).

Instance inhab_lock : Inhab (lock_state * commit).
  constructor. exists* (ls_free, 0).
Qed.

Definition cfg : Type := threads * graph * locks.

Definition do_commit (t : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(_, e, d, h) := T[t] in
  (T[t := (state_running, e, empty, h_new)],
   graph_commit G h h_new d)
.

Definition push_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(T', G') := do_commit t h_new T G in
  let '(ts, e, d, _) := T'[t'] in
  (T'[t' := (ts, e, d, h_new)], G').

Definition push_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph * locks :=
  let '(T', G') := do_commit t h_new T G in
  let '(ls, _) := L[l] in
  (T', G', L[l := (ls, h_new)]).

Definition do_merge (t : tid) (h h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(ts, e, d, h_t) := T[t] in
  (T[t := (ts, e, d, h_new)], graph_merge G h h_t h_new).

Definition pull_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
    let '(_, _, _, h') := T[t'] in
    do_merge t h' h_new T G.

Definition pull_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph :=
  let '(_, h) := L[l] in
  do_merge t h h_new T G.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G L t e d h,
    binds T t (state_new, e, d, h) ->
    step (T, G, L) (T[t := (state_running, e, d, h)], G, L)
| StepEnd : forall T T' G G' L t r d h h',
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh G h' ->
    do_commit t h' T G = (T', G') ->
    step (T, G, L) (T'[t := (state_terminated, te_ret r, empty, h')], G', L)
| StepReadLocal : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    binds d i v ->
    step (T, G, L) (T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L)
| StepReadGlobal : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    i \notindom d ->
    is_latest_value G h i v ->
    step (T, G, L) (T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L)
| StepWrite : forall T G L t e d h K i v,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write i v) ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), d[i := v], h)], G, L)
 | StepSpawn : forall T T' G G' L t (t' : tid) e d h h' K e',
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    commit_fresh G h' ->
    push_thread t t' h' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)]) G = (T', G') ->
    step (T, G, L) (T', G', L)
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_thread t t' h'' T G = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K r), d, h'')], G', L)
| StepLock : forall T T' G G' L t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h'' ->
    pull_lock t l h'' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K void), d, h'')], G', L[l := (ls_held t, h')])
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h') ->
    commit_fresh G h'' ->
    push_lock t l h'' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h'') ->
    step (T, G, L) (T'[t := (state_running, te_exp (K void), empty, h'')], G', L'[l := (ls_free, h'')])
.
