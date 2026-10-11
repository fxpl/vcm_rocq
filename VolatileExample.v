From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.

(* ------------------------------------------------------------------------ *)
(* The volatile example of volatile.tex, on the Branching model of          *)
(* [non-conflicting-non-pulling-volatile-writes]: a volatile write pushes   *)
(* without pulling and records its value in the volatile's stored commit;   *)
(* volatiles are ignored by conflict checking.                              *)
(*                                                                          *)
(*   volatile x, non-volatile y                                             *)
(*                                                                          *)
(*     t1:  y = 1;        t2:  x = 2;                                       *)
(*          x = 1;             print(y);                                    *)
(*                             print(x);                                    *)
(*                                                                          *)
(* scheduled so that t1 runs to completion before t2 runs ([print] is       *)
(* emulated by a read). There is no concrete program syntax, so the threads *)
(* are axiomatised: each thread is a chain of expressions, each of which    *)
(* offers exactly one effect, and whose continuation leads to the next one. *)
(* The assumptions are section hypotheses, not global axioms.               *)
(* ------------------------------------------------------------------------ *)

(* Reflexive-transitive closure of the Branching [step]. *)
Inductive steps : cfg -> cfg -> Prop :=
| steps_refl : forall c, steps c c
| steps_step : forall c1 c2 c3, step c1 c2 -> steps c2 c3 -> steps c1 c3.

(* [e] offers exactly one reduction: effect [a] with continuation [K]. *)
Definition only_step (e : exp) (K : cont) (a : eff) : Prop :=
  step_ul e K a /\ forall K' a', step_ul e K' a' -> K' = K /\ a' = a.

(* Nothing is in the change set between a commit and itself, so a merge of a
   commit with itself is always conflict-free. *)
Lemma conflict_free_merge_self :
  forall d c G, conflict_free_merge d c c G.
Proof.
  introv. unfold conflict_free_merge. rew_set. intros j Hj1 Hj2.
  destruct G as (C & P). unfold change_set in Hj2.
  destruct Hj2 as (_ & c0 & _ & Hanc & Hnanc). applys Hnanc Hanc.
Qed.

Lemma vc_read_empty : forall x, vc_read empty x = root_commit.
Proof.
  intros. unfold vc_read. apply read_default_notindom.
  intro Hin. applys indom_empty_inv Hin.
Qed.

Section Example.

(* [v0] is the initial value of both variables *)
Variables (x y : var) (v0 v1 v2 : val).
Hypothesis Hxvol : x \in Volatiles.
Hypothesis Hynvol : y \notin Volatiles.

Variables (t1 t2 : tid).
Hypothesis Ht12 : t1 <> t2.

(* t1:  y = 1; x = 1 *)
Variables (p1 p2 : exp) (k1 k2 : cont) (r1 : ret).
Hypothesis P1 : only_step p1 k1 (eff_write y v1).
Hypothesis P1k : k1 void = te_exp p2.
Hypothesis P2 : only_step p2 k2 (eff_write x v1).
Hypothesis P2k : k2 void = te_ret r1.

(* t2:  x = 2; print(y); print(x) *)
(* The value read by each print is remembered by the rest of the program, and
   the thread's final result [res a b] records the two printed values. *)
Variables (q1 q2 : exp) (q3 : val -> exp) (j1 j2 : cont) (j3 : val -> cont)
          (res : val -> val -> ret).
Hypothesis Q1 : only_step q1 j1 (eff_write x v2).
Hypothesis Q1k : j1 void = te_exp q2.
Hypothesis Q2 : only_step q2 j2 (eff_read y).
Hypothesis Q2k : forall a, j2 (ret_val a) = te_exp (q3 a).
Hypothesis Q3 : forall a, only_step (q3 a) (j3 a) (eff_read x).
Hypothesis Q3k : forall a b, j3 a (ret_val b) = te_ret (res a b).

(* Both variables are initialised to [v0] at the root commit; both threads
   start there, with empty staging areas. *)
Definition G_init : graph :=
  ((empty : commit_data)[root_commit := ((empty : diff)[y := v0][x := v0])],
   (empty : commit_rels)).

Definition init_cfg : cfg :=
  (empty[t1 := (state_new, te_exp p1, (empty : diff), root_commit)]
        [t2 := (state_new, te_exp q1, (empty : diff), root_commit)],
   G_init, (empty : locks), (empty : volatiles)).

Hint Resolve Ht12 : core.
Lemma Ht21 : t2 <> t1. Proof. auto. Qed.
Hint Resolve Ht21 : core.

(* [c] is not in the domain of the commit data of a small concrete graph *)
Ltac solve_fresh :=
  unfold commit_fresh, graph_merge_with, graph_merge, graph_commit, G_init; cbn; rew_dom;
  let H := fresh "Hin" in intro H; rew_set in H;
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
  first [ (eapply indom_empty_inv; eassumption) | discriminate ].

Ltac solve_binds :=
  repeat first [ apply binds_update_same | apply binds_update_neq; [ solve [auto] | ] ].

(* The commit graph and the stored commit of [x] once t1 has finished: t1's
   volatile write pushes commit 1 (holding [y = 1] and [x = 1]) on top of the
   root and leaves t1 there; [x]'s stored commit becomes the merge 2 of the
   root and 1, which carries the write [x = 1]; t1 then ends with commit 3. *)
Definition G_end : graph :=
  graph_commit
    (graph_merge_with
       (graph_commit G_init 0 1 ((empty : diff)[y := v1][x := v1]))
       root_commit 1 2 ((empty : diff)[x := v1]))
    1 3 (empty : diff).

Definition V_end : volatiles := empty[x := 2].

(* t1 runs to completion (starting, writing [y], volatile-writing [x],
   ending), and then t2 starts. *)
Lemma t1_completes :
  exists T G,
    steps init_cfg (T, G, empty, V_end) /\
    G = G_end /\
    binds T t1 (state_terminated, te_ret r1, empty, 3) /\
    binds T t2 (state_running, te_exp q1, empty, root_commit) /\
    (forall t, t \indom T -> t = t1 \/ t = t2).
Proof.
  eexists _, _. splits.
  - (* t1 starts *)
    eapply steps_step.
    { eapply StepStart with (t := t1). unfold init_cfg. solve_binds. }
    (* y = 1: a plain write *)
    eapply steps_step.
    { eapply StepWrite with (t := t1) (x := y) (v := v1); [ solve_binds | apply (proj1 P1) | assumption ]. }
    (* x = 1: a volatile write, which pushes without pulling *)
    eapply steps_step.
    { eapply StepWriteVolatile with (t := t1) (x := x) (v := v1) (h' := 1) (h'' := 2).
      - rewrite P1k. solve_binds.
      - apply (proj1 P2).
      - assumption.
      - solve_fresh.
      - solve_fresh.
      - unfold push_volatile, do_commit. rewrite read_update_same. reflexivity. }
    (* t1 ends *)
    eapply steps_step.
    { eapply StepEnd with (t := t1) (h' := 3).
      - rewrite P2k. solve_binds.
      - solve_fresh.
      - unfold do_commit. rewrite read_update_same. reflexivity. }
    (* t2 starts *)
    eapply steps_step.
    { eapply StepStart with (t := t2). solve_binds. }
    apply steps_refl.
  - unfold G_end. rewrite vc_read_empty. reflexivity.
  - solve_binds.
  - solve_binds.
  - intros t Hin. rew_dom. rew_set in Hin.
    repeat (match goal with H : _ \/ _ |- _ => destruct H end);
      first [ (exfalso; eapply indom_empty_inv; eassumption)
            | (left; assumption) | (right; assumption) ].
Qed.

(* ---- Facts about the commit graphs along t2's run ----------------------- *)

Lemma x_neq_y : x <> y.
Proof. intro H. subst. applys Hynvol Hxvol. Qed.

Lemma vc_read_V_end : vc_read V_end x = 2.
Proof. unfold V_end, vc_read. apply read_default_update_same. Qed.

(* t2's volatile write pushes commit 4 (holding [x = 2]) on top of the root,
   without having seen any of t1's writes, and t2 stays at commit 4; [x]'s
   stored commit becomes the merge 5 of the previous stored commit (2) and 4,
   which carries the write [x = 2]. *)
Definition G_b : graph :=
  graph_merge_with
    (graph_commit G_end 0 4 ((empty : diff)[x := v2]))
    (vc_read V_end x) 4 5 ((empty : diff)[x := v2]).

Definition V_b : volatiles := V_end[x := 5].

Lemma vc_read_V_b : vc_read V_b x = 5.
Proof. unfold V_b, vc_read. apply read_default_update_same. Qed.

Ltac solve_fresh2 := unfold G_end, G_b; solve_fresh.

(* Every edge goes from a smaller to a larger commit id, so ancestors are
   smaller. *)
Lemma anc_le :
  forall G,
    (forall a b : nat, graph_edge G a b -> a < b) ->
    forall a b : nat, ancestor G a b -> a <= b.
Proof.
  introv Hedge Hanc. induction Hanc as [c | c1 c2 c3 Hanc IH Hp].
  - nat_math.
  - asserts He: (graph_edge G c2 c3). { destruct G. exact Hp. }
    forwards: Hedge He. nat_math.
Qed.

Ltac unfold_G_b :=
  unfold G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit;
  rewrite vc_read_V_end.

Ltac edges_incr :=
  intros ? ? Hedge; cbn in Hedge; rew_set in Hedge;
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
  first [ contradiction
        | (match goal with H : (_, _) = (_, _) |- _ =>
             inversion H; subst; try unfold root_commit; nat_math end) ].

Lemma edges_G_b : forall a b : nat, graph_edge G_b a b -> a < b.
Proof. unfold_G_b. edges_incr. Qed.

(* the only edge into commit 4 comes from the root *)
Lemma edge_into_4 : forall a : nat, graph_edge G_b a 4 -> a = 0.
Proof.
  intros a Hedge. revert Hedge. unfold_G_b.
  intro Hedge. cbn in Hedge. rew_set in Hedge.
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
    first [ contradiction
          | (match goal with H : (_, _) = (_, _) |- _ =>
               inversion H; subst; first [ reflexivity | discriminate ] end) ].
Qed.

(* t1's push (commit 1) is not below t2's push (commit 4) *)
Lemma not_anc_1_4 : ~ ancestor G_b 1 4.
Proof.
  intro Hanc. inversion Hanc as [ | c1 c2 c3 Hanc' Hedge ]; subst.
  asserts He: (graph_edge G_b c2 4). { exact Hedge. }
  forwards Hc2: edge_into_4 He. subst c2.
  forwards Hle: anc_le edges_G_b Hanc'. nat_math.
Qed.

Ltac peel H :=
  let H' := fresh "Hp" in
  forwards H': binds_update_inv H; clear H; case_if in H'.

(* the writers in [G_b]: the initialisation (commit 0), t1's push (commit 1),
   and the merge commits 2 and 5 and t2's push 4, which only write [x] *)
Lemma writers_G_b :
  forall c z w,
    graph_writes G_b c z w ->
    (c = 0 /\ ((z = y /\ w = v0) \/ (z = x /\ w = v0))) \/
    (c = 1 /\ ((z = y /\ w = v1) \/ (z = x /\ w = v1))) \/
    ((c = 2 \/ c = 4 \/ c = 5) /\ z = x).
Proof.
  introv (d & Hb & Hbd).
  clear Q1 Q1k Q2 Q2k Q3 Q3k P1 P1k P2 P2k.
  unfold graph_binds, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit in Hb.
  cbn in Hb.
  repeat (match goal with H : binds (_[_:=_]) _ _ |- _ => peel H end).
  all: subst.
  all: repeat (match goal with H : binds (_[_:=_]) _ _ |- _ => peel H end).
  all: try (exfalso; match goal with H : binds _ _ _ |- _ =>
              first [ (applys binds_empty_false H; typeclass) | (applys binds_empty_false H) ] end).
  all: subst.
  all: first
    [ (left; split; [ reflexivity | first [ (left; split; reflexivity) | (right; split; reflexivity) ] ])
    | (right; left; split; [ reflexivity | first [ (left; split; reflexivity) | (right; split; reflexivity) ] ])
    | (right; right; split; [ first [ (left; reflexivity) | (right; left; reflexivity) | (right; right; reflexivity) ] | reflexivity ]) ].
Qed.

(* print(y) after t2's volatile write: t2 is at commit 4, which has only seen
   the initialisation of [y], not t1's write. *)
Lemma t2_reads_y : is_latest_value G_b 4 y v0.
Proof.
  exists 0. splits.
  - exists ((empty : diff)[y := v0][x := v0]). split.
    + unfold graph_binds, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit.
      cbn. solve_binds.
    + apply binds_update_neq; [ exact (fun H => x_neq_y (eq_sym H)) | apply binds_update_same ].
  - eapply AncestorTrans; [ apply AncestorRefl | ].
    unfold_G_b. cbn. rew_set. repeat first [ left; reflexivity | right ].
  - introv Hw Ha1 Ha2.
    forwards [(Hc & _) | [(Hc & _) | (_ & Hz)]]: writers_G_b Hw.
    + exact Hc.
    + exfalso. subst c''. applys not_anc_1_4 Ha2.
    + exfalso. applys x_neq_y. symmetry. exact Hz.
Qed.

(* ---- No conflicts: [G_b] is conflict free ------------------------------- *)

Ltac solve_in := first [ reflexivity | (left; solve_in) | (right; solve_in) ].

Lemma edges_indom_G_b :
  forall a b, graph_edge G_b a b -> graph_indom G_b a /\ graph_indom G_b b.
Proof.
  intros a b Hedge. revert Hedge. unfold_G_b.
  intro Hedge. cbn in Hedge. rew_set in Hedge.
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
    first [ contradiction
          | (match goal with H : (_, _) = (_, _) |- _ =>
               inversion H; subst; unfold graph_indom; cbn; rew_dom; rew_set;
               split; solve_in end) ].
Qed.

(* the root is an ancestor of every commit *)
Lemma anc_root_G_b : forall c, graph_indom G_b c -> ancestor G_b 0 c.
Proof.
  introv Hc. unfold graph_indom, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit in Hc.
  cbn in Hc. rew_dom. rew_set in Hc.
  repeat (match goal with H : _ \/ _ |- _ => destruct H end).
  all: try (exfalso; eapply indom_empty_inv; eassumption).
  all: subst.
  all: unfold_G_b.
  - apply AncestorRefl.
  - eapply AncestorTrans; [ apply AncestorRefl | ]. cbn. rew_set. repeat first [ left; reflexivity | right ].
  - eapply AncestorTrans; [ apply AncestorRefl | ]. cbn. rew_set. repeat first [ left; reflexivity | right ].
  - eapply AncestorTrans with (c2 := 1);
      [ (eapply AncestorTrans; [ apply AncestorRefl | ]) | ];
      cbn; rew_set; repeat first [ left; reflexivity | right ].
  - eapply AncestorTrans; [ apply AncestorRefl | ]. cbn. rew_set. repeat first [ left; reflexivity | right ].
  - eapply AncestorTrans with (c2 := 4);
      [ (eapply AncestorTrans; [ apply AncestorRefl | ]) | ];
      cbn; rew_set; repeat first [ left; reflexivity | right ].
Qed.

Lemma indom_writes :
  forall G c j,
    graph_indom G c -> j \indom (fst G)[c] ->
    graph_writes G c j ((fst G)[c][j]).
Proof.
  introv Hc Hj. destruct G as (C & P). cbn in *.
  exists (C[c]). split.
  - unfold graph_binds. applys binds_of_indom_read Hc; (reflexivity || typeclass).
  - applys binds_of_indom_read Hj; (reflexivity || typeclass).
Qed.

(* a non-volatile variable is only written by the initialisation and by t1's push *)
Lemma nonvol_writer :
  forall c j,
    graph_indom G_b c -> j \indom (fst G_b)[c] -> j \notin Volatiles ->
    c = 0 \/ c = 1.
Proof.
  introv Hc Hj Hnv.
  forwards Hgw: indom_writes Hc Hj.
  forwards [(Hc0 & _) | [(Hc1 & _) | (_ & Hz)]]: writers_G_b Hgw.
  - left. exact Hc0.
  - right. exact Hc1.
  - exfalso. subst j. applys Hnv Hxvol.
Qed.

Lemma cs_inv :
  forall G c1 c2 j,
    j \in change_set G c1 c2 ->
    j \notin Volatiles /\
    exists c, j \indom (fst G)[c] /\ ancestor G c c2 /\ ~ ancestor G c c1.
Proof. introv H. destruct G as (C & P). destruct H as (Hnv & c & Hc). split~. exists c. exact Hc. Qed.

Lemma conflict_free_graph_G_b : conflict_free_graph G_b.
Proof.
  intros c1 c2 Hd1 Hd2. unfold conflict_free_merge. rew_set. intros j Hj1 Hj2.
  rew_set in Hj1. destruct Hj1 as [Hde | Hcs1]; [ applys indom_empty_inv Hde | ].
  forwards (Hnv & ha & Hja & Hanca & Hnanca): cs_inv Hcs1.
  forwards (_ & hb & Hjb & Hancb & Hnancb): cs_inv Hj2.
  asserts Hindha: (graph_indom G_b ha).
  { forwards [Hin | Heq]: ancestor_src_indom edges_indom_G_b Hanca; [ exact Hin | subst ha; exact Hd1 ]. }
  asserts Hindhb: (graph_indom G_b hb).
  { forwards [Hin | Heq]: ancestor_src_indom edges_indom_G_b Hancb; [ exact Hin | subst hb; exact Hd2 ]. }
  forwards Hr1: anc_root_G_b Hd1. forwards Hr2: anc_root_G_b Hd2.
  forwards [-> | ->]: nonvol_writer Hindha Hja Hnv.
  - applys Hnanca Hr2.
  - forwards [-> | ->]: nonvol_writer Hindhb Hjb Hnv.
    + applys Hnancb Hr1.
    + applys Hnanca Hancb.
Qed.

Lemma indom_5_G_b : graph_indom G_b 5.
Proof. unfold graph_indom, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit. cbn. rew_dom. rew_set. solve_in. Qed.

Lemma indom_4_G_b : graph_indom G_b 4.
Proof. unfold graph_indom, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit. cbn. rew_dom. rew_set. solve_in. Qed.

(* t2 runs to completion: its volatile write, [print(y)] reads the initial [v0],
   and [print(x)] reads t2's own [x = 2], carried by [x]'s stored commit. *)
Lemma t2_completes :
  forall (T : threads),
    binds T t2 (state_running, te_exp q1, empty, root_commit) ->
    exists T' G' L' V' c,
      steps (T, G_end, empty, V_end) (T', G', L', V') /\
      binds T' t2 (state_terminated, te_ret (res v0 v2), empty, c) /\
      (forall s, binds T t1 s -> binds T' t1 s).
Proof.
  introv Hb2.
  eexists _, _, _, _, _. splits.
  - (* x = 2: volatile write; no pull, no conflict check *)
    eapply steps_step.
    { eapply StepWriteVolatile with (t := t2) (x := x) (v := v2) (h' := 4) (h'' := 5).
      - exact Hb2.
      - apply (proj1 Q1).
      - assumption.
      - solve_fresh2.
      - solve_fresh2.
      - unfold push_volatile, do_commit. rewrite read_update_same. reflexivity. }
    (* print(y): a global read, which does not see t1's write *)
    eapply steps_step.
    { eapply StepReadGlobal with (t := t2) (x := y) (v := v0).
      - rewrite Q1k. apply binds_update_same.
      - apply (proj1 Q2).
      - assumption.
      - intro Hin. applys indom_empty_inv Hin.
      - apply t2_reads_y. }
    (* print(x): a volatile read, which returns the value carried by [x]'s
       stored commit *)
    eapply steps_step.
    { eapply StepReadVolatile with (t := t2) (x := x) (v := v2) (h'' := 6).
      - rewrite Q2k. apply binds_update_same.
      - apply (proj1 (Q3 v0)).
      - assumption.
      - match goal with |- conflict_free_merge _ _ ?c _ =>
          replace c with 5 by (unfold vc_read; symmetry; apply read_default_update_same)
        end.
        apply conflict_free_graph_G_b; [ apply indom_4_G_b | apply indom_5_G_b ].
      - match goal with |- view_conflict_free _ ?c =>
          replace c with 5 by (unfold vc_read; symmetry; apply read_default_update_same)
        end.
        apply conflict_free_graph_view;
          [ apply edges_indom_G_b | apply indom_5_G_b | apply conflict_free_graph_G_b ].
      - solve_fresh2.
      - unfold pull_volatile, do_merge. rewrite read_update_same. reflexivity.
      - rewrite Q2k. apply binds_update_same.
      - match goal with |- graph_writes _ ?c _ _ =>
          replace c with 5 by (unfold vc_read; symmetry; apply read_default_update_same)
        end.
        exists ((empty : diff)[x := v2]). split.
        + unfold graph_binds, G_b, G_end, G_init, graph_merge_with, graph_merge, graph_commit.
          cbn. apply binds_update_same.
        + apply binds_update_same. }
    (* t2 ends *)
    eapply steps_step.
    { eapply StepEnd with (t := t2) (h' := 7).
      - rewrite Q3k. apply binds_update_same.
      - solve_fresh2.
      - unfold do_commit. rewrite read_update_same. reflexivity. }
    apply steps_refl.
  - solve_binds.
  - introv Hs. solve_binds. exact Hs.
Qed.

(* The example on [non-conflicting-non-pulling-volatile-writes]: t1 runs to
   completion, then t2 runs to completion without any conflict; t2's volatile
   write does not pull, so [print(y)] returns the initial [v0], while
   [print(x)] returns t2's own [x = 2] (cf. "print(y) gives 0; print(x) gives 2"
   in volatile.tex). The result [res v0 v2] of t2 records the two prints. *)
Theorem volatile_example :
  exists T G L V c1 c2,
    steps init_cfg (T, G, L, V) /\
    binds T t1 (state_terminated, te_ret r1, empty, c1) /\
    binds T t2 (state_terminated, te_ret (res v0 v2), empty, c2).
Proof.
  forwards (T & G & Hsteps & HG & Hb1 & Hb2 & Hdom): t1_completes.
  subst G.
  forwards (T' & G' & L' & V' & c & Hsteps2 & Hb2' & Hb1'): t2_completes Hb2.
  exists T' G' L' V' 3 c. splits.
  - clear - Hsteps Hsteps2. induction Hsteps; [ exact Hsteps2 | econstructor; eauto ].
  - apply Hb1'. exact Hb1.
  - exact Hb2'.
Qed.

End Example.
