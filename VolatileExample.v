From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.

(* ------------------------------------------------------------------------ *)
(* The volatile example of volatile.tex, on the Branching model of          *)
(* [non-conflicting-volatiles] (a volatile write pulls, and volatiles are   *)
(* ignored by conflict checking).                                           *)
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

Variables (x y : var) (v1 v2 : val).
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

(* Both threads start at the root commit, with empty staging areas. *)
Definition init_cfg : cfg :=
  (empty[t1 := (state_new, te_exp p1, (empty : diff), root_commit)]
        [t2 := (state_new, te_exp q1, (empty : diff), root_commit)],
   graph_root root_commit, (empty : locks), (empty : volatiles)).

Hint Resolve Ht12 : core.
Lemma Ht21 : t2 <> t1. Proof. auto. Qed.
Hint Resolve Ht21 : core.

(* [c] is not in the domain of the commit data of a small concrete graph *)
Ltac solve_fresh :=
  unfold commit_fresh, graph_merge, graph_commit, graph_root; cbn; rew_dom;
  let H := fresh "Hin" in intro H; rew_set in H;
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
  first [ (eapply indom_empty_inv; eassumption) | discriminate ].

Ltac solve_binds :=
  repeat first [ apply binds_update_same | apply binds_update_neq; [ solve [auto] | ] ].

(* The commit graph and the stored commit of [x] once t1 has finished:
   0 (root) --merge--> 1 --push (y = 1, x = 1)--> 2 --end--> 3. *)
Definition G_end : graph :=
  graph_commit
    (graph_commit (graph_merge (graph_root root_commit) 0 0 1) 1 2
       ((empty : diff)[y := v1][x := v1]))
    2 3 (empty : diff).

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
    (* x = 1: a volatile write *)
    eapply steps_step.
    { eapply StepWriteVolatile with (t := t1) (x := x) (v := v1) (h' := 1) (h'' := 2).
      - rewrite P1k. solve_binds.
      - apply (proj1 P2).
      - assumption.
      - rewrite vc_read_empty. apply conflict_free_merge_self.
      - solve_fresh.
      - unfold pull_volatile, do_merge. rewrite read_update_same. reflexivity.
      - rewrite P1k. apply binds_update_same.
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

Lemma vc_read_V_c : vc_read (V_end[x := 5]) x = 5.
Proof. unfold vc_read. apply read_default_update_same. Qed.

(* t2's volatile write pulls [x]'s stored commit (2) into a merge commit 4,
   then pushes commit 5 holding [x = 2]; t2's volatile read of [x] pulls the
   stored commit (now 5) into merge commit 6; and t2 ends with commit 7. *)
Definition G_b : graph := graph_merge G_end (vc_read V_end x) root_commit 4.
Definition G_c : graph := graph_commit G_b 4 5 ((empty : diff)[x := v2]).
Definition G_d : graph :=
  graph_merge G_c (vc_read (V_end[x := 5]) x) 5 6.

Ltac solve_fresh2 := unfold G_end, G_b, G_c, G_d; solve_fresh.

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

Ltac edges_incr :=
  intros ? ? Hedge; cbn in Hedge; rew_set in Hedge;
  repeat (match goal with H : _ \/ _ |- _ => destruct H end);
  first [ contradiction
        | (match goal with H : (_, _) = (_, _) |- _ => inversion H; subst; try unfold root_commit; nat_math end) ].

Lemma edges_G_end : forall a b : nat, graph_edge G_end a b -> a < b.
Proof. unfold G_end, graph_merge, graph_commit, graph_root. edges_incr. Qed.

Lemma edges_G_d : forall a b : nat, graph_edge G_d a b -> a < b.
Proof.
  unfold G_d, G_c, G_b, G_end, graph_merge, graph_commit, graph_root.
  rewrite vc_read_V_end, vc_read_V_c. edges_incr.
Qed.

Lemma change_set_nvol :
  forall G c1 c2 j, j \in change_set G c1 c2 -> j \notin Volatiles.
Proof. introv H. destruct G as (C & P). destruct H as (Hnv & _). exact Hnv. Qed.

Ltac edge_in := cbn; rew_set; repeat first [ left; reflexivity | right ].

(* t2's volatile write does not conflict: of t1's changes only [y] is visible
   to t2, [x] being ignored, and t2 has nothing in the other direction. *)
Lemma t2_write_no_conflict :
  conflict_free_merge ((empty : diff)[x := v2]) root_commit 2 G_end.
Proof.
  unfold conflict_free_merge. rew_set. intros j Hj1 Hj2.
  forwards Hnv: change_set_nvol Hj2.
  rew_set in Hj1. destruct Hj1 as [Hd | Hcs].
  - rew_dom. rew_set in Hd. destruct Hd as [Hd | Hd].
    + applys indom_empty_inv Hd.
    + subst j. applys Hnv Hxvol.
  - unfold change_set in Hcs. destruct Hcs as (_ & c & _ & Hanc & Hnanc).
    forwards Hle: anc_le edges_G_end Hanc.
    asserts Hc0: ((c : nat) = 0). { unfold root_commit in Hle. nat_math. }
    subst c. applys Hnanc.
    eapply AncestorTrans; [ eapply AncestorTrans; [ apply AncestorRefl | ] | ];
      unfold G_end, graph_root; edge_in.
Qed.

Ltac peel H :=
  let H' := fresh "Hp" in
  forwards H': binds_update_inv H; clear H; case_if in H'.

(* the only writers in [G_c]: commit 2 (t1's push) and commit 5 (t2's push) *)
Lemma writers_G_c :
  forall c z w,
    graph_writes G_c c z w ->
    (c = 2 /\ ((z = y /\ w = v1) \/ (z = x /\ w = v1))) \/
    (c = 5 /\ z = x /\ w = v2).
Proof.
  introv (d & Hb & Hbd).
  clear Q1 Q1k Q2 Q2k Q3 Q3k P1 P1k P2 P2k.
  unfold graph_binds, G_c, G_b, G_end, graph_root in Hb. cbn in Hb.
  repeat (match goal with H : binds (_[_:=_]) _ _ |- _ => peel H end).
  all: subst.
  all: repeat (match goal with H : binds (_[_:=_]) _ _ |- _ => peel H end).
  all: try (exfalso; match goal with H : binds _ _ _ |- _ =>
              first [ (applys binds_empty_false H; typeclass) | (applys binds_empty_false H) ] end).
  all: subst.
  all: first [ (left; split; [ reflexivity | first [ (left; split; reflexivity) | (right; split; reflexivity) ] ])
             | (right; split; [ reflexivity | split; reflexivity ]) ].
Qed.

Lemma writers_G_d :
  forall c z w,
    graph_writes G_d c z w ->
    (c = 2 /\ ((z = y /\ w = v1) \/ (z = x /\ w = v1))) \/
    (c = 5 /\ z = x /\ w = v2).
Proof.
  introv Hgw. unfold G_d in Hgw.
  destruct (classic (c = 6)) as [-> | Hne].
  - exfalso. applys graph_writes_graph_merge_same_false Hgw.
  - applys writers_G_c w. applys graph_writes_graph_merge_inv Hne Hgw.
Qed.

(* print(y) after t2's volatile write: t2 sees t1's write [y = 1] *)
Lemma t2_reads_y : is_latest_value G_c 5 y v1.
Proof.
  exists 2. splits.
  - exists ((empty : diff)[y := v1][x := v1]). split.
    + unfold graph_binds, G_c, G_b, G_end, graph_root. cbn. solve_binds.
    + apply binds_update_neq; [ exact (fun H => x_neq_y (eq_sym H)) | apply binds_update_same ].
  - unfold G_c, G_b, G_end, graph_root. rewrite vc_read_V_end.
    apply AncestorTrans with (c2 := 4);
      [ apply AncestorTrans with (c2 := 2); [ apply AncestorRefl | edge_in ] | edge_in ].
  - introv Hw Ha1 Ha2. forwards [(Hc & _) | (_ & Hz & _)]: writers_G_c Hw.
    + exact Hc.
    + exfalso. applys x_neq_y. symmetry. exact Hz.
Qed.

(* print(x) after t2's volatile read pull: t2 sees its own write [x = 2] *)
Lemma t2_reads_x : is_latest_value G_d 6 x v2.
Proof.
  exists 5. splits.
  - unfold G_d. apply graph_writes_graph_merge; [ discriminate | ].
    exists ((empty : diff)[x := v2]). split.
    + unfold graph_binds, G_c, G_b, G_end, graph_root. cbn. solve_binds.
    + apply binds_update_same.
  - unfold G_d, G_c, G_b, G_end, graph_root. rewrite vc_read_V_c.
    apply AncestorTrans with (c2 := 5); [ apply AncestorRefl | edge_in ].
  - introv Hw Ha1 Ha2. forwards [(Hc & _) | (Hc & _)]: writers_G_d Hw.
    + exfalso. forwards Hle: anc_le edges_G_d Ha1. nat_math.
    + exact Hc.
Qed.

(* t2 runs to completion after t1: every step is enabled, and [print(y)] and
   [print(x)] return [v1] and [v2] (recorded in t2's final result). *)
Lemma t2_completes :
  forall (T : threads),
    binds T t2 (state_running, te_exp q1, empty, root_commit) ->
    exists T' G' L' V' c,
      steps (T, G_end, empty, V_end) (T', G', L', V') /\
      binds T' t2 (state_terminated, te_ret (res v1 v2), empty, c) /\
      (forall s, binds T t1 s -> binds T' t1 s).
Proof.
  introv Hb2.
  eexists _, _, _, _, _. splits.
  - (* x = 2: volatile write *)
    eapply steps_step.
    { eapply StepWriteVolatile with (t := t2) (x := x) (v := v2) (h' := 4) (h'' := 5).
      - exact Hb2.
      - apply (proj1 Q1).
      - assumption.
      - rewrite vc_read_V_end. apply t2_write_no_conflict.
      - solve_fresh2.
      - unfold pull_volatile, do_merge. rewrite (read_of_binds Hb2). reflexivity.
      - apply binds_update_same.
      - solve_fresh2.
      - unfold push_volatile, do_commit. rewrite read_update_same. reflexivity. }
    (* print(y): a global read *)
    eapply steps_step.
    { eapply StepReadGlobal with (t := t2) (x := y) (v := v1).
      - rewrite Q1k. apply binds_update_same.
      - apply (proj1 Q2).
      - assumption.
      - intro Hin. applys indom_empty_inv Hin.
      - apply t2_reads_y. }
    (* print(x): a volatile read *)
    eapply steps_step.
    { eapply StepReadVolatile with (t := t2) (x := x) (v := v2) (h'' := 6).
      - rewrite Q2k. apply binds_update_same.
      - apply (proj1 (Q3 v1)).
      - assumption.
      - match goal with |- conflict_free_merge _ _ ?c _ =>
          replace c with 5 by (unfold vc_read; symmetry; apply read_default_update_same)
        end.
        apply conflict_free_merge_self.
      - solve_fresh2.
      - unfold pull_volatile, do_merge. rewrite read_update_same. reflexivity.
      - rewrite Q2k. apply binds_update_same.
      - apply t2_reads_x. }
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

(* The example on [non-conflicting-volatiles]: t1 runs to completion, then t2
   runs to completion without any conflict, printing [y = 1] and [x = 2]
   (cf. the third execution in volatile.tex). *)
Theorem volatile_example :
  exists T G L V c1 c2,
    steps init_cfg (T, G, L, V) /\
    binds T t1 (state_terminated, te_ret r1, empty, c1) /\
    binds T t2 (state_terminated, te_ret (res v1 v2), empty, c2).
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

(* [Print Assumptions volatile_example] lists only the [Common.v] parameters
   and the TLC axioms: the program assumptions are section hypotheses. *)
