From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import Branching.

(* ------------------------------------------------------------------------ *)
(* The volatile example of volatile.tex, on the Branching model of [main]   *)
(* (a volatile write pulls, and writes to volatiles conflict).              *)
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
  destruct Hj2 as (c0 & _ & Hanc & Hnanc). applys Hnanc Hanc.
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
Variables (q1 q2 q3 : exp) (j1 j2 j3 : cont) (r2 : ret).
Hypothesis Q1 : only_step q1 j1 (eff_write x v2).
Hypothesis Q1k : j1 void = te_exp q2.
Hypothesis Q2 : only_step q2 j2 (eff_read y).
Hypothesis Q2k : forall v, j2 (ret_val v) = te_exp q3.
Hypothesis Q3 : only_step q3 j3 (eff_read x).
Hypothesis Q3k : forall v, j3 (ret_val v) = te_ret r2.

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

(* t2's write to the volatile [x] conflicts with t1's: the stored commit of
   [x] (commit 2) holds t1's write of [x] (and of [y]), which t2's commit
   (the root) has not seen. *)
Lemma t2_write_conflicts :
  ~ conflict_free_merge ((empty : diff)[x := v2]) root_commit (vc_read V_end x) G_end.
Proof.
  intro Hcf.
  asserts Hvc: (vc_read V_end x = 2).
  { unfold V_end, vc_read. apply read_default_update_same. }
  rewrite Hvc in Hcf.
  unfold conflict_free_merge in Hcf. rew_set in Hcf.
  applys Hcf x.
  - rew_set. left. rew_dom. rew_set. right. reflexivity.
  - unfold change_set, G_end. exists 2. splits.
    + cbn. rewrite read_update_neq; [ | discriminate ]. rewrite read_update_same.
      rew_dom. rew_set. right. reflexivity.
    + apply AncestorRefl.
    + intro Hanc. inversion Hanc; subst.
      rename H0 into Hedge. cbn in Hedge. rew_set in Hedge.
      repeat (match goal with H : _ \/ _ |- _ => destruct H end);
        try (unfold root_commit in *; congruence).
Qed.

(* In the final configuration only t1 (terminated) and t2 (running [q1]) exist. *)
Lemma final_binds :
  forall (T : threads) (t : tid) (s : thread),
    binds T t1 (state_terminated, te_ret r1, empty, 3) ->
    binds T t2 (state_running, te_exp q1, empty, root_commit) ->
    (forall t, t \indom T -> t = t1 \/ t = t2) ->
    binds T t s ->
    (t = t1 /\ s = (state_terminated, te_ret r1, empty, 3)) \/
    (t = t2 /\ s = (state_running, te_exp q1, empty, root_commit)).
Proof.
  introv Hb1 Hb2 Hdom Hb.
  forwards [-> | ->]: Hdom (indom_of_binds Hb).
  - left. split; [ reflexivity | applys binds_inj Hb Hb1; typeclass ].
  - right. split; [ reflexivity | applys binds_inj Hb Hb2; typeclass ].
Qed.

(* No step is possible once t1 has finished and t2 is about to write [x]. *)
Lemma t2_stuck :
  forall (T : threads),
    binds T t1 (state_terminated, te_ret r1, empty, 3) ->
    binds T t2 (state_running, te_exp q1, empty, root_commit) ->
    (forall t, t \indom T -> t = t1 \/ t = t2) ->
    forall cfg', ~ step (T, G_end, empty, V_end) cfg'.
Proof.
  introv Hb1 Hb2 Hdom Hstep.
  inverts Hstep;
    match goal with
    | H : binds T ?t ?s |- _ =>
        forwards [(-> & Hs) | (-> & Hs)]: final_binds Hb1 Hb2 Hdom H;
        inverts Hs
    end.
  (* rules with a second thread (join): also pin down the acting thread *)
  all: try (match goal with
        | H : binds _ ?t (state_running, te_exp ?e, ?d, ?h) |- _ =>
            is_var e;
            forwards [(-> & Hs) | (-> & Hs)]: final_binds Hb1 Hb2 Hdom H;
            inverts Hs
        end).
  all: try (match goal with
        | Hul : step_ul q1 _ _ |- _ =>
            destruct ((proj2 Q1) _ _ Hul) as [_ Hc]; inversion Hc; subst
        end).
  all: first [ contradiction | (eapply t2_write_conflicts; eassumption) ].
Qed.

(* The example on [main]: t1 runs to completion, then t2's first action, the
   volatile write [x = 2], is a conflict with t1's [x = 1]; the configuration
   is stuck and t2 never gets to its prints (cf. "Conflict at x = 2" in
   volatile.tex). *)
Theorem volatile_example :
  exists T,
    steps init_cfg (T, G_end, empty, V_end) /\
    binds T t2 (state_running, te_exp q1, empty, root_commit) /\
    ~ conflict_free_merge ((empty : diff)[x := v2]) root_commit
        (vc_read V_end x) G_end /\
    (forall cfg', ~ step (T, G_end, empty, V_end) cfg').
Proof.
  forwards (T & G & Hsteps & HG & Hb1 & Hb2 & Hdom): t1_completes.
  subst G. exists T. splits.
  - exact Hsteps.
  - exact Hb2.
  - apply t2_write_conflicts.
  - applys t2_stuck Hb1 Hb2 Hdom.
Qed.

End Example.

(* [Print Assumptions volatile_example] lists only the [Common.v] parameters
   and the TLC axioms: the program assumptions are section hypotheses. *)
