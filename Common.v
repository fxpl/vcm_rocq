From TLC Require Export LibTactics LibLogic LibList LibSet LibMap LibNat LibMin LibEpsilon.

From Stdlib Require Export Lia.

(* Hint database *)
Hint Extern 1 => congruence : vcm.
Hint Extern 1 => nat_math : vcm.

Ltac auto_star ::= try solve [intuition eauto with vcm].
Ltac auto_tilde ::= try solve [intuition auto with vcm].

Parameters val exc exp : Type.

Parameter inhab_val : Inhab val.
Parameter inhab_exc : Inhab exc.
Parameter inhab_exp : Inhab exp.

(* Register the Inhab witnesses as typeclass instances so that [Inhab val] etc.
   are resolved automatically (they are [Parameter]s, not [Instance]s, so
   typeclass resolution would otherwise not find them). *)
Existing Instance inhab_val.
Existing Instance inhab_exc.
Existing Instance inhab_exp.

(* Something to feed to the continuation when no value is needed *)
Parameter void : val.

(* thread id *)
Definition tid := nat.

(* The distinguished initial ("root") thread which exists at program start. *)
Parameter t_root : tid.

(* lock id *)
Definition lid := nat.

(* variable *)
Definition var := nat.

Inductive ret : Type :=
| ret_val (v : val)
| ret_exc (e : exc)
| ret_tid (t : tid)
| ret_race
.

Coercion ret_val : val >-> ret.
Coercion ret_exc : exc >-> ret.
Coercion ret_tid : tid >-> ret.

Inductive eff :=
| eff_spawn (e : exp)
| eff_join (t : tid)
| eff_read (x : var)
| eff_write (x : var) (v : val)
| eff_lock (l : lid)
| eff_unlock (l : lid)
.

Inductive thread_state :=
| state_new
| state_running
| state_terminated
.

#[global]
Instance inhab_thread_state : Inhab thread_state.
Proof. apply (Inhab_of_val state_new). Qed.

Inductive thread_exp :=
| te_exp (e : exp)
| te_ret (r : ret)
.

#[global]
Instance inhab_thread_exp : Inhab thread_exp.
Proof. apply (Inhab_of_val (te_ret void)). Qed.

Definition cont := ret -> thread_exp.

Parameter step_ul : exp -> cont -> eff -> Prop.

Inductive lock_state :=
| ls_free
| ls_held (t : tid)
.

#[global]
Instance inhab_lock_state : Inhab lock_state.
Proof. apply (Inhab_of_val ls_free). Qed.

Definition commit := nat.

Definition root_commit := 0.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition diff := map var val.

Definition empty_diff : diff := empty.

Instance inhab_diff : Inhab diff.
  constructor. exists empty_diff. tauto.
Qed.

(* A tactic for rewriting domain equations *)
Ltac rew_dom :=
  repeat
  match goal with
  | H : context[dom ?M[?k := ?v]] |- _ =>
      replace (dom M[k := v]) with (union (dom M) (single k)) in H;
      [| solve[symmetry; apply dom_update] ]
  | _ : _ |- context[dom ?M[?k := ?v]] =>
      replace (dom M[k := v]) with (union (dom M) (single k));
      [| solve[symmetry; apply dom_update] ]
  end.

Lemma mem_le_sum : forall (n : nat) (l : list nat),
  mem n l -> n <= fold_right plus 0 l.
Proof.
  introv Hmem. induction Hmem; rewrite fold_right_cons; nat_math.
Qed.

(* No mechanisation is complete without custom list lemmas *)
Lemma single_eq_middle_inv :
  forall A (x y : A) l1 l2,
    x :: nil = l1 ++ y :: l2 ->
    l1 = nil /\ x = y /\ l2 = nil.
Proof.
  introv Heq.
  destruct l1; rew_list in *; inverts* Heq.
  forwards: nil_eq_middle_inv y l1 l2; rew_list~.
Qed.

Lemma last_eq_middle_inv :
  forall A (xs : list A) x ys1 y ys2,
    xs & x = ys1 ++ y :: ys2 ->
    x = y /\ xs = ys1 /\ ys2 = nil \/
    exists ys2', ys2 = ys2' & x /\ xs = ys1 ++ y :: ys2'.
Proof.
  introv Heq.
  gen ys1 ys2 x y.
  induction xs; rew_list in *; intros.
  - destruct ys1; rew_list in *; inverts* Heq.
    apply nil_eq_app_inv in H1 as (-> & contra). congruence.
  - destruct ys1; rew_list in *; inverts* Heq.
    forwards* [(-> & -> & ->) | (ys2' & -> & ->)]: IHxs H1.
Qed.
