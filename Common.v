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

(* lock id *)
Definition lid := nat.

(* location *)
Definition loc := nat.

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
| eff_read (i : loc)
| eff_write (i : loc) (v : val)
| eff_lock (l : lid)
| eff_unlock (l : lid)
.

Definition cont := ret -> exp.

Parameter step_ul : exp -> cont -> eff -> Prop.

Inductive thread_state :=
| state_new
| state_running
| state_terminated
.

Inductive thread_exp :=
| te_exp (e : exp)
| te_ret (r : ret)
.

Inductive lock_state :=
| ls_free
| ls_held (t : tid)
.

#[global]
Instance inhab_lock_state : Inhab lock_state.
Proof. apply (Inhab_of_val ls_free). Qed.

(*
Module FMap.

Inductive fmap (A B : Type) := make {
  map_data :> map A B;
  map_finite : finite map_data
}.

Lemma finite_update :
  forall A B (M : map A B) k v, finite M -> finite (M[k := v]).
Proof.
  introv Hfin.
    rewrite update_eq_union_single. apply~ finite_union.
    apply finite_single.
Qed.

Instance fmap_binds_inst : forall A B, BagBinds A B (fmap A B).
  constructor. rapply (@binds_impl A B).
Defined.

Instance fmap_update_inst : forall A B, BagUpdate A B (fmap A B).
  constructor.
  apply (fun M k v =>
           make A B (map_data _ _ M)[k:=v]
             (finite_update A B M k v (map_finite _ _ M))).
Qed.

Instance fmap_dom_inst : forall A B, BagDom (fmap A B) (set A).
  constructor. rapply (@dom_impl A B).
Defined.

(* TODO: Do I need to mirror all of LibMap? rew_set and lemmas
don't work on fmaps (of course). I could write the semantics so
that they work on the underlying map instead. *)
End FMap.
*)

