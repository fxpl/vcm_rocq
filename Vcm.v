From TLC Require Import LibTactics LibLogic LibList LibSet LibMap LibNat LibMin LibEpsilon.

Require Import Lia.

(* Hint database *)
Hint Extern 1 => congruence : vcm.
Hint Extern 1 => nat_math : vcm.

Ltac auto_star ::= try solve [intuition eauto with vcm].
Ltac auto_tilde ::= try solve [intuition auto with vcm].

Parameters val exc exp : Type.

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

Module SharedMemory.

(* Import FMap. *)

Definition thread := (thread_state * thread_exp)%type.

(* TODO: Somewhere along the line, rew_set stopped working for
updated threads (I think it used to work!?). Turning this from a
Definition into a Notation seemed to work, but I don't like it...
*)
Definition threads := (map tid thread).

(*
Instance threads_dom_inst : BagDom threads (set tid) := @LibMap.dom_inst tid thread.

Instance threads_union_inst : BagUnion threads := @union_inst tid thread.
*)

(* Needed for some reason (to let typeclass instantiation look
inside the definition?) *)
(*
Instance in_inst : BagIn tid (set tid).
  constructor. rapply (@in_impl tid).
Defined.
*)

(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Defined.
*)

(* Not sure why these are needed for fmap *)
(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Qed.

Instance threads_binds_inst : BagBinds tid thread threads.
  constructor. rapply (@binds_impl tid thread).
Qed.
*)
Definition heap := map loc val.

(*
Instance heap_binds_inst : BagBinds loc val heap.
  constructor. rapply (@binds_impl loc val).
Qed.
*)
Definition locks := map lid lock_state.

(*
Instance locks_binds_inst : BagBinds lid lock_state locks.
  constructor. rapply (@binds_impl lid lock_state).
Qed.
*)

Definition cfg := (threads * heap * locks)%type.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T H L t e,
    binds T t (state_new, e) ->
    step (T, H, L) (T[t := (state_running, e)], H, L)
| StepEnd : forall (T : threads) H L t r,
    binds T t (state_running, te_ret r) ->
    step (T, H, L) (T[t := (state_terminated, te_ret r)], H, L)
| StepRead : forall (T : threads) H L t e K i v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read i) ->
    binds H i v ->
    step (T, H, L) (T[t := (state_running, te_exp (K (ret_val v)))], H, L)
| StepWrite : forall (T : threads) (H : heap) L t e K i v,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write i v) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H[i := v], L)
| StepSpawn : forall (T : threads) H L (t t' : tid) e K e',
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step (T, H, L) (T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')], H, L)
| StepJoin : forall (T : threads) H L t t' e K r,
    (* This means multiple threads can join the same thread *)
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step (T, H, L) (T[t := (state_running, te_exp (K r))], H, L)
| StepLock : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_held t])
| StepRelease : forall (T : threads) H (L : locks) t e K l,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void))], H, L[l := ls_free])
.

End SharedMemory.

Module Log.

Inductive event :=
| event_spawn (t1 t2 : tid)
| event_join (t1 t2 : tid)
| event_read (t : tid) (i : loc) (v : val)
| event_write (t : tid) (i : loc) (v : val)
| event_lock (t : tid) (l : lid)
| event_unlock (t : tid) (l : lid)
| event_start (t : tid)
| event_end (t : tid)
.

Definition get_thread (e : event) :=
  match e with
  | event_spawn t _
  | event_join t _
  | event_read t _ _
  | event_write t _ _
  | event_lock t _
  | event_unlock t _
  | event_start t
  | event_end t => t
  end.

Definition touches_lock (l : lid) (e : event) :=
  match e with
  | event_lock _ l'
  | event_unlock _ l' => l = l'
  | _ => False
  end.

Definition writes_location (i : loc) (e : event) :=
  match e with
  | event_write _ j _ => i = j
  | _ => False
  end.

Definition is_write (e : event) :=
  match e with
  | event_write _ _ _ => True
  | _ => False
  end.

Definition log := list event.

Inductive hb (log : log) : event -> event -> Prop :=
| HbPo : forall l1 l2 t e1 e2,
    (* Events are adjacent when projecting the program order of a thread *)
    l1 ++ e1 :: e2 :: l2 = LibList.filter (fun e => get_thread e = t) log ->
    hb log e1 e2
| HbLock : forall l1 l2 t1 t2 l,
    (* Events unlock l/lock l are adjacent when projecting the events of a lock *)
    l1 ++ event_unlock t1 l :: event_lock t2 l :: l2 =
      LibList.filter (fun e => touches_lock l e) log ->
    hb log (event_unlock t1 l) (event_lock t2 l)
| HbSpawn : forall l1 l2 t1 t2,
    (* The spawn event of a thread is before its start event *)
    (* TODO: No need to split list. Well-formedness will ensure they are ordered *)
    log = l1 ++ l2 ->
    mem (event_spawn t1 t2) l1 ->
    mem (event_start t2) l2 ->
    hb log (event_spawn t1 t2) (event_start t2)
| HbJoin : forall l1 l2 t1 t2,
    (* The end event of a thread is before its join event(s) *)
    log = l1 ++ l2 ->
    mem (event_end t2) l1 ->
    mem (event_join t1 t2) l2 ->
    hb log (event_end t2) (event_join t1 t2)
| HbTrans : forall e1 e2 e3,
    (* Transitivity *)
    hb log e1 e2 ->
    hb log e2 e3 ->
    hb log e1 e3
.

Inductive wf_lock_log : log -> Prop :=
| WfLockEmpty :
  wf_lock_log nil
| WfLockSingle :
  forall t l,
    wf_lock_log (event_lock t l :: nil)
| WfLockUnlock :
  forall t1 l log,
    wf_lock_log log ->
    wf_lock_log (event_lock t1 l :: event_unlock t1 l :: log)
.

Definition wf_log (log : log) : Prop :=
  (* Unique spawns *)
  (forall l1 l2 t1 t2,
      log = l1 ++ event_spawn t1 t2 :: l2 ->
      (~exists t1', mem (event_spawn t1' t2) (l1 ++ l2)))

  (* Alternative formulation based on length*)
  (* forall t2, length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) log) <= 1 x*)
  /\
  (* Unique starts *)
  (forall l1 l2 t,
      log = l1 ++ event_start t :: l2 ->
      (~mem (event_start t) (l1 ++ l2)))
  /\
  (* Unique ends *)
  (forall l1 l2 t,
      log = l1 ++ event_end t :: l2 ->
      (~mem (event_end t) (l1 ++ l2)))
  /\
  (* Threads start after spawning *)
  (forall l1 l2 t2,
      log = l1 ++ event_start t2 :: l2 ->
      exists t1, mem (event_spawn t1 t2) l1)
  /\
  (* Threads are joined after ending *)
  (forall l1 l2 t1 t2,
      log = l1 ++ event_join t1 t2 :: l2 ->
      mem (event_end t2) l1)
  /\
  (* Threads start by starting *)
  (forall l1 l2 e t,
      log = l1 ++ e :: l2 ->
      get_thread e = t ->
      e <> event_start t ->
      mem (event_start t) l1)
  /\
  (* Threads end by ending *)
  (forall l1 l2 t,
      log = l1 ++ event_end t :: l2 ->
      LibList.Forall (fun e => get_thread e <> t) l2)
  /\
  (* Locks are locked and unlocked, in that order, by the same thread *)
  (forall l,
      wf_lock_log (LibList.filter (fun e => touches_lock l e) log)
  )
.

Definition conflict_free (log : log) : Prop :=
  forall l1 l2 t1 t2 i v1 v2,
    log = l1 ++ l2 ->
    mem (event_write t1 i v1) l1 ->
    mem (event_write t2 i v2) l2 ->
    (* mem e l2 -> *)
    (* (e = event_write t2 i v2 \/ e = event_read t2 i v2) -> *)
    hb log (event_write t1 i v1) (event_write t2 i v2)
.

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

Lemma unique_spawn_snoc' :
  forall log e t2,
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) log) <= 1 ->
    ~(exists t1 t2, e = event_spawn t1 t2) ->
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) (log & e)) <= 1.
Proof.
  introv Hlen Hnex.
  induction log0; rew_listx in *.
  - cases_if~. rew_list~.
  - cases_if~. rew_list in *. cases_if~; rew_list in *; autos~.
    false Hnex. unpack. substs*.
Qed.

End Log.

Module LoggingSharedMemory.

(* Import FMap. *)
Import SharedMemory.
Import Log.

(* TODO: Do we need something about reads? Is it enough to say
that a location exists as soon as it has been written to? *)
Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log) <-> exists e, binds T t2 (state_new, e))
      /\
      (* Ended threads are ended *)
      (forall t,
          mem (event_end t) log <-> exists e, binds T t ((state_terminated, e)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e, binds T t (state_running, e))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> binds L l (ls_held t))
      /\
      (* Unlocked locks are unlocked TODO: Could be empty if no lock yet *)
      (forall l,
          (log = nil \/ exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* The value of each location is its latest write *)
      (forall i v,
          (exists t log', LibList.filter (fun e => writes_location i e) log = log' & event_write t i v) <-> binds H i v)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T H L t e log,
    binds T t (state_new, e) ->
    step ((T, H, L), log) ((T[t := (state_running, e)], H, L), log & event_start t)
| StepEnd : forall (T : threads) H L t r log,
    binds T t (state_running, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_terminated, te_ret r)], H, L), log & event_end t)
| StepRead : forall (T : threads) H L t e K i v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_read i) ->
    binds H i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)))], H, L), log & event_read t i v)
| StepWrite : forall (T : threads) (H : heap) L t e K i v log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_write i v) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H[i := v], L), log & event_write t i v)
| StepSpawn : forall (T : threads) H L t (t' : tid) e K e' log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K t'))][t' := (state_new, te_exp e')], H, L), log & event_spawn t t')
| StepJoin : forall (T : threads) H L t t' e K r log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K r))], H, L), log & event_join t t')
| StepLock : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall (T : threads) H (L : locks) t e K l log,
    binds T t (state_running, te_exp e) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void))], H, L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step SharedMemory.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> SharedMemory.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepRead.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - destruct Hdesc as (_ & Hdstart & _).
    asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t) log0 /\ ~mem (event_start t) log0).
    { apply* Hdstart. }
    splits.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros (t1' & Hmem'). apply~ Huspawn.
      exists t1'.
      rew_listx. rew_listx in Hmem'.
      branches; autos.
    + introv Heq.
      forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      * inverts Hmem'. rew_list~.
      * intros contra. apply~ (Hustart l1 l2' t0).
        rew_listx. rew_listx in contra.
        branches; autos. inverts H0.
        false Hnmem. rew_listx~.
    + introv Heq.
      forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
      intros contra. apply~ (Huend l1 l2' t0).
      rew_listx. rew_listx in contra.
      branches; autos.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      inverts* contra.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Heq <- Hneq.
      forwards* [(<- & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    + introv Heq.
      forwards* [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
      rew_listx. splits*.
      simpl. intros ->.
      forwards~ Hmem': (Hstart l1 l2' (event_end t0) t0).
      false Hnmem. rew_listx*.
    + introv. rew_listx.
      cases_if~. rew_list~.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
(*
Instance threads_dom_inst : BagDom threads (set tid).
  constructor. rapply (@dom_impl tid thread).
Defined.
*)

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Proof.
  introv Hwf Hdesc Hstep.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock).
  inversion Hstep; substs; clear Hstep.
  - destruct Hdesc as (Hdspawned & Hdstart & Hdend & Hdrunning & Hdlock & Hdunlock & Hdwrite).
    splits.
    + intros.
      replaces ((dom (update T t (pair state_running e)))) with (union (dom T) (single t));
        [apply dom_update|].
      rew_set.
      splits.
      * introv (t3 & Hmem).
        rew_listx in Hmem. branches; [|congruence].
        asserts* Hin: (t2 \indom T).
        { apply* Hdspawned. }
        autos.
      * intros Hin. branches.
        -- asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t2) log0).
           { apply* Hdspawned. }
           exists. rew_listx*.
        -- subst.
           asserts (t1 & Hmem) : (exists t1, mem (event_spawn t1 t) log0).
           { apply* Hdspawned. }
           exists. rew_listx*.
    + intros. splits.
      * introv (t1 & Hmem & Hnmem).
        asserts Hneq: (t2 <> t).
        { intros ->. false Hnmem. rew_listx*. }
        asserts (e' & Hbinds): (exists e, binds T t2 (state_new, e)).
        { apply Hdstart. exists t1. rew_listx in *. splits*. }
        exists e'.
        apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t2 <> t).
        { intros ->. apply binds_update_same_inv in Hbinds. congruence. }
        asserts (t1 & Hmem & Hnmem): (exists t1, mem (event_spawn t1 t2) log0 /\ ~ mem (event_start t2) log0).
        { apply Hdstart. exists e'. forwards~: binds_update_neq_inv Hbinds. }
        exists. rew_listx. splits*.
    + intros. splits.
      * introv Hmem.
        rew_listx in Hmem. branches; [|congruence].
        asserts (e' & Hbinds): (exists e, binds T t0 (state_terminated, e)).
        { apply~ Hdend. }
        exists e'.
        apply~ binds_update_neq.
      * introv (e' & Hbinds).
        asserts Hneq: (t0 <> t).
        { introv ->. apply binds_update_same_inv in Hbinds. congruence. }
        forwards~ : binds_update_neq_inv Hbinds.
        rew_listx. left.
        apply* Hdend.
    + intros t0. splits.
      * introv (Hmem & Hnmem).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- exists e. apply binds_update_same.
        -- rew_listx in Hmem.
           branches; autos.
           rew_listx in Hnmem.
           asserts (e' & Hbinds) : (exists e, binds T t0 (state_running, e)).
           { apply~ Hdrunning. }
           exists e'. apply~ binds_update_neq.
      * introv (e' & Hbinds).
        destruct (classic (t0 = t)) as [->|Hneq].
        -- apply binds_update_same_inv in Hbinds.
           inverts Hbinds.
           rew_listx. splits~.
           intros contra. branches~.
           apply Hdend in H0 as (e' & Hbinds).
           forwards*: binds_inj.
        -- forwards~ Hbinds': binds_update_neq_inv Hbinds.
           asserts (Hmem & Hnmem): (mem (event_start t0) log0 /\
              ~ mem (event_end t0) log0).
           { apply* Hdrunning. }
           rew_listx. splits*.
    + intros t0 l.
      rew_listx. cases_if~. rew_list.
      apply Hdlock.
    + intros l.
      rew_listx. cases_if~. rew_list.
      splits.
      * introv Hdisj. hint last_eq_nil_inv. branches~.
        apply* Hdunlock.
      * introv Hbinds. right. apply Hdunlock in Hbinds.
        branches~. subst. (* Step is not preserving wf_log (unlocked an already free lock) *) admit.
    + intros l. rew_listx. cases_if~. rew_list.
      apply Hdwrite.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

End LoggingSharedMemory.

Module Linear.

Definition timestamp := nat.

Hint Unfold timestamp : vcm.
Hint Extern 1 => unfolds timestamp : vcm.

Definition staging_area := map loc val.

Definition thread := (thread_state * thread_exp * staging_area * timestamp)%type.

Definition threads := map tid thread.

Definition version_history := (set (val * timestamp)).

Instance version_history_in_inst : BagIn (val * timestamp) version_history.
  apply LibSet.in_inst.
Defined.

Module AlternativeHistory.
Definition version_history' := list (val * timestamp).

Fixpoint latest_value' (vh : version_history') :=
  match vh with
  | nil => None
  | (v, ts) :: vh' =>
      match latest_value' vh' with
      | None => Some (v, ts)
      | Some (v', ts') => If ts' < ts then Some (v, ts) else Some (v', ts')
      end
  end.

Lemma Forall_le_lt :
  forall m n (vh : version_history'),
    m < n ->
    Forall (fun '(_, k) => k <= m) vh ->
    Forall (fun '(_, k) => k <= n) vh.
Proof.
  introv Hlt Hall.
  induction vh as [|(? & ts1)]; rew_listx*.
  rew_listx in Hall.
  splits*.
Qed.

Lemma latest_value_max :
  forall vh v ts,
    latest_value' vh = Some (v, ts)  ->
    Forall (fun tup => let '(v', ts') := tup in ts' <= ts) vh.
Proof.
  introv Hval.
  gen v ts.
  induction vh as [|(v', ts') vh']; intros; simpls; [congruence|].
  remember (latest_value' vh') as opt.
  destruct opt as [(v'' & ts'')|].
  - cases_if; inverts Hval.
    + rew_listx. splits*; try nat_math.
      forwards* IH: IHvh' v'' ts''.
      clear Heqopt IHvh'.
      apply* Forall_le_lt.
    + rew_listx. splits*.
  - inverts Hval.
    destruct vh' as [|(v' & ts') vh'']; rew_listx*.
    simpls. destruct (latest_value' vh'') as [(? & ?)|]; [|congruence].
    cases_if*.
Qed.

Parameters v1 v2 : val.

Open Scope liblist_scope.

Definition vh_ex : version_history' := (v1, 0) :: (v2, 1) :: nil.

Example vh_example :
  latest_value' vh_ex = Some (v2, 1).
Proof.
  simpl. repeat cases_if*.
Qed.

End AlternativeHistory.

Definition latest_value (vh : version_history) : option (val * timestamp) :=
    fold (LibMonoid.monoid_make
            (fun opt opt' =>
               match opt, opt' with
               | None, _ => opt'
               | Some (v, ts), None => opt
               | Some (v, ts), Some (v', ts') =>
                   If ts < ts' then opt' else opt end) None) Some vh.
(*
Lemma latest_value_correct :
  forall vh v ts,
    latest_value vh = Some (v, ts) ->
    (forall v' ts', (v', ts') \in vh -> ts' <= ts).
Proof.
  introv. gen v ts.
  unfolds latest_value.
  apply LibSet.fold_induction; simpls*.
  - admit.
  - introv Hin Hstep Hmatch Hin'.
    destruct a as (v'' & ts'').
    destruct x as [(v''' & ts''')|].
    + cases_if*. inverts Hmatch.
      forwards*: Hstep v''' ts'''.
    + inverts Hmatch.
Admitted.
*)

Definition heap := map loc version_history.

Definition is_latest_value (H : heap) (i : loc) (v : val) :=
  exists vh,
    binds H i vh /\
    exists ts, (v, ts) \in vh /\
               (forall v' ts', (v', ts') \in vh -> ts' <= ts).

Lemma set_inv :
  forall A (E : set A),
    LibSet.finite E ->
    E = \{} \/ exists E' x, x \notin E' /\ E = \{x} \u E'.
Proof.
  introv Hfin.
  destruct* (classic (E = \{})).
  right. asserts (x & Hin): (exists x, x \in E).
  {
    forwards Hrepr: list_repr_to_list_of_finite Hfin.
    destruct (to_list E).
    - asserts: (E = \{}); substs*.
      rew_set. intros. splits; rew_set; autos.
      intros contra. apply Hrepr in contra.
      inverts contra.
    - exists a. apply* Hrepr.
  }
  exists (E \-- x) x. splits.
  - intros y. rew_set in y. inverts* y.
  - apply* eq_union_single_remove_one.
Qed.

Lemma set_ind :
  forall A E,
    LibSet.finite E ->
    forall (P : set A -> Prop),
      P \{} ->
      (forall E' e, e \notin E' -> P E' -> P (\{e} \u E')) ->
      P E.
Proof.
  introv Hfin Hempty Hih.
  forwards (L & Hrepr & _): finite_inv_list_repr_and_card Hfin.
  clear Hfin.
  gen E.
  induction L; intros.
  - asserts: (E = \{}); substs~.
    rew_set. intros. splits; rew_set; autos.
    intros contra. apply Hrepr in contra.
    inverts contra.
  - asserts (E' & Hnin & Hrepr' & ->): (exists E', list_repr E' L /\ a \notin E' /\ E = \{a} \u E').
    {
      exists (E \-- a). splits.
      - destruct Hrepr as (Hndup & Hiff).
        rew_listx in Hndup.
        splits~.
        intros x. splits.
        + introv Hmem.
          asserts Hmem': (mem x (a :: L)).
          { rew_listx~. }
          apply Hiff in Hmem'.
          asserts Hneq: (x <> a).
          { intros contra. subst*. }
          set_prove.
        + intros Hin.
          asserts Hneq: (x <> a).
          { intros contra. set_prove. }
          asserts Hin': (x \in E).
          { set_prove. }
          apply Hiff in Hin'.
          inverts~ Hin'.
      - intros contra. set_prove.
      - rewrite~ <- eq_union_single_remove_one.
        apply~ Hrepr.
    }
    apply~ Hih.
Qed.

Lemma set_ind' :
  forall A E,
    LibSet.finite E ->
    forall (P : set A -> Prop),
      P \{} ->
      (forall E' e, P E' -> P (\{e} \u E')) ->
      P E.
Proof.
  introv Hfin Hempty Hih.
  forwards (L & Hrepr & _): finite_inv_list_repr_and_card Hfin.
  clear Hfin.
  gen E.
  induction L; intros.
  - asserts: (E = \{}); substs~.
    rew_set. intros. splits; rew_set; autos.
    intros contra. apply Hrepr in contra.
    inverts contra.
  - asserts (E' & Hrepr' & ->): (exists E', list_repr E' L /\ E = \{a} \u E').
    {
      exists (E \-- a). splits.
      - destruct Hrepr as (Hndup & Hiff).
        rew_listx in Hndup.
        splits~.
        intros x. splits.
        + introv Hmem.
          asserts Hmem': (mem x (a :: L)).
          { rew_listx~. }
          apply Hiff in Hmem'.
          asserts Hneq: (x <> a).
          { intros contra. subst*. }
          set_prove.
        + intros Hin.
          asserts Hneq: (x <> a).
          { intros contra. set_prove. }
          asserts Hin': (x \in E).
          { set_prove. }
          apply Hiff in Hin'.
          inverts~ Hin'.
      - rewrite~ <- eq_union_single_remove_one.
        apply~ Hrepr.
    }
    apply~ Hih.
Qed.

(* TODO: connect to is_latest_value *)
Lemma ex_latest :
  forall (vh : version_history),
    LibSet.finite vh ->
    vh <> \{} ->
    exists v ts,
      (v, ts) \in vh /\
        (forall v' ts', (v', ts') \in vh -> ts' <= ts).
Proof.
  introv Hfin.
  pattern vh.
  apply~ set_ind.
  intros vh' (v & ts) Hnin IH _.
  destruct (classic (vh' = \{})).
  - substs. exists v ts. split; [set_prove|].
    introv Hin. rew_set in Hin. branches; autos.
    inverts* H.
  - forwards~ (v' & ts' & Hin & Hle): IH.
    asserts Hneq: ((v, ts) <> (v', ts')).
    { introv contra. inverts* contra. }
    destruct (classic (ts' <= ts)).
    + exists v, ts. splits; [set_prove|].
      introv Hin'. rew_set in Hin'. branches.
      * inverts* H1.
      * forwards* Hle': Hle H1.
    + exists v', ts'. splits; [set_prove|].
      introv Hin'.
      rew_set in Hin'. branches; autos*.
      inverts* H1.
Qed.

Lemma ex_latest' :
  forall (vh : version_history),
    LibSet.finite vh ->
    vh <> \{} ->
    exists v ts,
      (v, ts) \in vh /\
        (forall v' ts', (v', ts') \in vh -> ts' <= ts).
Proof.
  introv Hfin.
  pattern vh.
  apply~ set_ind'.
  intros vh' (v & ts) IH _.
  destruct (classic (vh' = \{})).
  - substs. exists v ts. split; [set_prove|].
    introv Hin. rew_set in Hin. branches; autos.
    inverts* H.
  - forwards~ (v' & ts' & Hin & Hle): IH.
    destruct (classic ((v, ts) = (v', ts'))).
    + inverts H0. exists v', ts'. splits; [set_prove|].
      introv Hin'. rew_set in Hin'. branches; autos*.
      inverts* H0.
    + destruct (classic (ts' <= ts)).
      * exists v, ts. splits; [set_prove|].
        introv Hin'. rew_set in Hin'. branches.
        -- inverts* H2.
        -- forwards*: Hle.
      * exists v', ts'. splits; [set_prove|].
        introv Hin'.
        rew_set in Hin'. branches; autos*.
        inverts* H2.
Qed.

Definition is_max_timestamp (H : heap) (ts : timestamp) :=
  (* ts is used somewhere *)
  (exists i vh,
      binds H i vh /\
      exists v, (v, ts) \in vh)
  /\
  (* ts is maximum timestamp *)
  (forall i vh v ts',
      binds H i vh ->
      (v, ts') \in vh ->
      ts' <= ts).

Lemma ninhab_empty :
  forall A B (M : map A B),
    ~Inhab B ->
    M = \{}.
Proof.
  introv Hninhab.
  apply eq_empty_of_not_binds.
  introv Hnbinds.
  apply Hninhab.
  constructor. exists* k.
Qed.

Lemma map_ind :
  forall A B M,
    finite M ->
    forall (P : map A B -> Prop),
      P \{} ->
      (forall M' k v, P M' -> P M'[k:=v]) ->
      P M.
Proof.
  introv Hfin Hempty Hih.
  asserts~ Hfin': (LibSet.finite (dom M)).
  forwards (L & Hrepr & _): finite_inv_list_repr_and_card Hfin'.
  clear Hfin Hfin'.
  destruct (classic (~Inhab B)) as [|Hinhab].
  { forwards* ->: ninhab_empty. }
  rew_logic in Hinhab.
  gen M.
  induction L; intros.
  - asserts: (M = \{}); substs~.
    apply dom_empty_inv. rew_set.
    intros. splits; rew_set; autos.
    intros contra. apply Hrepr in contra.
    inverts contra.
  - asserts Hin: (a \indom M).
    { apply* Hrepr. }
    asserts (v & Hbinds): (exists v, binds M a v).
    {
      exists M[a]. rewrite binds_eq_indom_read with (H := Hinhab).
      splits*.
    }
    asserts (M' & Hrepr' & ->): (exists M', list_repr (dom M') L /\ M = M'[a:=v]).
    {
      exists (M \-- a). splits.
      - destruct Hrepr as (Hndup & Hiff).
        rew_listx in Hndup.
        splits~.
        intros x. splits.
        + introv Hmem.
          asserts Hmem': (mem x (a :: L)).
          { rew_listx~. }
          apply Hiff in Hmem'.
          asserts Hneq: (x <> a).
          { intros contra. subst*. }
          rewrite dom_remove_one. set_prove.
        + rewrite dom_remove_one. intros Hin'.
          asserts Hneq: (x <> a).
          { intros contra. set_prove. }
          asserts Hin'': (x \indom M).
          { set_prove. }
          apply Hiff in Hin''.
          inverts~ Hin''.
      - apply eq_union_restrict_remove_one with (H := Hinhab) in Hin.
        rewrite~ update_eq_union_single.
        rewrite binds_eq_indom_read with (H := Hinhab) in Hbinds.
        unpack.
        subst*.
    }
    apply~ Hih.
Qed.

Lemma max_timestamp_exists :
  forall H,
    finite H ->
    (exists i vh, binds H i vh /\ vh <> \{}) ->
    exists ts, is_max_timestamp H ts.
Proof.
  introv Hfin.
  pattern H.
  apply~ map_ind.
  - introv (i & vh & Hbinds & Hneq).
    inverts Hbinds.
  - introv IH (i & vh & Hbinds & Hneq).
    rename v into vh'.
    destruct (classic ((exists (i : loc) (vh : version_history), binds M' i vh /\ vh <> \{}))).
    + forwards~ (ts & Hmax): IH.
      apply binds_update_inv in Hbinds.
      case_if.
      * substs. admit.
      * admit.
    + rew_logic in H0.
      forwards Hnex: H0 i.
      rew_logic in Hnex.
      forwards Hndisj: Hnex vh.
      rew_logic in Hndisj. branches;[|congruence].

      admit.
Admitted.

Definition push_staged (h : staging_area) (ts : timestamp) (H : heap): heap :=
  fun i => match h i with
           | None => H i
           | Some v =>
               match H i with
               | None => Some \{(v, ts)}
               | Some vh => Some (vh \u \{(v, ts)})
               end
           end.

Definition locks := SharedMemory.locks.

Definition conflict_free (h : staging_area) (ts : timestamp) (H : heap) :=
  forall i h',
    i \indom h ->
    binds H i h' ->
    (forall v' ts', (v', ts') \in h' -> ts' <= ts).

Definition cfg := (threads * heap * locks)%type.

Inductive push (t : tid) : cfg -> cfg -> Prop :=
| Push : forall T H L st e h ts ts',
    binds T t (st, e, h, ts) ->
    conflict_free h ts H ->
    is_max_timestamp H ts' ->
    push t (T, H, L) (T[t := (st, e, empty, S ts')], push_staged h (S ts') H, L)
.

Inductive pull (t : tid) : cfg -> cfg -> Prop :=
| Pull : forall T H L st e h ts ts',
    binds T t (st, e, h, ts) ->
    conflict_free h ts H ->
    is_max_timestamp H ts' ->
    pull t (T, H, L) (T[t := (st, e, h, ts')], H, L)
.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T T' H L L' t e h ts,
    binds T t (state_new, e, empty, 0) ->
    pull t (T, H, L) (T', H, L') ->
    binds T' t (state_new, e, h, ts) ->
    step (T, H, L) (T'[t := (state_running, e, h, ts)], H, L)
| StepEnd : forall T T' H H' L t r h ts ts',
    binds T t (state_running, te_ret r, h, ts) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_ret r, empty, ts') ->
    step (T, H, L) (T[t := (state_terminated, te_ret r, empty, ts')], H, L)
| StepReadLocal : forall T H L t e h ts K i v,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    binds h i v ->
    step (T, H, L) (T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L)
| StepReadGlobal : forall T H L t e h ts K i v,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    i \notindom h ->
    is_latest_value H i v ->
    step (T, H, L) (T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L)
| StepWrite : forall T H L t e h ts K i v,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_write i v) ->
    step (T, H, L) (T[t := (state_running, te_exp (K void), h[i := v], ts)], H, L)
| StepSpawn : forall T T' H H' L t (t' : tid) e h ts ts' K e',
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_spawn e') ->
    push t (T, H, L) (T', H', L) ->
    t' \notindom T' ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step (T, H, L) (T[t := (state_running, te_exp (K t'), empty, ts')][t' := (state_new, te_exp e', empty, 0)], H', L)
| StepJoin : forall T T' H L t t' e h h' ts ts' ts'' K r,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, h', ts') ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts'') ->
    step (T, H, L) (T[t := (state_running, te_exp (K r), h, ts'')], H, L)
| StepLock : forall T T' H L t e h ts ts' K l,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts') ->
    step (T, H, L) (T[t := (state_running, te_exp (K void), h, ts')], H, L[l := ls_held t])
| StepRelease : forall T T' H H' (L : locks) t e h ts ts' K l,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step (T, H, L) (T[t := (state_running, te_exp (K void), empty, ts')], H', L[l := ls_free])
.

End Linear.

Module LoggingLinear.

Import Linear.
Import Log.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, H, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log) <-> exists e h ts, binds T t2 (state_new, e, h, ts))
      /\
      (* Ended threads are ended *)
      (forall t,
          mem (event_end t) log <-> exists e h ts, binds T t ((state_terminated, e, h, ts)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e h ts, binds T t (state_running, e, h, ts))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> binds L l (ls_held t))
      /\
      (* Unlocked locks are unlocked or untouched *)
      (forall l,
          (log = nil \/ exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l) <-> binds L l ls_free)
      /\
      (* TODO: Each location in the heap consists of pushed values *)
      (* TODO: Do we need timestamps in the events or can we reconstruct them? We should probably define play_event like for branching and "run it backwards" to see what the latest value is *)
      True
      /\
      (* TODO: Each staging area contains unpushed writes *)
      True
  end.

(* TODO: Do we need something about timestamps? *)

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T T' H L L' t e h ts log,
    binds T t (state_new, e, empty, 0) ->
    pull t (T, H, L) (T', H, L') ->
    binds T' t (state_new, e, h, ts) ->
    step ((T, H, L), log) ((T'[t := (state_running, e, h, ts)], H, L), log & event_start t)
| StepEnd : forall T T' H H' L t r h ts ts' log,
    binds T t (state_running, te_ret r, h, ts) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_ret r, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_terminated, te_ret r, empty, ts')], H, L), log & event_end t)
| StepReadLocal : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    binds h i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L), log & event_read t i v)
| StepReadGlobal : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_read i) ->
    i \notindom h ->
    is_latest_value H i v ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), h, ts)], H, L), log & event_read t i v)
| StepWrite : forall T H L t e h ts K i v log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_write i v) ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), h[i := v], ts)], H, L), log & event_write t i v)
| StepSpawn : forall T T' H H' L t (t' : tid) e h ts ts' K e' log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_spawn e') ->
    push t (T, H, L) (T', H', L) ->
    t' \notindom T' ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K t'), empty, ts')][t' := (state_new, te_exp e', empty, 0)], H', L), log & event_spawn t t')
| StepJoin : forall T T' H L t t' e h h' ts ts' ts'' K r log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, h', ts') ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts'') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K r), h, ts'')], H, L), log & event_join t t')
| StepLock : forall T T' H L t e h ts ts' K l log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_lock l) ->
    binds L l ls_free ->
    pull t (T, H, L) (T', H, L) ->
    binds T' t (state_running, te_exp e, h, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), h, ts')], H, L[l := ls_held t]), log & event_lock t l)
| StepRelease : forall T T' H H' (L : locks) t e h ts ts' K l log,
    binds T t (state_running, te_exp e, h, ts) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t) ->
    push t (T, H, L) (T', H', L) ->
    binds T' t (state_running, te_exp e, empty, ts') ->
    step ((T, H, L), log) ((T[t := (state_running, te_exp (K void), empty, ts')], H', L[l := ls_free]), log & event_unlock t l)
.

Hint Constructors step Linear.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Linear.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepReadLocal.
    + exists. applys* StepReadGlobal.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Admitted.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Admitted.

End LoggingLinear.

Module LinearEquiv.

Import Log.

Definition same_expressions (cfgSh : SharedMemory.cfg) (cfgL : Linear.cfg) :=
  match cfgSh, cfgL with
  | (TSh, _, _), (TL, _, _) =>
      forall t st e,
        binds TSh t (st, e) <-> exists h ts, binds TL t (st, e, h, ts)
  end.

Theorem linear_equiv :
  forall log log' cfgSh cfgL,
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingLinear.describes log cfgL ->
    same_expressions cfgSh cfgL ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgL', LoggingLinear.step (cfgL, log) (cfgL', log')).
Proof.
  introv Hwf HdescSh HdescL Hexp Hcf.
  splits.
  - introv (cfgSh' & Hstep).
    destruct cfgL as [(T & H) L].
    inverts Hstep.
    + apply Hexp in H2 as (h & ts & Hbinds).
      exists. applys_eq (LoggingLinear.StepStart).
      * admit. (* new threads have empty staging areas and timestamp 0 *)
      * constructors*.
        -- admit. (* conflict free log means a conflict free heap *)
        -- admit. (* New timestamp is the maximum one (would be
           easier if we could just calculate it...) *)
      * apply binds_update_same.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - introv (cfgL' & Hstep).
    destruct cfgSh as ((Tsh & H) & Lsh).
    inverts Hstep;
      try
      match goal with
      | H: binds ?T ?t (?st, ?e, ?h, ?ts) |- _ =>
          asserts Hex: (exists h ts, binds T t (st, e, h, ts));
          [exists h; exists ts; exact H|];
          apply Hexp in Hex as Hbinds; clear Hex
      end.
    + admit. (* same_expressions_pull *)
    + exists. constructors*.
    + exists. constructors*.
      admit. (* binds H i v from local read *)
    + exists. constructors*.
      admit. (* binds H i v from global read *)
    + exists. constructors*.
    + admit. (* same_expressions_push *)
    + asserts* Hex: (exists h ts, binds T t (state_running, te_exp e, h, ts)).
      apply Hexp in Hex.
      exists. constructors*.
    + exists. constructors*.
      admit. (* Correspondence between locks via log *)
    + exists. constructors*.
      admit. (* Correspondence between locks via log *)
Admitted.

End LinearEquiv.

Module Branching.

Definition commit := nat.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition staging_area := map loc val.

Definition thread := (thread_state * thread_exp * staging_area * commit)%type.

Definition threads := map tid thread.

(* TODO: unify staging_areas to something more general *)
Definition commit_data := map commit staging_area.

Definition commit_rels := set (commit * commit).

Instance commit_rels_in_inst : BagIn (commit * commit) commit_rels.
  apply LibSet.in_inst.
Defined.

Definition graph : Type := commit_data * commit_rels.

Definition get_data (G : graph) (h : commit) :=
  match G with
  | (C, _) => C h
  end.

Definition commit_fresh (G : graph) (h : commit) :=
  match G with
  | (C, _) => h \notindom C
  end.

Definition locks := map lid (lock_state * commit).

Definition cfg : Type := threads * graph * locks.

(* The paper defines it as a closure of a direct relation, but
only uses the closure so we define it as such *)
Inductive ancestor (G : graph) : commit -> commit -> Prop :=
| AncestorDirect : forall h1 h2,
    match G with
    | (_, P) => (h1, h2) \in P
    end ->
    ancestor G h1 h2
| AncestorRefl : forall h,
    (* TODO: Should we require c to be in P? *)
    ancestor G h h
| AncestorTrans : forall h1 h2 h3,
    ancestor G h1 h2 ->
    ancestor G h2 h3 ->
    ancestor G h1 h3
.

(* TODO: What is the relation between the data and ancestry? They
should correspond domain-wise *)
Definition wf_graph (G : graph) :=
  forall h1 h2,
    ancestor G h1 h2 ->
    ancestor G h2 h1 ->
    h1 = h2.

Definition conflict_free (G : graph) :=
  forall h h1 h2 d1 d2,
    ancestor G h1 h ->
    ancestor G h2 h ->
    get_data G h1 = Some d1 ->
    get_data G h2 = Some d2 ->
    ~dom d1 \# dom d2 ->
    ancestor G h1 h2 \/ ancestor G h2 h1
.


Inductive push_thread (t t' : tid) : cfg -> cfg -> Prop :=
| PushThread : forall T C P L e e' d h h' h_new,
    binds T t (state_running, e, d, h) ->
    binds T t' (state_new, e', empty, h') ->
    commit_fresh (C, P) h_new ->
    push_thread t t' (T, (C, P), L) (T[t := (state_running, e, empty, h_new)][t' := (state_new, e', empty, h_new)], (C[h_new := d], \{(h, h_new)} \u P), L)
.

Inductive push_lock (t : tid) (l : lid) : cfg -> cfg -> Prop :=
| PushLock : forall T C P L e d h h' h_new,
    binds T t (state_running, e, d, h) ->
    binds L l (ls_held t, h') ->
    commit_fresh (C, P) h_new ->
    push_lock t l (T, (C, P), L) (T[t := (state_running, e, empty, h_new)], (C[h_new := d], \{(h, h_new)} \u P), L[l := (ls_held t, h_new)]).

(* TODO: This needs looking at! Do we create two commits or use
the staging area (d) when checking conflict_free *)
Inductive pull_thread (t t' : tid) : cfg -> cfg -> Prop :=
| PullThread : forall T C P G' L e e' d h h' h'' h_new,
    binds T t (state_running, e, d, h) ->
    binds T t' (state_terminated, e', empty, h') ->
    commit_fresh (C, P) h'' ->
    commit_fresh (C, P) h_new ->
    G' = (C[h'':=d][h_new:=empty], \{(h, h'')} \u \{(h'', h_new)} \u \{(h', h_new)} \u P) ->
    conflict_free G' ->
    pull_thread t t' (T, (C, P), L) (T[t := (state_running, e, empty, h_new)][t' := (state_terminated, e', empty, h_new)], G', L)
.

(* TODO: This needs looking at! *)
Inductive pull_lock (t : tid) (l : lid) : cfg -> cfg -> Prop :=
| PullLock : forall T C P G' L e d h h' h'' h_new,
    binds T t (state_running, e, d, h) ->
    binds L l (ls_free, h') ->
    commit_fresh (C, P) h'' ->
    commit_fresh (C, P) h_new ->
    G' = (C[h'':=d][h_new:=empty], \{(h, h'')} \u \{(h'', h_new)} \u \{(h', h_new)} \u P) ->
    conflict_free G' ->
    pull_lock t l (T, (C, P), L) (T[t := (state_running, e, empty, h_new)], G', L[l := (ls_free, h_new)])
.

Definition is_latest_value (G : graph) (h : commit) (i : loc) (v : val) :=
  exists h',
    ancestor G h' h /\
    match G with
    | (C, _) =>
        exists d',
          binds C h' d' /\
          binds d' i v /\
          ~exists h'',
            h'' \indom C /\ h' <> h'' /\
            ancestor G h' h'' /\
            ancestor G h'' h /\
            exists d'', binds C h'' d'' /\ i \indom d''
    end.

Example latest_value_exact :
  forall C P h i v d,
    wf_graph (C, P) ->
    binds C h d ->
    binds d i v ->
    is_latest_value (C, P) h i v.
Proof.
  introv Hwf Hbinds Hbinds'.
  exists h. splits.
  - apply AncestorRefl.
  - exists d. splits*.
    introv (h'' & Hin & Hneq & Hanc & Hanc' & d'' & Hbinds'' & Hin').
    forwards* ->: Hwf Hanc Hanc'.
Qed.

Inductive step : cfg -> cfg -> Prop :=
| StepStart : forall T G L t e d h,
    binds T t (state_new, e, d, h) ->
    step (T, G, L) (T[t := (state_running, e, d, h)], G, L)
| StepEnd : forall T C P L t r d h h',
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh (C, P) h' ->
    step (T, (C, P), L) (T[t := (state_terminated, te_ret r, empty, h')], (C[h' := d], \{(h, h')} \u P), L)
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
| StepSpawn : forall T T' G G' L t (t' : tid) e d h K e',
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    push_thread t t' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)], G, L) (T', G', L) ->
    step (T, G, L) (T', G', L)
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    pull_thread t t' (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step (T, G, L) (T[t := (state_running, te_exp (K r), d, h'')], G', L)
| StepLock : forall T T' G G' L t e d h h' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    pull_lock t l (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h') ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), d, h')], G', L[l := (ls_held t, h')])
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h'') ->
    push_lock t l (T, G, L) (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h') ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), empty, h')], G', L'[l := (ls_free, h')])
.

End Branching.

Module LoggingBranching.

Import Branching.
Import Log.

Definition deltas := map tid staging_area.
Definition commits := map tid commit.
Definition lcommits := map lid commit.

Inductive play_event : event -> (deltas * commits * graph * lcommits) -> (deltas * commits * graph * lcommits) -> Prop :=
| PlayRead :
  forall D TC G LC t i v,
    play_event (event_read t i v) (D, TC, G, LC) (D, TC, G, LC)
| PlayWrite :
  forall D TC G LC t i v d,
    binds D t d ->
    play_event (event_write t i v) (D, TC, G, LC) (D[t := d[i := v]], TC, G, LC)
| PlayStart :
  forall D TC G LC t,
    play_event (event_start t) (D, TC, G, LC) (D, TC, G, LC)
| PlayEnd :
  forall D TC C P LC t c c' d,
    binds TC t c ->
    c' \notindom C ->
    binds D t d ->
    play_event (event_end t) (D, TC, (C, P), LC) (D[t := empty], TC[t := c'], (C[c' := d], \{(c, c')} \u P), LC)
| PlaySpawn :
  forall D TC C P LC t1 t2 c c' d,
    binds TC t1 c ->
    c' \notindom C ->
    binds D t1 d ->
    play_event (event_spawn t1 t2) (D, TC, (C, P), LC) (D[t1 := empty][t2 := empty], TC[t1 := c'][t2 := c'], (C[c' := d], \{(c, c')} \u P), LC)
| PlayJoin :
  forall D TC C P LC t1 t2 c1 c2 c',
    binds TC t1 c1 ->
    binds TC t2 c2 ->
    c' \notindom C ->
    play_event (event_join t1 t2) (D, TC, (C, P), LC) (D, TC[t1 := c'], (C[c' := empty], \{(c1, c')} \u \{(c2, c')} \u P), LC)
| PlayLock :
  forall D TC C P LC t l c1 c2 c',
    binds TC t c1 ->
    binds LC l c2 ->
    c' \notindom C ->
    play_event (event_lock t l) (D, TC, (C, P), LC) (D, TC[t := c'], (C[c' := empty], \{(c1, c')} \u \{(c2, c')} \u P), LC)
| PlayUnlock :
  forall D TC C P LC t l c c' d,
    binds TC t c ->
    c' \notindom C ->
    binds D t d ->
    play_event (event_unlock t l) (D, TC, (C, P), LC) (D[t := empty], TC[t := c'], (C[c' := d], \{(c, c')} \u P), LC[l := c'])
.

Inductive play_log : log -> (deltas * commits * graph * lcommits) -> (deltas * commits * graph * lcommits) -> Prop :=
| PlayNil :
  forall D TC G LC,
    play_log nil (D, TC, G, LC) (D, TC, G, LC)
| PlaySnoc :
  forall E log D D' D'' TC TC' TC'' G G' G'' LC LC' LC'',
    play_log log (D, TC, G, LC) (D', TC', G', LC') ->
    play_event E (D', TC', G', LC') (D'', TC'', G'', LC'') ->
    play_log (log & E) (D, TC, G, LC) (D'', TC'', G'', LC'')
.

Definition is_sync_event (E : event) :=
  match E with
  | event_spawn t _
  | event_join t _
  | event_lock t _
  | event_unlock t _
  | event_start t
  | event_end t => True
  | _ => False
  end.

Fixpoint get_uncommitted' (t : tid) (l : log) (acc : log) :=
  match l with
  | nil => acc
  | E :: log' => get_uncommitted' t log' (If is_sync_event E then nil else acc & E)
  end.

Definition get_uncommitted (t : tid) (log : log) :=
  get_uncommitted' t log nil.

Lemma get_uncommitted'_has_sync :
  forall log t acc,
    Exists is_sync_event log ->
    get_uncommitted' t log acc = get_uncommitted' t log nil.
Proof.
  introv Hex.
  gen acc.
  induction Hex; intros; simpls; cases_if~.
Qed.

Lemma get_uncommitted'_no_sync :
  forall log t acc,
    ~Exists is_sync_event log ->
    get_uncommitted' t log acc = acc ++ log.
Proof.
  intros log.
  induction log; introv Hnex; simpls; rew_list~.
  cases_if~.
  - false Hnex. constructors*.
  - rew_listx in Hnex. rew_logic in Hnex. unpack.
    rewrite~ IHlog. rew_list~.
Qed.

Lemma get_uncommited_inv :
  forall log t,
    exists log', log = log' ++ get_uncommitted t log.
Proof.
  intros log t.
  unfolds get_uncommitted.
  induction log; simpls.
  - exists* (@nil event).
  - unpack. destruct (classic (Exists is_sync_event log0)).
    + rewrite~ get_uncommitted'_has_sync. exists (a :: log'). rew_list*.
    + cases_if.
      * rewrite~ get_uncommitted'_no_sync. exists (a :: nil). rew_list*.
      * rewrite~ get_uncommitted'_no_sync. exists (@nil event). rew_list*.
Qed.

Fixpoint find_write (log : log) (i : loc) : option val :=
  match log with
  | nil => None
  | event_write t j v :: log' =>
      match find_write log' i with
      | None => If i = j then Some v else None
      | Some v' => Some v'
      end
  | _ :: log' => find_write log' i
  end.

Lemma find_write_none :
  forall log i,
    LibList.filter (writes_location i) log = nil ->
    find_write log i = None.
Proof.
  introv Hfilter.
  induction~ log0.
  rew_listx in Hfilter.
  cases_if~.
  simpls. rewrite~ IHlog0.
  destruct~ a. cases_if*.
Qed.

Lemma find_write_writes_location :
  forall log log' i v t,
    LibList.filter (writes_location i) log = log' & event_write t i v ->
    find_write log i = Some v.
Proof.
  introv Hfilter.
  gen log'. induction log0; intros; simpls.
  - rew_listx in Hfilter. false. apply* nil_eq_last_inv.
  - rew_listx in Hfilter. cases_if.
    + destruct a; simpls*. destruct log'; rew_list in Hfilter.
      * inverts Hfilter. rewrite~ find_write_none. case_if*.
      * inverts Hfilter.
        rewrite* (IHlog0 log').
    + rewrite* (IHlog0 log').
      destruct* a.
Qed.

Lemma find_write_get_uncommitted :
  forall log t i v,
    find_write (get_uncommitted t log) i = Some v ->
    exists log' t, LibList.filter (writes_location i) log = log' & event_write t i v.
Proof.
  introv Hfind.
  induction log0; simpls*.
  (* TODO: probably need to prove something more general about get_uncommitted' *)
Admitted.

Definition describes (log : log) (cfg : cfg) : Prop :=
  match cfg with
  | (T, G, L) =>
      (* Spawned threads exist *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log) <-> t2 \indom T)
      /\
      (* Spawned threads that have not started are new *)
      (forall t2,
          (exists t1, mem (event_spawn t1 t2) log /\ ~mem (event_start t2) log) <-> exists e h ts, binds T t2 (state_new, e, h, ts))
      /\
      (* Ended threads are ended *)
      (forall t,
          mem (event_end t) log <-> exists e h ts, binds T t ((state_terminated, e, h, ts)))
      /\
      (* Started threads that are not ended are running *)
      (forall t,
          mem (event_start t) log /\ ~mem (event_end t) log <-> exists e d h, binds T t (state_running, e, d, h))
      /\
      (* Locked locks are locked *)
      (forall t l,
          (exists log', LibList.filter (fun e => touches_lock l e) log = log' & event_lock t l) <-> exists h, binds L l (ls_held t, h))
      /\
      (* Unlocked locks are unlocked (or untouched) *)
      (forall l,
          (log = nil \/ (exists t log', LibList.filter (fun e => touches_lock l e) log = log' & event_unlock t l)) <-> exists h, binds L l (ls_free, h))
      /\
      (* Replaying the log produces the commit graph, staging areas and lock/thread commits *)
      (exists D TC LC,
          play_log log (empty, empty, (empty, empty), empty) (D, TC, G, LC) /\
            (forall t, t \indom T -> exists ts e, binds T t (ts, e, D[t], TC[t])) /\
            (forall l, l \indom L -> exists ls, binds L l (ls, LC[l])))

(*      (* Deltas are uncommitted writes *)
      (forall t ts e d h,
          binds T t (ts, e, d, h) -> d = find_write (get_uncommitted t log)
      )*)
  end.

Inductive step : (cfg * log) -> (cfg * log) -> Prop :=
| StepStart : forall T G L t e d h log,
    binds T t (state_new, e, d, h) ->
    step ((T, G, L), log) ((T[t := (state_running, e, d, h)], G, L), log & event_start t)
| StepEnd : forall T C P L t r d h h' log,
    binds T t (state_running, te_ret r, d, h) ->
    commit_fresh (C, P) h' ->
    step ((T, (C, P), L), log) ((T[t := (state_terminated, te_ret r, empty, h')], (C[h' := d], \{(h, h')} \u P), L), log & event_end t)
| StepReadLocal : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    binds d i v ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L), log & event_read t i v)
| StepReadGlobal : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_read i) ->
    i \notindom d ->
    is_latest_value G h i v ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K (ret_val v)), d, h)], G, L), log & event_read t i v)
| StepWrite : forall T G L t e d h K i v log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_write i v) ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), d[i := v], h)], G, L), log & event_write t i v)
| StepSpawn : forall T T' G G' L t (t' : tid) e d h K e' log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_spawn e') ->
    t' \notindom T ->
    push_thread t t' (T[t := (state_running, te_exp (K t'), d, h)][t' := (state_new, te_exp e', empty, 0)], G, L) (T', G', L) ->
    step ((T, G, L), log) ((T', G', L), log & event_spawn t t')
| StepJoin : forall T T' G G' L t t' e d h h' h'' K r log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_join t') ->
    binds T t' (state_terminated, te_ret r, empty, h') ->
    pull_thread t t' (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h'') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K r), d, h'')], G', L), log & event_join t t')
| StepLock : forall T T' G G' L t e d h h' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    pull_lock t l (T, G, L) (T', G', L) ->
    binds T' t (state_running, te_exp e, d, h') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), d, h')], G', L[l := (ls_held t, h')]), log & event_lock t l)
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l log,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h'') ->
    push_lock t l (T, G, L) (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h') ->
    step ((T, G, L), log) ((T[t := (state_running, te_exp (K void), empty, h')], G', L'[l := (ls_free, h')]), log & event_unlock t l)
.

Hint Constructors step Branching.step : vcm.

Theorem step_equiv :
  forall cfg cfg' log,
    (exists log', step (cfg, log) (cfg', log')) <-> Branching.step cfg cfg'.
Proof.
  introv. split; introv Hstep.
  - destruct Hstep as (log' & Hstep). inverts* Hstep.
  - inverts* Hstep.
    + exists. applys* StepReadLocal.
    + exists. applys* StepReadGlobal.
    + exists. applys* StepSpawn.
    + exists. applys* StepJoin.
Qed.

Theorem step_preserves_wf_log :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    wf_log log'.
Admitted.

Theorem step_preserves_describes :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    describes log' cfg'.
Admitted.

End LoggingBranching.

Module BranchingEquiv.

Import Log.

Definition same_expressions (cfgSh : SharedMemory.cfg) (cfgB : Branching.cfg) :=
  match cfgSh, cfgB with
  | (TSh, _, _), (TB, _, _) =>
      forall t st e,
        binds TSh t (st, e) <-> exists d h, binds TB t (st, e, d, h)
  end.

Lemma same_expressions_same_domain :
  forall Tsh H Lsh TB G LG,
    same_expressions (Tsh, H, Lsh) (TB, G, LG) ->
    dom Tsh = dom TB.
Proof.
  introv Hexp.
  simpls. unfolds SharedMemory.threads, Branching.threads.
  do 2 rewrite dom_eq_set_of_binds.
  apply set_st_eq.
  intros t. splits.
  - introv ((st & e) & Hbinds).
    apply Hexp in Hbinds as (d & h & Hbinds').
    exists*.
  - introv ((((st & e) & d ) & h) & Hbinds).
    exists (st, e). apply* Hexp.
Qed.

Theorem branching_equiv :
  forall log log' cfgSh cfgB,
    wf_log log ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions cfgSh cfgB ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgB', LoggingBranching.step (cfgB, log) (cfgB', log')).
Proof.
  introv Hwf HdescSh HdescB Hexp Hcf.
  splits.
  - introv (cfgSh' & Hstep).
    destruct cfgB as [(T & G) L].
    inverts Hstep;
      match goal with
      | H: binds ?T ?t (?ts', ?e) |- _ =>
          apply Hexp in H as (d & h & Hbinds)
      end.
    + exists. constructors*.
    + destruct G as (C & P).
      asserts (h' & cheat): (exists h, Branching.commit_fresh (C, P) h). admit.
      exists. constructors*.
    + destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      apply Hwrite in H6. admit. (* Cases on whether it is a global or local read *)
    + exists. constructors*.
    + destruct G as (C & P).
      forwards* Heq: same_expressions_same_domain.
      rewrite Heq in H6.
      asserts (h' & cheat): (exists h, Branching.commit_fresh (C, P) h). admit.
      asserts* Hneq: (t <> t').
      exists. constructors*.
      applys_eq* Branching.PushThread.
      * apply* binds_update_neq.
        apply* binds_update_same.
      * apply* binds_update_same.
    + destruct G as (C & P).
      apply Hexp in H4 as (d' & h' & Hbinds').
      asserts cheat: (d = \{}). admit. (* terminated thread has an empty staging area. *)
      substs.
      exists. constructors*.
      admit. (* Revisit when pulling has been updated to match paper *)
    + exists. constructors*.
      admit. (* Correspondence between locks via log *)
      admit. (* Revisit when pulling has been updated to match paper *)
    + destruct G as (C & P).
      asserts (h' & cheat): (exists h, Branching.commit_fresh (C, P) h). admit.
      exists. constructors*.
      * admit. (* Correspondence between locks via log *)
      * applys_eq* Branching.PushLock.
        admit. (* Correspondence between locks via log *)
      * apply* binds_update_same.
  - introv (cfgB' & Hstep).
    destruct cfgSh as ((Tsh & H) & Lsh).
    inverts Hstep;
      try
      match goal with
      | H: binds ?T ?t (?ts, ?e, ?d, ?h) |- _ =>
          asserts Hex: (exists d h, binds T t (ts, e, d, h));
          [exists d; exists h; exact H|];
          apply Hexp in Hex as Hbinds; clear Hex
      end.
    + exists. constructors*.
    + exists. constructors*.
    + exists. constructors*.
(*      destruct HdescB as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite').
      forwards~: Hwrite H4.
      subst. apply Hwrite'.
      forwards~ aoeu: LoggingBranching.find_write_writes_location H6. *)
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & _ & _ & _ & (D & TC & LC & Hplay & Hdelta & Hlocks)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      (* i |-> v \in D[t] -> v is an uncommited write of t in the tail of the log *) admit.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & _ & _ & _ & (D & TC & LC & Hplay & Hdelta & Hlocks)).
      apply Hwrite.
      (* latest value is also latest value in commit graph *)
      admit. (* binds H i v from global read *)
    + exists. constructors*.
    + exists. constructors*.
      forwards* ->: same_expressions_same_domain.
    + asserts* Hex: (exists d h, binds T t' (state_terminated, te_ret r, d, h)).
      apply Hexp in Hex.
      exists. constructors*.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & HunlockedSh & _).
      destruct HdescB as (_ & _ & _ & _ & _ & HunlockedB & _).
      forwards Hiff: HunlockedSh l0.
      forwards Hiff': HunlockedB l0.
      apply Hiff. apply* Hiff'.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & HlockedSh & _ & _).
      destruct HdescB as (_ & _ & _ & _ & HunlockedB & _ & _).
      forwards* (t' & log' & Hiff): HlockedSh t l0.
      forwards* (t'' & log'' & Hiff'): HunlockedB t l0.
Admitted.

(* TODO: We currently model data races as stuck states. Regardless
of whether we add the exception rules, we will probably need a
lemma that says that a conflict-free log that describes a graph
implies a conflict-free graph. *)

(*
Lemma conflict_free_log_describes_conflict_free_graph :
  forall log G,
    conflict_free log ->
    describes log G ->
    conflict_free G. *)

End BranchingEquiv.
