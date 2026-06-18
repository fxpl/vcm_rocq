From Vcm Require Import Common.

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

(*
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
| HbTrans: forall e1 e2 e3,
    (* Transitivity *)
    hb log e1 e2 ->
    hb log e2 e3 ->
    hb log e1 e3
.
*)

Inductive hb (log : log) : nat -> nat -> Prop :=
| HbPo : forall m n t e1 e2,
    (* Events are ordered within a thread *)
    LibList.Nth m log e1 ->
    LibList.Nth n log e2 ->
    get_thread e1 = t ->
    get_thread e2 = t ->
    m < n ->
    hb log m n
| HbLock : forall n m t1 t2 l,
    (* All lock events of a lock are ordered after preceding unlock events *)
    LibList.Nth m log (event_unlock t1 l) ->
    LibList.Nth n log (event_lock t2 l) ->
    m < n ->
    hb log m n
| HbSpawn : forall m n t1 t2,
    (* The spawn event of a thread is before its start event *)
    LibList.Nth m log (event_spawn t1 t2) ->
    LibList.Nth n log (event_start t2) ->
    m < n ->
    hb log m n
| HbJoin : forall m n t1 t2,
    (* The end event of a thread is before its join event(s) *)
    LibList.Nth m log (event_end t2) ->
    LibList.Nth n log (event_join t1 t2) ->
    m < n ->
    hb log m n
| HbTrans : forall m n k,
    (* Transitivity *)
    hb log m k ->
    hb log k n ->
    hb log m n
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

(*
Definition conflict_free (log : log) : Prop :=
  forall l1 l2 t1 t2 i v1 v2,
    log = l1 ++ l2 ->
    mem (event_write t1 i v1) l1 ->
    mem (event_write t2 i v2) l2 ->
    (* mem e l2 -> *)
    (* (e = event_write t2 i v2 \/ e = event_read t2 i v2) -> *)
    hb log (event_write t1 i v1) (event_write t2 i v2)
.
*)

Definition conflict_free (log : log) : Prop :=
  forall m n t1 t2 i v1 v2,
    LibList.Nth m log (event_write t1 i v1) ->
    LibList.Nth n log (event_write t2 i v2) ->
    m < n ->
    hb log m n
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

Lemma wf_lock_log_snoc_lock : forall xs t l,
    wf_lock_log xs ->
    (xs = nil \/ exists t' xs', xs = xs' & event_unlock t' l) ->
    wf_lock_log (xs & event_lock t l).
Proof.
  introv Hwf Hfree. induction Hwf.
  - rew_list. apply WfLockSingle.
  - destruct Hfree as [|( t' & xs' & Heq)]; [congruence|].
    destruct xs' as [| x [| y xs']]; rew_list in Heq; inverts Heq; congruence.
  - rew_list. apply WfLockUnlock.
    apply IHHwf.
    destruct Hfree as [Hnil | (t' & xs' & Heq)]; [congruence|].
    destruct (last_case log0) as [-> | (x & log'' & ->)]; autos.
    replaces (event_lock t1 l0 :: event_unlock t1 l0 :: log'' & x)
        with ((event_lock t1 l0 :: event_unlock t1 l0 :: log'') & x)
          in Heq.
    { rew_list~. }
    apply last_eq_last_inv in Heq as [_ ->].
    right. exists t' log''. rew_list~.
Qed.

Lemma wf_lock_log_snoc_unlock : forall xs xs' t l,
    wf_lock_log (LibList.filter (fun e : event => touches_lock l e) xs) ->
    LibList.filter (fun e : event => touches_lock l e) xs = xs' & event_lock t l ->
    wf_lock_log (LibList.filter (fun e : event => touches_lock l e) xs & event_unlock t l).
Proof.
  introv Hwf Heq. gen xs'. induction Hwf; intros.
  - destruct xs'; rew_listx in Heq; congruence.
  - destruct xs' as [| x [| y xs']]; rew_list in Heq; inverts Heq; try congruence.
    rew_list. apply WfLockUnlock. apply WfLockEmpty.
  - rew_list. apply WfLockUnlock.
    destruct (last_case log0) as [-> | (y & log'' & ->)].
    + replaces (event_lock t1 l0 :: event_unlock t1 l0 :: nil)
          with ((event_lock t1 l0 :: nil) & event_unlock t1 l0) in Heq.
      { rew_list~. }
      apply last_eq_last_inv in Heq as [_ Hcontra]. congruence.
    + replaces (event_lock t1 l0 :: event_unlock t1 l0 :: log'' & y)
          with ((event_lock t1 l0 :: event_unlock t1 l0 :: log'') & y) in Heq.
      { rew_list~. }
      apply last_eq_last_inv in Heq as [_ ->].
      apply (IHHwf log''). rew_list~.
Qed.

Lemma unique_spawn_snoc :
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

Lemma conflict_free_nil :
  conflict_free nil.
Proof.
  introv Hnth1 Hnth2 Hlt.
  inverts Hnth1.
Qed.

Lemma hb_lt :
  forall log m n,
    hb log m n ->
    m < n.
Proof.
  introv Hhb.
  induction* Hhb.
Qed.

Lemma hb_app_inv :
  forall l1 l2 m n,
    hb (l1 ++ l2) m n ->
    n < length l1 ->
    hb l1 m n.
Proof.
  introv Hhb Hlt.
  induction Hhb.
  - rew_listx in H1.
    forwards* Hdisj1: Nth_app_inv m.
    inverts Hdisj1; [| unpack; nat_math].
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbPo.
  - rew_listx in H1.
    forwards* Hdisj1: Nth_app_inv m.
    inverts Hdisj1; [| unpack; nat_math].
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbLock.
  - forwards* Hdisj1: Nth_app_inv m.
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj1; [| unpack; nat_math].
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbSpawn.
  - forwards* Hdisj1: Nth_app_inv m.
    forwards* Hdisj2: Nth_app_inv n.
    inverts Hdisj1; [| unpack; nat_math].
    inverts Hdisj2; [| unpack; nat_math].
    applys* HbJoin.
  - hint hb_lt.
    asserts* Hlt': (k < n).
    applys* HbTrans.
Qed.

Lemma conflict_free_last_inv :
  forall log e,
    conflict_free (log & e) ->
    conflict_free log.
Proof.
  introv Hcf.
  introv Hnth1 Hnth2 Hlt.
  hint Nth_app_l.
  asserts* Hnth1': (LibList.Nth m (log0 & e) (event_write t1 i v1)).
  asserts* Hnth2': (LibList.Nth n (log0 & e) (event_write t2 i v2)).
  forwards* Hhb: Hcf Hnth1' Hnth2'.
  applys* hb_app_inv.
  applys* Nth_inbound.
Qed.

(* The events that commit a thread's delta, making its local changes visible to
   other threads ("sync out"). These are exactly the source events of every
   cross-thread happens-before edge. *)
Definition is_commit_event (e : event) : Prop :=
  match e with
  | event_unlock _ _
  | event_spawn _ _
  | event_end _ => True
  | _ => False
  end.

(* The events that merge other threads' changes in without committing the
   thread's own delta. These keep the delta intact. *)
Definition is_merge_event (e : event) : Prop :=
  match e with
  | event_lock _ _
  | event_join _ _ => True
  | _ => False
  end.

Lemma hb_Nth_l :
  forall log m n,
    hb log m n ->
    exists e, LibList.Nth m log e.
Proof.
  introv Hhb. induction Hhb; eauto.
Qed.

Lemma hb_Nth_r :
  forall log m n,
    hb log m n ->
    exists e, LibList.Nth n log e.
Proof.
  introv Hhb. induction Hhb; eauto.
Qed.

(* If [m] is an event of thread [t] and [t] performs no [is_commit_event] event at
   any index [>= m], then every event [t] happens-before lies on thread [t].
   Reason: every cross-thread hb edge has an [is_commit_event] source, and a chain
   leaving [m] can only first cross threads via such a [t]-event at index [>= m]
   (all base edges strictly increase the index). *)
Lemma hb_preserves_thread :
  forall log m n,
    hb log m n ->
    forall t em en,
      LibList.Nth m log em ->
      get_thread em = t ->
      (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep) ->
      LibList.Nth n log en ->
      get_thread en = t.
Proof.
  introv Hhb.
  induction Hhb as
    [ m n th ea eb HNa HNb Hga Hgb Hlt
    | n m lt1 lt2 ll HNsrc HNtgt Hlt
    | m n st1 st2 HNsrc HNtgt Hlt
    | m n jt1 jt2 HNsrc HNtgt Hlt
    | m n mid Hmk IHmk Hkn IHkn ];
    introv Hm Hgt Hns Hn.
  - (* HbPo: same thread *)
    forwards Heqa: Nth_functional Hm HNa.
    forwards Heqb: Nth_functional Hn HNb.
    congruence.
  - (* HbLock: source [event_unlock lt1 ll] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_unlock lt1 ll)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbSpawn: source [event_spawn st1 st2] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_spawn st1 st2)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbJoin: source [event_end jt2] is a sync_out of t *)
    forwards Heq: Nth_functional Hm HNsrc. subst em.
    false (Hns m (event_end jt2)); [ nat_math | assumption | assumption | simpl; exact I ].
  - (* HbTrans: chain through the intermediate index [mid] *)
    forwards (ek & Hek): hb_Nth_r Hmk.
    forwards Hgek: IHmk Hm Hgt Hns Hek.
    asserts Hns': (forall p ep, mid <= p -> LibList.Nth p log0 ep -> get_thread ep = t -> ~ is_commit_event ep).
    { introv Hle HN Hg. forwards Hlt': hb_lt Hmk.
      apply Hns with (p := p); [ nat_math | exact HN | exact Hg ]. }
    applys IHkn Hek Hgek Hns' Hn.
Qed.
