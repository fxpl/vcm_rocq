From Vcm Require Import Common.
From Vcm Require Import Log.

Lemma wf_log_read_last :
  forall lg t i v,
    mem (event_start t) lg ->
    ~mem (event_end t) lg ->
    wf_log lg ->
    wf_log (lg & event_read t i v).
Proof.
  introv Hstart Hend Hwf.
  destruct Hwf as (Hspawns & Hstarts & Hends & Hspawn & Hjoin & Hstart' & Hend' & Hlock & Hinit & Hrootsp).
  splits 10.
  - introv Heq (t1' & Hmem).
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_spawn t1 t2 :: l2' & e)
          with ((l1 ++ event_spawn t1 t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hspawns in Heq'.
      apply Heq'. exists t1'.
      rew_listx in Hmem.
      rew_listx.
      branches; auto_star.
  - introv Heq Hmem.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_start t0 :: l2' & e)
          with ((l1 ++ event_start t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hstarts in Heq'.
      apply Heq'.
      rew_listx in Hmem.
      rew_listx.
      branches; auto_star.
  - introv Heq Hmem.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_end t0 :: l2' & e)
          with ((l1 ++ event_end t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hends in Heq'.
      apply Heq'.
      rew_listx in Hmem.
      rew_listx.
      branches; auto_star.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_start t2 :: l2' & e)
          with ((l1 ++ event_start t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_join t1 t2 :: l2' & e)
          with ((l1 ++ event_join t1 t2 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq Hthread Hneq Hni.
    destruct (last_case l2) as [-> | (e' & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
      unpack. subst. simpls*.
    + replaces (l1 ++ e :: l2' & e')
          with ((l1 ++ e :: l2') & e')
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
  - introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + rew_listx*.
    + replaces (l1 ++ event_end t0 :: l2' & e)
          with ((l1 ++ event_end t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      rew_listx. splits*.
      asserts Hmem': (mem (event_end t0) lg).
      { subst. rew_listx*. }
      asserts* Hneq: (t <> t0).
      simpls*.
  - (* locks *) introv. rew_listx. cases_if*. rew_list*.
  - (* init *) introv Heq.
    destruct (last_case l2) as [-> | (e & l2' & ->)].
    + forwards*: last_eq_last_inv Heq.
    + replaces (l1 ++ event_init t0 :: l2' & e)
          with ((l1 ++ event_init t0 :: l2') & e)
            in Heq; [rew_list*|].
      forwards* (Heq' & <-): last_eq_last_inv Heq.
      apply Hinit in Heq'. exact Heq'.
  - (* root never spawned *) intros t1 Hmem. rew_listx in Hmem.
    destruct Hmem as [Hmem | Hmem]; (applys Hrootsp Hmem || inverts Hmem).
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
    destruct (last_case log) as [-> | (x & log'' & ->)]; autos.
    replaces (event_lock t1 l0 :: event_unlock t1 l0 :: log'' & x)
        with ((event_lock t1 l0 :: event_unlock t1 l0 :: log'') & x)
          in Heq.
    { rew_list~. }
    apply last_eq_last_inv in Heq as [_ ->].
    right. exists t' log''. rew_list~.
Qed.

(* The last entry of a lock's touch-filter is a lock or unlock of that lock. *)
Lemma filter_touches_lock_last_inv : forall l lg xs' x,
    LibList.filter (fun e => touches_lock l e) lg = xs' & x ->
    (exists t', x = event_lock t' l) \/ (exists t', x = event_unlock t' l).
Proof.
  introv Heq.
  asserts Hmem: (mem x (LibList.filter (fun e => touches_lock l e) lg)).
  { rewrite Heq. apply mem_last_r. }
  forwards (_ & Htl): mem_filter_inv Hmem.
  destruct x; simpls; try contradiction.
  - left. exists t. congruence.
  - right. exists t. congruence.
Qed.

(* Appending a lock event to a well-formed log keeps it well formed, given the
   acquiring thread is running and the lock's touch-filter is empty or ends in an
   unlock.  Both lock step rules (free and never-touched) produce the same log. *)
Lemma wf_log_snoc_lock : forall lg t l,
    wf_log lg ->
    mem (event_start t) lg ->
    ~ mem (event_end t) lg ->
    (LibList.filter (fun e => touches_lock l e) lg = nil \/
     exists t'' lg'', LibList.filter (fun e => touches_lock l e) lg = lg'' & event_unlock t'' l) ->
    wf_log (lg & event_lock t l).
Proof.
  introv Hwf Hsmem Hlnmem Hlfree.
  destruct Hwf as (Huspawn & Hustart & Huend & Hspawn & Hjoin & Hstart & Hend & Hlock & Hinit & Hrootsp).
  splits 10.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros (t1' & Hmem'). apply~ Huspawn. exists t1'.
    rew_listx. rew_listx in Hmem'. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Hustart l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    intros contra. apply~ (Huend l1 l2' t0).
    rew_listx. rew_listx in contra. branches; autos.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hspawn.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hjoin.
  + introv Heq <- Hneq Hninit.
    forwards [(Hmem' & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq.
    * inverts Hmem'. simpl. exact Hsmem.
    * apply~ Hstart.
  + introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    rew_listx. splits.
    * apply~ Hend.
    * simpl. intros ->. apply Hlnmem. rew_listx*.
  + (* locks *) introv. rew_listx.
    cases_if as Heql.
    * unfold touches_lock in Heql. subst. rew_list.
      apply wf_lock_log_snoc_lock.
      { apply~ Hlock. }
      { destruct Hlfree as [Hnil | (t'' & lg'' & Hfilt)].
        - left. exact Hnil.
        - right. exists t'' lg''. exact Hfilt. }
    * rew_list. apply~ Hlock.
  + (* init *) introv Heq.
    forwards [(contra & -> & ->) | (l2' & -> & ->)]: last_eq_middle_inv Heq; [false~|].
    apply* Hinit.
  + (* root never spawned *) intros t1 Hmem. rew_listx in Hmem.
    destruct Hmem as [Hmem | Hmem]; (applys Hrootsp Hmem || inverts Hmem).
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
    destruct (last_case log) as [-> | (y & log'' & ->)].
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
  forall lg e t2,
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) lg) <= 1 ->
    ~(exists t1 t2, e = event_spawn t1 t2) ->
    length (LibList.filter (fun e => exists t1, e = event_spawn t1 t2) (lg & e)) <= 1.
Proof.
  introv Hlen Hnex.
  induction lg; rew_listx in *.
  - cases_if~. rew_list~.
  - cases_if~. rew_list in *. cases_if~; rew_list in *; autos~.
    false Hnex. unpack. substs*.
Qed.

Lemma conflict_free_nil :
  conflict_free nil.
Proof.
  introv Hnth1 Hnth2 Hacc Hlt.
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
  forall lg e,
    conflict_free (lg & e) ->
    conflict_free lg.
Proof.
  introv Hcf.
  introv Hnth1 Hnth2 Hacc Hlt.
  hint Nth_app_l.
  asserts* Hnth1': (LibList.Nth m (lg & e) (event_write t1 x v1)).
  asserts* Hnth2': (LibList.Nth n (lg & e) e2).
  forwards* Hhb: Hcf Hnth1' Hnth2' Hacc.
  applys* hb_app_inv.
  applys* Nth_inbound.
Qed.

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
  forall lg m n,
    hb lg m n ->
    forall t em en,
      LibList.Nth m lg em ->
      get_thread em = t ->
      (forall p ep, m <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep) ->
      LibList.Nth n lg en ->
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
    asserts Hns': (forall p ep, mid <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep).
    { introv Hle HN Hg. forwards Hlt': hb_lt Hmk.
      apply Hns with (p := p); [ nat_math | exact HN | exact Hg ]. }
    applys IHkn Hek Hgek Hns' Hn.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lemmas relocated here from BranchingEquiv.v (organization pass).          *)
(* ---------------------------------------------------------------------- *)

(* Extending a "no commit event of [t] at index >= m" property by one event:
   it survives appending any event that is not a commit event of [t]. *)
Lemma no_commit_event_snoc :
  forall (lg : log) E m t,
    (forall p ep, m <= p -> LibList.Nth p lg ep -> get_thread ep = t -> ~ is_commit_event ep) ->
    (get_thread E = t -> ~ is_commit_event E) ->
    (forall p ep, m <= p -> LibList.Nth p (lg & E) ep -> get_thread ep = t -> ~ is_commit_event ep).
Proof.
  introv Hbase HE. introv Hle HN Hg.
  forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
  - applys* Hbase.
  - subst ep. applys* HE.
Qed.

(* Membership is preserved when an element is appended at the very end. *)
Lemma mem_app_snoc_r : forall (x E : event) l1 l2,
  mem x (l1 ++ l2) -> mem x (l1 ++ (l2 & E)).
Proof.
  introv H. rewrite mem_app_eq in *. rewrite mem_last_eq. tauto.
Qed.

(* Dropping the last element of a well-formed lock log keeps it well-formed. *)
Lemma wf_lock_log_drop_last :
  forall ll, wf_lock_log ll -> forall xs y, ll = xs & y -> wf_lock_log xs.
Proof.
  introv H. induction H as [ | t l | t1 l ll0 Hwf0 IH ]; introv Heq.
  - false. applys nil_eq_last_inv Heq.
  - assert (Hrw: event_lock t l :: nil = nil & event_lock t l) by (rew_list; reflexivity).
    rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs. constructor.
  - destruct (last_case ll0) as [Hnil | (z & ll' & Hsnoc)].
    + subst ll0.
      assert (Hrw: event_lock t1 l :: event_unlock t1 l :: nil
                 = (event_lock t1 l :: nil) & event_unlock t1 l) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs. constructor.
    + subst ll0.
      assert (Hrw: event_lock t1 l :: event_unlock t1 l :: (ll' & z)
                 = (event_lock t1 l :: event_unlock t1 l :: ll') & z) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs.
      apply WfLockUnlock. apply (IH ll' z). reflexivity.
Qed.

(* An unlock at the end of a well-formed lock log is preceded by the matching lock. *)
Lemma wf_lock_log_unlock_prev :
  forall ll, wf_lock_log ll ->
    forall xs t l, ll = xs & event_unlock t l ->
    exists pre, xs = pre & event_lock t l.
Proof.
  introv H. induction H as [ | t0 l0 | t1 l0 ll0 Hwf0 IH ]; introv Heq.
  - false. applys nil_eq_last_inv Heq.
  - assert (Hrw: event_lock t0 l0 :: nil = nil & event_lock t0 l0) by (rew_list; reflexivity).
    rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. discriminate Hy.
  - destruct (last_case ll0) as [Hnil | (z & ll' & Hsnoc)].
    + subst ll0.
      assert (Hrw: event_lock t1 l0 :: event_unlock t1 l0 :: nil
                 = (event_lock t1 l0 :: nil) & event_unlock t1 l0) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq.
      inverts Hy. subst xs. exists (@nil event). rew_list. reflexivity.
    + subst ll0.
      assert (Hrw: event_lock t1 l0 :: event_unlock t1 l0 :: (ll' & z)
                 = (event_lock t1 l0 :: event_unlock t1 l0 :: ll') & z) by (rew_list; reflexivity).
      rewrite Hrw in Heq. forwards (Hxs & Hy): last_eq_last_inv Heq. subst xs.
      forwards (pre & Hpre): (>> IH ll' t l).
      { rewrite Hy. reflexivity. }
      exists (event_lock t1 l0 :: event_unlock t1 l0 :: pre). rewrite Hpre. rew_list. reflexivity.
Qed.

(* wf_log is preserved by dropping the last event. *)
Lemma wf_log_last_inv :
  forall log E, wf_log (log & E) -> wf_log log.
Proof.
  introv Hwf. unfold wf_log in *.
  destruct Hwf as (Huspawn & Hustart & Huend & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & Hinit & Hrootsp).
  splits 10.
  - introv Heq. intros (t1' & Hm).
    forwards Hno: (>> Huspawn l1 (l2 & E) t1 t2).
    { rewrite Heq. rew_list. reflexivity. }
    apply Hno. exists t1'. applys mem_app_snoc_r. exact Hm.
  - introv Heq. intro Hm.
    forwards Hno: (>> Hustart l1 (l2 & E) t).
    { rewrite Heq. rew_list. reflexivity. }
    apply Hno. applys mem_app_snoc_r. exact Hm.
  - introv Heq. intro Hm.
    forwards Hno: (>> Huend l1 (l2 & E) t).
    { rewrite Heq. rew_list. reflexivity. }
    apply Hno. applys mem_app_snoc_r. exact Hm.
  - introv Heq.
    forwards Hex: (>> Hstartsp l1 (l2 & E) t2).
    { rewrite Heq. rew_list. reflexivity. }
    exact Hex.
  - introv Heq.
    forwards Hm: (>> Hjoinend l1 (l2 & E) t1 t2).
    { rewrite Heq. rew_list. reflexivity. }
    exact Hm.
  - introv Heq Hgt Hne Hni.
    forwards Hm: (>> Hstartby l1 (l2 & E) e t).
    { rewrite Heq. rew_list. reflexivity. } { exact Hgt. } { exact Hne. } { exact Hni. }
    exact Hm.
  - introv Heq.
    forwards HF: (>> Hendby l1 (l2 & E) t).
    { rewrite Heq. rew_list. reflexivity. }
    rewrite Forall_last_eq in HF. destruct HF as (HF & _). exact HF.
  - (* locks *) intro l.
    forwards Hwll: Hlock l.
    rewrite filter_last in Hwll.
    cases_if as Ht.
    + applys wf_lock_log_drop_last Hwll. rew_list. reflexivity.
    + rew_list in Hwll. exact Hwll.
  - (* init *) introv Heq.
    forwards Hr: (>> Hinit l1 (l2 & E) t).
    { rewrite Heq. rew_list. reflexivity. }
    exact Hr.
  - (* root never spawned *) intros t1 Hmem.
    apply (Hrootsp t1). rewrite mem_last_eq. auto.
Qed.

Lemma spawned_thread_no_prior_event :
  forall log t1 t2 m em,
    wf_log (log & event_spawn t1 t2) ->
    LibList.Nth m log em ->
    get_thread em <> t2.
Proof.
  introv Hwf HN.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  destruct Hwf as (Huspawn & Hustart & Huend & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & Hinit & Hrootsp).
  intro Hgt.
  assert (Hmemstart: mem (event_start t2) log).
  { destruct (classic (em = event_start t2)) as [Hes | Hes].
    - rewrite <- Hes. exact Hmem.
    - assert (Heq2: log & event_spawn t1 t2 = l1 ++ em :: (l2 & event_spawn t1 t2))
        by (rewrite Heq; rew_list; reflexivity).
      forwards Hms: (>> Hstartby l1 (l2 & event_spawn t1 t2) em t2).
      { exact Heq2. } { exact Hgt. } { exact Hes. }
      { (* em <> event_init t2: else t2 = t_root, but t2 is spawned *)
        intro Hci. subst em.
        forwards (Het & _): Hinit Heq2.
        apply (Hrootsp t1). rewrite Het. apply mem_last_r. }
      rewrite Heq. rewrite mem_app_eq. left. exact Hms. }
  forwards (a & b & Heqs): mem_inv_middle Hmemstart.
  assert (Heq3: log & event_spawn t1 t2 = a ++ event_start t2 :: (b & event_spawn t1 t2))
    by (rewrite Heqs; rew_list; reflexivity).
  forwards [(tsp & Hmemsp) | Hminit]: Hstartsp Heq3.
  - (* start preceded by a spawn: contradicts unique spawn *)
    assert (Heq4: log & event_spawn t1 t2 = log ++ event_spawn t1 t2 :: nil)
      by (rew_list; reflexivity).
    forwards Hnospawn: Huspawn Heq4.
    apply Hnospawn. exists tsp. rew_list.
    rewrite Heqs. rewrite mem_app_eq. left. exact Hmemsp.
  - (* start preceded by an init: t2 = t_root, but t2 is spawned *)
    assert (Hmi: mem (event_init t2) (log & event_spawn t1 t2)).
    { rewrite Heqs. rew_listx. tauto. }
    forwards (c & d & Heqc): mem_inv_middle Hmi.
    forwards (Het & _): Hinit Heqc.
    apply (Hrootsp t1). rewrite Het. apply mem_last_r.
Qed.

(* Any thread that has an init event is the root (from the init conjunct of
   [wf_log], here taken as a hypothesis to avoid re-destructing). *)
Lemma mem_init_root :
  forall lg t,
    (forall l1 l2 t', lg = l1 ++ event_init t' :: l2 -> t' = t_root /\ l1 = nil) ->
    mem (event_init t) lg ->
    t = t_root.
Proof.
  introv Hinit Hmem. forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  forwards (Het & _): Hinit Heq. exact Het.
Qed.

(* wf bookkeeping: an event appended after [t2] has ended is not [t2] acting nor
   a (re-)spawn of [t2]. (From "threads end by ending" + "unique spawns".) *)
Lemma event_after_end_snoc :
  forall log E m t2,
    wf_log (log & E) ->
    LibList.Nth m log (event_end t2) ->
    get_thread E <> t2 /\ (forall t1, E <> event_spawn t1 t2) /\ (E <> event_init t2).
Proof.
  introv Hwf HN.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  destruct Hwf as (Huspawn & Hustart & Huend & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & Hinit & Hrootsp).
  assert (Heq2: log & E = l1 ++ event_end t2 :: (l2 & E))
    by (rewrite Heq; rew_list; reflexivity).
  splits.
  - forwards HForall: Hendby Heq2.
    applys Forall_mem_inv HForall. rewrite mem_last_eq. right. reflexivity.
  - introv Heqsp.
    forwards Hmemstart: (>> Hstartby l1 (l2 & E) (event_end t2) t2).
    { exact Heq2. } { reflexivity. } { discriminate. } { discriminate. }
    forwards (a & b & Heql1): mem_inv_middle Hmemstart.
    assert (Heq3: log & E = a ++ event_start t2 :: (b ++ event_end t2 :: (l2 & E))).
    { rewrite Heq2. rewrite Heql1. rew_list. reflexivity. }
    forwards [(tsp & Hmemsp) | Hminit]: Hstartsp Heq3.
    + assert (Heq4: log & E = log ++ event_spawn t1 t2 :: nil)
        by (rewrite Heqsp; rew_list; reflexivity).
      forwards Hnospawn: Huspawn Heq4.
      apply Hnospawn. exists tsp. rew_list.
      rewrite Heq, Heql1. rewrite mem_app_eq. left. rewrite mem_app_eq. left. exact Hmemsp.
    + assert (Hmi: mem (event_init t2) (log & E)).
      { rewrite Heq3. rew_listx. tauto. }
      forwards ->: mem_init_root Hinit Hmi.
      apply (Hrootsp t1). rewrite Heqsp. apply mem_last_r.
  - intros contra.
    subst E.
    forwards* (Heq3 & Heq4): Hinit.
    subst. destruct l1; rew_list in Heq4; inverts Heq4.
Qed.

(* wf bookkeeping: before [t2] has started, no event is [t2] acting nor a
   re-spawn of [t2]. (From "threads start by starting" + "unique spawns".) *)
Lemma event_after_spawn_snoc :
  forall log E m t1 t2,
    wf_log (log & E) ->
    LibList.Nth m log (event_spawn t1 t2) ->
    ~ LibList.mem (event_start t2) (log & E) ->
    get_thread E <> t2 /\ (forall t1', E <> event_spawn t1' t2) /\ E <> event_init t2.
Proof.
  introv Hwf HN Hnstart.
  forwards Hmem: Nth_mem HN.
  forwards (l1 & l2 & Heq): mem_inv_middle Hmem.
  unfold wf_log in Hwf.
  destruct Hwf as (Huspawn & Hustart & Huend & Hstartsp & Hjoinend & Hstartby & Hendby & Hlock & Hinit & Hrootsp).
  splits.
  - intro Hgt.
    destruct (classic (E = event_start t2)) as [HE | HE].
    + apply Hnstart. rewrite mem_last_eq. right. rewrite HE. reflexivity.
    + forwards Hms: (>> Hstartby log (@nil event) E t2).
      { rew_list. reflexivity. } { exact Hgt. } { exact HE. }
      { intro Hci.
        assert (Heqe: log & E = log ++ event_init t2 :: nil)
          by (rewrite Hci; rew_list; reflexivity).
        forwards (_ & Hnil): Hinit Heqe. rewrite Hnil in *. subst.
        forwards*: Nth_nil_inv.
      }
      apply Hnstart. rewrite mem_last_eq. left. exact Hms.
  - introv Heqsp.
    assert (Heq4: log & E = log ++ event_spawn t1' t2 :: nil)
      by (rewrite Heqsp; rew_list; reflexivity).
    forwards Hnospawn: Huspawn Heq4.
    apply Hnospawn. exists t1. rew_list.
    rewrite Heq. rewrite mem_app_eq. right. rewrite mem_cons_eq. left. reflexivity.
  - intros contra.
    subst E.
    forwards* (Heq3 & Heq4): Hinit.
    subst. destruct l1; rew_list in Heq4; inverts Heq4.
Qed.

(* wf bookkeeping: a thread's start event is unique. *)
Lemma start_not_in_prefix :
  forall log t2,
    wf_log (log & event_start t2) ->
    ~ LibList.mem (event_start t2) log.
Proof.
  introv Hwf. unfold wf_log in Hwf.
  destruct Hwf as (_ & Hustart & _).
  assert (Heq: log & event_start t2 = log ++ event_start t2 :: nil)
    by (rew_list; reflexivity).
  forwards Hns: Hustart Heq.
  rew_list in Hns. exact Hns.
Qed.

(* wf_lock_log bookkeeping (assumed): an unlock of [l] is immediately preceded, in
   the [l]-filter, by the matching [event_lock t l]. *)
Lemma unlock_prev_lock :
  forall log t l,
    wf_log (log & event_unlock t l) ->
    exists pre, LibList.filter (fun e => touches_lock l e) log = pre & event_lock t l.
Proof.
  introv Hwf. unfold wf_log in Hwf.
  destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hlock & _).
  forwards Hwll: Hlock l.
  rewrite filter_last in Hwll.
  cases_if as Ht.
  applys wf_lock_log_unlock_prev Hwll. rew_list. reflexivity.
Qed.

(* The last element of the i-write filter is the last i-write in the log, as a
   position with the maximality property. *)
Lemma last_write_position :
  forall log x lw tw vw,
    LibList.filter (fun e => writes_variable x e) log = lw & event_write tw x vw ->
    exists m, LibList.Nth m log (event_write tw x vw) /\
              (forall k tk vk, LibList.Nth k log (event_write tk x vk) -> k <= m).
Proof.
  induction log as [ | e log' IH ]; introv Hfilter.
  - rew_listx in Hfilter. false. applys nil_eq_last_inv Hfilter.
  - rew_listx in Hfilter. cases_if as HP.
    + (* writes_variable x e *)
      destruct (last_case (LibList.filter (fun e0 => writes_variable x e0) log'))
        as [Hnil | (x' & lw' & Hsnoc')].
      * (* no x-write in log': e is the last x-write, at index 0 *)
        rewrite Hnil in Hfilter.
        change (e :: nil) with (nil & e) in Hfilter.
        forwards (Hlweq & Hex): last_eq_last_inv Hfilter.
        exists 0. split.
        -- rewrite <- Hex. apply Nth_zero.
        -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
           ++ subst. nat_math.
           ++ exfalso.
              asserts Hmemf:
                (mem (event_write tk x vk) (LibList.filter (fun e0 => writes_variable x e0) log')).
              { applys mem_filter; [ applys Nth_mem HNmm | reflexivity ]. }
              rewrite Hnil in Hmemf. rewrite mem_nil_eq in Hmemf. exact Hmemf.
      * (* filter log' nonempty; its last element is event_write tw x vw *)
        asserts Hsnoc2:
          (LibList.filter (fun e0 => writes_variable x e0) log' = lw' & event_write tw x vw).
        { rewrite Hsnoc' in Hfilter.
          change (e :: (lw' & x')) with ((e :: lw') & x') in Hfilter.
          forwards (Hlweq & Hxeq): last_eq_last_inv Hfilter.
          rewrite Hsnoc'. rewrite Hxeq. reflexivity. }
        forwards (m' & HNm' & Hmax'): IH Hsnoc2.
        exists (S m'). split.
        -- apply Nth_succ. exact HNm'.
        -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
           ++ subst. nat_math.
           ++ forwards Hle: Hmax' HNmm. nat_math.
    + (* ~ writes_variable x e *)
      forwards (m' & HNm' & Hmax'): IH Hfilter.
      exists (S m'). split.
      -- apply Nth_succ. exact HNm'.
      -- introv HNk. forwards [(Hk0 & Hxe) | (mm & Hkm & HNmm)]: Nth_cons_inv HNk.
         ++ subst. exfalso. apply HP. reflexivity.
         ++ forwards Hle: Hmax' HNmm. nat_math.
Qed.

Example init_log_wf : wf_log init_log.
Proof.
  unfolds init_log. splits 10; rew_list.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
    rew_list in Heq. inverts* Heq.
    simpls. introv -> _ contra. autos.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - intros. rew_listx. cases_if. constructor.
  - introv Heq.
    forwards* (-> & Heq' & ->): single_eq_middle_inv Heq.
  - introv contra.
    inverts contra as Hmem.
    inverts Hmem.
Qed.
