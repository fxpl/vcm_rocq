From Vcm Require Import Common.
From Vcm Require Import SharedMemory.

Definition timestamp := nat.

Hint Unfold timestamp : vcm.
Hint Extern 1 => unfolds timestamp : vcm.

Definition staging_area := map loc val.

Definition thread := (thread_state * thread_exp * staging_area * timestamp)%type.

Instance inhab_thread : Inhab thread.
  forwards* Hexp: inhab_exp.
  destruct Hexp as [[e _]].
  constructor. exists* (state_new, te_exp e, (empty : staging_area), (0 : timestamp)).
Qed.

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

Definition finite_histories (H : heap) :=
  forall i vh,
    binds H i vh ->
    LibSet.finite vh.

Lemma finite_histories_update_inv :
  forall H i vh,
    finite_histories (H[i := vh]) ->
    LibSet.finite vh.
Proof.
    introv Hfins.
    unfolds finite_histories.
    - asserts Hbinds: (binds H[i := vh] i vh).
      { apply* binds_update_same. }
      forwards*: Hfins.
Qed.

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
    finite_histories H ->
    (exists i vh, binds H i vh /\ vh <> \{}) ->
    exists ts, is_max_timestamp H ts.
Proof.
  introv Hfin.
  pattern H.
  apply~ map_ind.
  - introv Hfins (i & vh & Hbinds & Hneq).
    inverts Hbinds.
  - introv IH Hfins (i & vh & Hbinds & Hneq).
    rename v into vh'.
    simpl in Hfins.
    destruct (classic ((exists (i : loc) (vh : version_history), binds M' i vh /\ vh <> \{}))).
    + forwards~ (ts & Hmax): IH.
      forwards~ (v & ts' & Hin & Hle): ex_latest vh'.
      all: admit. (* Proof idea: ts is max of M'. There is some maximum timestamp of vh'. The maximum of M'[k:=vh'] is the maximum of ts and the maximum timestamp of vh'. *)
    + rew_logic in H0.
      forwards Hnex: H0 i.
      rew_logic in Hnex.
      forwards Hndisj: Hnex vh.
      rew_logic in Hndisj. branches;[|congruence].
      all: admit. (* Proof idea: by H0, there is no non-empty version history is M'. vh must be equal to vh'. vh is not empty, so there is some maximum timestamp of vh. *)
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

Lemma pull_preserves_thread_shape :
  forall t T H L T' H' L' t' st e h ts,
    pull t (T, H, L) (T', H', L') ->
    binds T t' (st, e, h, ts) ->
    exists h' ts', binds T' t' (st, e, h', ts').
Proof.
  introv Hpull Hbinds.
  inversion Hpull as [T0 H0 L0 st0 e0 h0 ts0 ts1 Hb0 Hcf Hmax]; subst.
  destruct (classic (t' = t)) as [->|Hneq].
  - assert (Heq : (st, e, h, ts) = (st0, e0, h0, ts0)).
    { eapply (binds_inj (H := inhab_thread)); eauto. }
    inverts Heq.
    exists h0 ts1.
    apply binds_update_same.
  - exists h ts.
    apply* binds_update_neq.
Qed.

Lemma push_preserves_thread_shape :
  forall t T H L T' H' L' t' st e h ts,
    push t (T, H, L) (T', H', L') ->
    binds T t' (st, e, h, ts) ->
    exists h' ts', binds T' t' (st, e, h', ts').
Proof.
  introv Hpush Hbinds.
  inversion Hpush as [T0 H0 L0 st0 e0 h0 ts0 ts1 Hb0 Hcf Hmax]; subst.
  destruct (classic (t' = t)) as [->|Hneq].
  - assert (Heq : (st, e, h, ts) = (st0, e0, h0, ts0)).
    { eapply (binds_inj (H := inhab_thread)); eauto. }
    inverts Heq.
    exists (empty : staging_area) (S ts1).
    apply binds_update_same.
  - exists h ts.
    apply* binds_update_neq.
Qed.

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

