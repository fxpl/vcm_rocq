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

(* TODO: What is the relation between the data and ancestry? They
should correspond domain-wise *)
Definition wf_graph (G : graph) :=
  (let '(C, _) := G in LibMap.finite C) /\
  forall h1 h2,
    ancestor G h1 h2 ->
    ancestor G h2 h1 ->
    h1 = h2.

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


Inductive is_latest_value (G : graph) (i : loc) (v : val) : commit -> Prop :=
| LatestDirect :
  forall h d,
    graph_binds G h d ->
    binds d i v ->
    is_latest_value G i v h
| LatestAncestor :
  forall h h' d,
    graph_binds G h d ->
    i \notindom d ->
    ancestor G h' h ->
    is_latest_value G i v h' ->
    is_latest_value G i v h
.

Lemma is_latest_value_graph_indom :
  forall G i v h,
    is_latest_value G i v h ->
    graph_indom G h.
Proof.
  introv Hval. inverts* Hval.
Qed.

Hint Resolve is_latest_value_graph_indom : vcm.

Lemma is_latest_value_inj :
  forall G i v1 v2 h,
    conflict_free_graph G ->
    is_latest_value G i v1 h ->
    is_latest_value G i v2 h ->
    v1 = v2.
Proof.
  introv Hcf Hval1 Hval2.
  induction Hval1; intros; inverts Hval2.
  - forwards*: graph_binds_inj G d d0.
  - forwards*: graph_binds_inj G d d0.
    subst. false*.
  - forwards*: graph_binds_inj G d d0.
    subst. false*.
  - forwards*: graph_binds_inj G d d0.
    subst.
    unfolds conflict_free_graph.
    asserts* Hdom1: (graph_indom G h').
    asserts* Hdom2: (graph_indom G h'0).
    forwards~ Hcfm: Hcf Hdom1 Hdom2.
    admit. (* Hey Claude, continue here please *)
Admitted.

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
    is_latest_value G i v h ->
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
