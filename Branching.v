From Vcm Require Import Common.

Definition commit := nat.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition staging_area := map loc val.

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

Definition get_data (G : graph) (h : commit) :=
  match G with
  | (C, _) => C h
  end.

Definition commit_fresh (G : graph) (h : commit) :=
  match G with
  | (C, _) => h \notindom C
  end.

Definition locks := map lid (lock_state * commit).

Instance inhab_lock : Inhab (lock_state * commit).
  constructor. exists* (ls_free, 0).
Qed.

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

Definition change_set (G : graph) (h1 h2 : commit) : set loc :=
  fun i =>
  match G with
  | (C, _) =>
      exists h,
        match C h with
        | Some d =>
          i \indom d /\
          ancestor G h h2 /\ ~ancestor G h h1
        | None => False
        end
  end.

Definition conflict_free_merge (d : staging_area) (h1 h2 : commit) (G : graph) :=
  (dom d \u change_set G h2 h1) \# (change_set G h1 h2).

(*
(* Old definition *)
Definition conflict_free (G : graph) :=
  forall h h1 h2 d1 d2,
    ancestor G h1 h ->
    ancestor G h2 h ->
    get_data G h1 = Some d1 ->
    get_data G h2 = Some d2 ->
    ~dom d1 \# dom d2 ->
    ancestor G h1 h2 \/ ancestor G h2 h1
.
*)

Definition do_commit (t : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(C, P) := G in
  let '(_, e, d, h) := T[t] in
  (T[t := (state_running, e, empty, h_new)],
   (C[h_new := d], \{(h, h_new)} \u P)).
(*
Inductive push_thread (t t' : tid) : cfg -> cfg -> Prop :=
| PushThread : forall T C P L e e' d h h' h_new,
    binds T t (state_running, e, d, h) ->
    binds T t' (state_new, e', empty, h') ->
    commit_fresh (C, P) h_new ->
    push_thread t t' (T, (C, P), L) (T[t := (state_running, e, empty, h_new)][t' := (state_new, e', empty, h_new)], (C[h_new := d], \{(h, h_new)} \u P), L)
.

(* Currently we don't have requirements on thread state and staging areas like we do above *)
Definition do_push_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(C, P) := G in
  match T t, T t' with
  | Some (_, e, d, h), Some (_, e', _, _) =>
      (T[t := (state_running, e, empty, h_new)][t' := (state_new, e', empty, h_new)],
       (C[h_new := d], \{(h, h_new)} \u P))
  | _, _ => (T, G)
  end.
*)
Definition push_thread (t t' : tid) (h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(T', G') := do_commit t h_new T G in
  let '(ts, e, d, _) := T'[t'] in
  (T'[t' := (ts, e, d, h_new)], G').

(*
Inductive push_lock (t : tid) (l : lid) : cfg -> cfg -> Prop :=
| PushLock : forall T C P L e d h h' h_new,
    binds T t (state_running, e, d, h) ->
    binds L l (ls_held t, h') ->
    commit_fresh (C, P) h_new ->
    push_lock t l (T, (C, P), L) (T[t := (state_running, e, empty, h_new)], (C[h_new := d], \{(h, h_new)} \u P), L[l := (ls_held t, h_new)]).

(* Currently we don't have requirements on thread state like we do above *)
Definition do_push_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph * locks :=
  let '(C, P) := G in
  match T t with
  | Some (_, e, d, h) =>
      (T[t := (state_running, e, empty, h_new)],
       (C[h_new := d], \{(h, h_new)} \u P),
       L[l := (ls_held t, h_new)])
  | None => (T, G, L)
  end.
*)

Definition push_lock (t : tid) (l : lid) (h_new : commit)
    (T : threads) (G : graph) (L : locks)
    : threads * graph * locks :=
  let '(T', G') := do_commit t h_new T G in
  let '(ls, _) := L[l] in
  (T', G', L[l := (ls, h_new)]).

(*
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
*)

Definition do_merge (t : tid) (h h_new : commit)
    (T : threads) (G : graph)
    : threads * graph :=
  let '(C, P) := G in
  let '(ts, e, d, h_t) := T[t] in
  (T[t := (ts, e, empty, h_new)],
   (C[h_new := d], \{(h_t, h_new)} \u \{(h, h_new)} \u P)).

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

(*
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
*)

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
    is_latest_value G h i v ->
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
    step (T, G, L) (T[t := (state_running, te_exp (K r), d, h'')], G', L)
| StepLock : forall T T' G G' L t e d h h' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_lock l) ->
    binds L l (ls_free, h') ->
    conflict_free_merge d h h' G ->
    commit_fresh G h' ->
    pull_lock t l h' T G L = (T', G') ->
    binds T' t (state_running, te_exp e, d, h') ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), d, h')], G', L[l := (ls_held t, h')])
| StepRelease : forall T T' G G' (L L' : locks) t e d h h' h'' K l,
    binds T t (state_running, te_exp e, d, h) ->
    step_ul e K (eff_unlock l) ->
    binds L l (ls_held t, h'') ->
    commit_fresh G h' ->
    push_lock t l h' T G L = (T', G', L') ->
    binds T' t (state_running, te_exp e, empty, h') ->
    step (T, G, L) (T[t := (state_running, te_exp (K void), empty, h')], G', L'[l := (ls_free, h')])
.

