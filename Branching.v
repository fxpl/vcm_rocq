From Vcm Require Import Common.

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

