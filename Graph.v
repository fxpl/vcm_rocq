From Vcm Require Import Common.

Definition commit := nat.

Definition root_commit := 0.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition diff := map loc val.

Definition empty_diff : diff := empty.

Instance inhab_diff : Inhab diff.
  constructor. exists empty_diff. tauto.
Qed.

Definition commit_data := map commit diff.

Definition commit_rels := set (commit * commit).

Instance commit_rels_in_inst : BagIn (commit * commit) commit_rels.
  apply LibSet.in_inst.
Defined.

Definition graph : Type := commit_data * commit_rels.

Definition empty_graph : graph := (empty, empty).

Definition graph_indom (G : graph) (c : commit) :=
  match G with
  | (C, _) => c \indom C
  end.

Definition graph_binds (G : graph) (c : commit) (d : diff) :=
  match G with
  | (C, _) => binds C c d
  end.

Definition graph_edge (G : graph) (a b : commit) : Prop :=
  match G with
  | (_, P) => (a, b) \in P
  end.

Definition commit_fresh (G : graph) (c : commit) : Prop :=
  match G with
  | (C, _) => c \notindom C
  end.

Definition get_diff (G : graph) (c : commit) : diff :=
  match G with
  | (C, _) => C[c]
  end.

(* The paper defines it as a closure of a direct relation, but
only uses the closure so we define it as such *)
Inductive ancestor (G : graph) : commit -> commit -> Prop :=
| AncestorRefl : forall c,
    (* TODO: Should we require c to be in P? *)
    ancestor G c c
| AncestorTrans : forall c1 c2 c3,
    ancestor G c1 c2 ->
    match G with
    | (_, P) => (c2, c3) \in P
    end ->
    ancestor G c1 c3
.

Definition wf_graph (G : graph) :=
  (let '(C, _) := G in LibMap.finite C) /\
  (forall c1 c2,
    ancestor G c1 c2 ->
    ancestor G c2 c1 ->
    c1 = c2) /\
  (* Every commit appearing in the ancestry relation has data (possibly empty).
     This ties the ancestry component [P] to the data component [C]: a commit
     that is fresh in the data is genuinely new and cannot already be an edge
     endpoint. *)
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b).

Definition change_set (G : graph) (c1 c2 : commit) : set loc :=
  fun i =>
  match G with
  | (C, _) =>
      exists c,
        i \indom C[c] /\
        ancestor G c c2 /\ ~ancestor G c c1
  end.

Definition conflict_free_merge (d : diff) (c1 c2 : commit) (G : graph) :=
  (dom d \u change_set G c2 c1) \# (change_set G c1 c2).

Definition conflict_free_graph (G : graph) :=
  forall c1 c2,
    graph_indom G c1 ->
    graph_indom G c2 ->
    conflict_free_merge empty c1 c2 G.

(* Introduce an origin commit [c] with empty data and no incoming/outgoing edges.
   Used to bootstrap the root thread's commit when it is initialised. *)
Definition graph_root (G : graph) (c : commit) :=
  match G with
  | (C, P) => (C[c := empty], P)
  end
.

Definition graph_commit (G : graph) (c1 c2 : commit) (d : diff) :=
  match G with
  | (C, P) => (C[c2 := d], \{(c1, c2)} \u P)
  end
.

Definition graph_merge (G : graph) (c1 c2 c : commit) :=
  match G with
  | (C, P) => (C[c := empty], \{(c2, c)} \u \{(c1, c)} \u P)
  end
.


Definition graph_writes (G : graph) (c : commit) (i : loc) (v : val) : Prop :=
  exists d, graph_binds G c d /\ binds d i v.

(* The latest value of [i] visible at commit [c] is the value written by some
   commit [c] that is an ancestor of [c] and is *maximal* among the i-writing
   ancestors of [c] (no other i-writer sits strictly between [c] and [c]).
   The maximality clause is what makes this single-valued; dropping it (as the
   previous inductive formulation did) makes the relation multivalued at
   conflict-free "inherit vs. overwrite" merges. *)
Definition is_latest_value (G : graph) (c : commit) (i : loc) (v : val) : Prop :=
  exists c',
    graph_writes G c' i v /\
    ancestor G c' c /\
    (forall c'' v',
       graph_writes G c'' i v' ->
       ancestor G c' c'' ->
       ancestor G c'' c ->
       c'' = c').
