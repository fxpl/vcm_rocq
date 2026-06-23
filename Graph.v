From Vcm Require Import Common.

Definition commit := nat.

Definition root_commit := 0.

Hint Unfold commit : vcm.
Hint Extern 1 => unfolds commit : vcm.

Definition staging_area := map loc val.

Definition empty_staging_area : staging_area := empty.

Instance inhab_staging_area : Inhab staging_area.
  constructor. exists empty_staging_area. tauto.
Qed.

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

Definition graph_edge (G : graph) (a b : commit) : Prop :=
  match G with
  | (_, P) => (a, b) \in P
  end.

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

Definition wf_graph (G : graph) :=
  (let '(C, _) := G in LibMap.finite C) /\
  (forall h1 h2,
    ancestor G h1 h2 ->
    ancestor G h2 h1 ->
    h1 = h2) /\
  (* Every commit appearing in the ancestry relation has data (possibly empty).
     This ties the ancestry component [P] to the data component [C]: a commit
     that is fresh in the data is genuinely new and cannot already be an edge
     endpoint. *)
  (forall a b, graph_edge G a b -> graph_indom G a /\ graph_indom G b).

Definition change_set (G : graph) (h1 h2 : commit) : set loc :=
  fun i =>
  match G with
  | (C, _) =>
      exists h,
        i \indom C[h] /\
        ancestor G h h2 /\ ~ancestor G h h1
  end.

Definition conflict_free_merge (d : staging_area) (h1 h2 : commit) (G : graph) :=
  (dom d \u change_set G h2 h1) \# (change_set G h1 h2).

Definition conflict_free_graph (G : graph) :=
  forall h1 h2,
    graph_indom G h1 ->
    graph_indom G h2 ->
    conflict_free_merge empty h1 h2 G.

(* Introduce an origin commit [h] with empty data and no incoming/outgoing edges.
   Used to bootstrap the root thread's commit when it is initialised. *)
Definition graph_root (G : graph) (h : commit) :=
  match G with
  | (C, P) => (C[h := empty], P)
  end
.

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


Definition graph_writes (G : graph) (c : commit) (i : loc) (v : val) : Prop :=
  exists d, graph_binds G c d /\ binds d i v.

(* The latest value of [i] visible at commit [h] is the value written by some
   commit [c] that is an ancestor of [h] and is *maximal* among the i-writing
   ancestors of [h] (no other i-writer sits strictly between [c] and [h]).
   The maximality clause is what makes this single-valued; dropping it (as the
   previous inductive formulation did) makes the relation multivalued at
   conflict-free "inherit vs. overwrite" merges. *)
Definition is_latest_value (G : graph) (h : commit) (i : loc) (v : val) : Prop :=
  exists c,
    graph_writes G c i v /\
    ancestor G c h /\
    (forall c' v',
       graph_writes G c' i v' ->
       ancestor G c c' ->
       ancestor G c' h ->
       c' = c).
