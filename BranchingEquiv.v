From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import Branching.
From Vcm Require Import LoggingBranching.

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
      exists. constructors*. admit.
    + destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      apply Hwrite in H6. admit. (* Cases on whether it is a global or local read *)
    + exists. constructors*.
    + destruct G as (C & P).
      forwards* Heq: same_expressions_same_domain.
      rewrite Heq in H6.
      asserts (h' & cheat): (exists h, Branching.commit_fresh (C, P) h). admit.
      asserts* Hneq: (t <> t').
      exists. constructors*. admit.
    + destruct G as (C & P).
      apply Hexp in H4 as (d' & h' & Hbinds').
      asserts cheat: (d = \{}). admit. (* terminated thread has an empty staging area. *)
      substs.
      exists. constructors*.
      all: admit.
    + exists. constructors*.
      admit. (* Correspondence between locks via log *)
      all: admit.
    + destruct G as (C & P).
      asserts (h' & cheat): (exists h, Branching.commit_fresh (C, P) h). admit.
      exists. constructors*.
      * admit. (* Correspondence between locks via log *)
      * admit.
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

