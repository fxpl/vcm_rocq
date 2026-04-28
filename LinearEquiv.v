From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import Linear.
From Vcm Require Import LoggingLinear.

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

