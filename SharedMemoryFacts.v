From Vcm Require Import Common.
From Vcm Require Import SharedMemory.

Import SharedMemory.

(* A finite thread domain stays finite under a step: every rule either updates
   an existing thread in place (domain unchanged) or spawns exactly one new
   thread (adds a single element). *)
Lemma step_preserves_finite :
  forall T H L cfg',
    LibSet.finite (dom T) ->
    step (T, H, L) cfg' ->
    match cfg' with (T', _, _) => LibSet.finite (dom T') end.
Proof.
  introv Hfin Hstep.
  hint LibSet.finite_single.
  hint LibSet.finite_union.
  inverts Hstep; rew_dom; autos.
Qed.

(* A fresh thread id always exists, since the domain is a finite set of [nat]s.
   (Used to discharge the freshness side-condition of [StepSpawn] in progress.) *)
Lemma exists_fresh_tid :
  forall (T : threads),
    LibMap.finite T ->
    exists t', t' \notindom T.
Proof.
  introv Hfin.
  lets (l & Hcov): finite_inv_list_covers Hfin.
  exists (1 + fold_right plus 0 l).
  simpl.
  introv Hindom.
  forwards Hmem: Hcov Hindom.
  forwards Hle: mem_le_sum Hmem.
  nat_math.
Qed.

Lemma list_covers_forall :
  forall A (s : set A) l P,
    list_covers s l ->
    (forall x, mem x l -> P x) ->
    (forall_ x \in s, P x).
Proof.
  introv Hcovers Hall Hin.
  induction* l.
Qed.

(* Progress, modulo deadlock.

   Assuming (i) the thread domain is finite and (ii) progress for the underlying
   sequential language (with effect-enabledness folded in), every configuration
   is in exactly one of three situations: it is [done] (all threads have
   terminated), it is [deadlocked] (every thread is terminated or inert, and at
   least one is inert), or it can take one more [step].

   Proof sketch (by induction over the -- finite -- thread domain):
     - [state_new] threads can always [StepStart].
     - running [te_ret r] threads can always [StepEnd].
     - running [te_exp e] threads can [step_ul] (premise) to an enabled effect;
       reads/writes/spawns/unlocks then fire (reads hit [dom H], unlocks hold
       the lock, spawns use [exists_fresh_tid]); joins/locks fire unless blocked,
       in which case -- if *every* reduction is blocked -- the thread is inert.
     - [state_terminated] threads contribute to [done].
   If no thread can step, then there are no [new] threads and no running
   [te_ret] threads, every running [te_exp] thread is inert, hence the
   configuration is [done] (no inert threads) or [deadlocked] (some inert). *)
Theorem progress :
  forall T H L,
    finite T ->
    ul_progress (T, H, L) ->
    done (T, H, L)
    \/ deadlocked (T, H, L)
    \/ (exists cfg', step (T, H, L) cfg').
Proof.
  introv Hfin Hul.
  lets (l & Hcov): finite_inv_list_covers Hfin.

  induction l.
  - left.
    introv Hin. apply Hcov in Hin. forwards*: mem_nil_inv.
  -

Admitted.
