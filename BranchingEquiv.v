From Vcm Require Import Common.
From Vcm Require Import SharedMemory.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingSharedMemory.
From Vcm Require Import LoggingSharedMemoryFacts.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Branching.
From Vcm Require Import LoggingBranching.
From Vcm Require Import LoggingBranchingFacts.

Import Log.
Import LogFacts.

Definition same_expressions_and_locks (cfgSh : SharedMemory.cfg) (cfgB : Branching.cfg) :=
  match cfgSh, cfgB with
  | (TSh, _, LSh), (TB, _, LB) =>
      (forall t st e,
        binds TSh t (st, e) <-> exists d h, binds TB t (st, e, d, h)) /\
      (forall l ls, binds LSh l ls <-> exists h, binds LB l (ls, h))
  end.

Lemma same_expressions_same_domains :
  forall Tsh H Lsh TB G LB,
    same_expressions_and_locks (Tsh, H, Lsh) (TB, G, LB) ->
    dom Tsh = dom TB /\ dom Lsh = dom LB.
Proof.
  introv Hexp.
  simpls. unfolds SharedMemory.threads, Branching.threads,
          SharedMemory.locks, Branching.locks.
  repeat rewrite dom_eq_set_of_binds.
  splits.
  - apply set_st_eq.
    intros t. splits.
    + introv ((st & e) & Hbinds).
      apply Hexp in Hbinds as (d & h & Hbinds').
      exists*.
    + introv ((((st & e) & d ) & h) & Hbinds).
      exists (st, e). apply* Hexp.
  - apply set_st_eq.
    intros l. splits.
    + introv (ls & Hbinds).
      apply Hexp in Hbinds as (ls' & Hbinds').
      exists*.
    + introv ((ls & h) & Hbinds).
      exists ls. apply* Hexp.
Qed.

(* TODO: Should probably show preservation of same_expressions_and_locks as well *)
Theorem branching_equiv :
  forall log log' cfgSh cfgB,
    wf_log log ->
    match cfgB with
    | (_, G, _) => wf_graph G
    end ->
    LoggingSharedMemory.describes log cfgSh ->
    LoggingBranching.describes log cfgB ->
    same_expressions_and_locks cfgSh cfgB ->
    conflict_free log' ->
      (exists cfgSh', LoggingSharedMemory.step (cfgSh, log) (cfgSh', log')) <->
      (exists cfgB', LoggingBranching.step (cfgB, log) (cfgB', log')).
Proof.
  introv Hwf HwfG HdescSh HdescB Hsame Hcf.
  splits.
  - introv (cfgSh' & Hstep).
    destruct cfgB as [(T & G) L].
    forwards* HdescSh': LoggingSharedMemoryFacts.step_preserves_describes Hwf.
    inverts Hstep;
      match goal with
      | H: binds ?T ?t (?ts', ?e) |- _ =>
          assert (Ht := H);
          apply (proj1 Hsame) in H as (d & h & Hbinds)
      end.
    + exists. constructors*.
    + forwards (h' & Hfresh): exists_commit_fresh HwfG.
      asserts (T' & G' & Hcommit): (exists T' G', do_commit t h' T G = (T', G')).
      {
        exists. unfolds do_commit.
        forwards Hread: read_of_binds Hbinds.
        replace T[t] with (state_running, te_ret r, d, h).
        reflexivity.
      }
      exists. constructors*.
    + destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      apply Hwrite in H6 as (t' & log'0 & Hfilter).
      destruct HdescB as (_ & _ & _ & Hrun & _ & _ &
        (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2)).
      lets Htin: (indom_of_binds Hbinds).
      forwards (ts0 & e0 & Hbd): Hdelta Htin.
      forwards* Heqdt: binds_inj Hbinds Hbd. inverts Heqdt.
      forwards Hcflog: conflict_free_last_inv Hcf.
      destruct (classic (i \indom (D[t]))) as [Hin | Hnin].
      * (* local (uncommitted) read: [i] is in [t]'s delta *)
        asserts Hdt: (t \indom D). { applys HdomD Htin. }
        asserts Hbdi: (binds (D[t]) i (D[t][i])).
        { applys binds_of_indom_read Hin; (reflexivity || typeclass). }
        forwards (log'' & Hfilt2): conflict_free_last_local_write Hcflog Hplay Hdt Hbdi.
        rewrite Hfilter in Hfilt2.
        forwards (_ & Heqw): last_eq_last_inv Hfilt2. inverts Heqw.
        exists. applys StepReadLocal Hbinds; [ eassumption | exact Hbdi ].
      * (* global (committed) read: [i] is visible as the latest committed value *)
        forwards Hcfg: conflict_free_log_describes_conflict_free_graph Hwf Hcflog Hplay.
        lets [_ Hback]: Hrun t. forwards (Hms & Hmne): Hback. { do 3 eexists. exact Hbinds. }
        asserts Hwfr: (wf_log (log & event_read t i v)). { applys wf_log_read_last Hms Hmne Hwf. }
        destruct (last_write_position log i log'0 t' v Hfilter) as (mw & HNL & Hlast).
        forwards HLlt: Nth_inbound HNL.
        asserts Hplayf: (exists CHf,
          play_log (log & event_read t i v) (\{}, \{}, (\{}, \{}), \{}) (D, TC, G, LC) CHf).
        { eexists. applys PlaySnoc Hplay. apply PlayRead. }
        destruct Hplayf as (CHf & Hplayf).
        asserts HNLf: (LibList.Nth mw (log & event_read t i v) (event_write t' i v)).
        { applys* Nth_app_l. }
        asserts HNread: (LibList.Nth (length log) (log & event_read t i v) (event_read t i v)).
        { applys* Nth_app_r'. }
        asserts Hlastf:
          (forall k tk vk, LibList.Nth k (log & event_read t i v) (event_write tk i vk) -> k <= mw).
        { introv HNk. forwards [HN' | (Hpe & Hee)]: Nth_last_inv HNk.
          - applys Hlast HN'.
          - inverts Hee. }
        asserts Hacc: (accesses_location i (event_read t i v)). { reflexivity. }
        forwards Hhb: Hcf HNLf HNread Hacc HLlt.
        asserts HndomL: (i \notindom (D[t'])).
        { destruct (classic (t' = t)) as [-> | Hne].
          - exact Hnin.
          - applys last_writer_not_in_delta Hplayf HNLf Hlastf HNread Hhb. simpl. congruence. }
        forwards Hlv:
          (>> hb_last_write_visible Hwfr Hcf Hcfg Hplayf HNLf Hlastf HndomL HNread Hhb).
        simpl in Hlv.
        exists. applys StepReadGlobal Hbinds; [ eassumption | exact Hnin | exact Hlv ].
    + exists. constructors*.
    + forwards (h' & Hfresh): exists_commit_fresh HwfG.
      forwards* (Heq & _): same_expressions_same_domains.
      rewrite Heq in H6.
      asserts* Hneq: (t <> t').
      asserts (T' & G' & Hpush): (exists T' G', push_thread t t' h' T[t:=(state_running, te_exp (K t'), d, h)][t':=(state_new, te_exp e', \{}, 0)] G = (T', G')).
      {
        exists. unfolds push_thread, do_commit.
        rewrite~ read_update_neq.
        rewrite read_update_same.
        rewrite~ read_update_neq.
        rewrite read_update_same.
        reflexivity.
      }
      exists. constructors*.
    + forwards (h'' & Hfresh): exists_commit_fresh HwfG.
      apply Hsame in H4 as (d' & h' & Hbinds').
      asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_thread t t' h'' T G = (T', G') /\
                                                           binds T' t (state_running, te_exp e, d', h'')).
      {
        exists. unfolds pull_thread, do_merge.
        forwards Hread: read_of_binds Hbinds.
        replace T[t'] with (state_terminated, te_ret r, d, h).
        forwards Hread': read_of_binds Hbinds'.
        replace T[t] with (state_running, te_exp e, d', h').
        splits.
        - reflexivity.
        - apply binds_update_same.
      }
      asserts Hempty: (d = \{}).
      {
        destruct HdescSh as (_ & _ & Hend & _).
        asserts Hmem: (mem (event_end t') log).
        { apply* Hend. }
        destruct HdescB as (_ & _ & Hend' & _).
        apply Hend' in Hmem as (e' & d'' & Hbinds''').
        forwards~ Heq: binds_inj Hbinds Hbinds'''.
        inverts* Heq.
      }
      substs.
      asserts Hmerge: (conflict_free_merge d' h' h G).
      {
        destruct HdescB as (_ & _ & _ & _ & _ & _ &
          (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2)).
        forwards Hcflog: conflict_free_last_inv Hcf.
        (* joiner [t]: [D[t] = d'], [TC[t] = h']. *)
        lets HtT: (indom_of_binds Hbinds').
        forwards (ts0 & e0 & Hbdt): Hdelta HtT.
        forwards* Heqt: binds_inj Hbinds' Hbdt. inverts Heqt.
        (* joined [t']: [TC[t'] = h]. *)
        lets Ht'T: (indom_of_binds Hbinds).
        forwards (ts1 & e1 & Hbdt'): Hdelta Ht'T.
        forwards* Heqt': binds_inj Hbinds Hbdt'. inverts Heqt'.
        forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (_ & HTCdom & _).
        applys conflict_free_merge_holds Hwf Hcflog Hplay;
          [ applys HdomD HtT | applys HdomTC HtT | applys HTCdom; applys HdomTC Ht'T ].
      }
      exists. constructors*.
    + branches.
      * forwards (h'' & Hfresh): exists_commit_fresh HwfG.
        apply Hsame in H0 as (h' & Hlock).
        asserts Hmerge: (conflict_free_merge d h h' G).
        {
          destruct HdescB as (_ & _ & _ & _ & _ & _ &
            (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2)).
          forwards Hcflog: conflict_free_last_inv Hcf.
          (* locker [t]: [D[t] = d], [TC[t] = h]. *)
          lets HtT: (indom_of_binds Hbinds).
          forwards (ts0 & e0 & Hbdt): Hdelta HtT.
          forwards* Heqt: binds_inj Hbinds Hbdt. inverts Heqt.
          (* lock [l0]: [LC[l0] = h']. *)
          lets Hl0L: (indom_of_binds Hlock).
          forwards (ls0 & Hbdl): Hlocks Hl0L.
          forwards* Heql: binds_inj Hlock Hbdl. inverts Heql.
          forwards Hpgwf: play_log_graph_wf Hplay. destruct Hpgwf as (_ & _ & HLCdom).
          applys conflict_free_merge_holds Hwf Hcflog Hplay;
            [ applys HdomD HtT | applys HdomTC HtT | applys HLCdom; applys HdomLC Hl0L ].
        }
        asserts (T' & G' & Hpull & Hbinds''): (exists T' G', pull_lock t l0 h'' T G L = (T', G') /\
                                                               binds T' t (state_running, te_exp e, d, h'')).
        {
          exists. unfolds pull_lock, do_merge.
          forwards Hread: read_of_binds Hlock.
          replace L[l0] with (ls_free, h').
          forwards Hread': read_of_binds Hbinds.
          replace T[t] with (state_running, te_exp e, d, h).
          splits.
          - reflexivity.
          - apply binds_update_same.
        }
        exists. constructors*.
      * forwards* (_ & Heq): same_expressions_same_domains.
        rewrite Heq in *.
        exists. applys* StepLockFresh.
    + forwards (h'' & Hfresh): exists_commit_fresh HwfG.
      asserts (h' & HbindsL): (exists h', binds L l0 (ls_held t, h')).
      {
        destruct HdescSh as (_ & _ & _ & _ & Hlock & _).
        match goal with
        | H : binds L0 l0 (ls_held t) |- _ => apply Hlock in H as Hex
        end.
        destruct HdescB as (_ & _ & _ & _ & Hlock' & _).
        apply* Hlock'.
      }
      asserts (T' & G' & L' & Hpush & Hbinds'): (exists T' G' L', push_lock t l0 h'' T G L = (T', G', L') /\ binds T' t (state_running, te_exp e, \{}, h'')).
      {
        exists. unfolds push_lock, do_commit.
        forwards Hread: read_of_binds Hbinds.
        replace T[t] with (state_running, te_exp e, d, h).
        forwards Hread': read_of_binds HbindsL.
        replace L[l0] with (ls_held t, h').
        splits.
        - reflexivity.
        - apply binds_update_same.
      }
      exists. constructors*.
  - introv (cfgB' & Hstep).
    destruct cfgSh as ((Tsh & H) & Lsh).
    inverts Hstep;
      try
      match goal with
      | H: binds ?T ?t (?ts, ?e, ?d, ?h) |- _ =>
          asserts Hex: (exists d h, binds T t (ts, e, d, h));
          [exists d; exists h; exact H|];
          apply Hsame in Hex as Hbinds; clear Hex
      end.
    + exists. constructors*.
    + exists. constructors*.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hstart & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      apply Hwrite.
      forwards Hcf': conflict_free_last_inv Hcf.
      forwards* Hbinds'': HdomD t.
      forwards* Hex: conflict_free_last_local_write Hplay.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & _ & Hwrite).
      destruct HdescB as (_ & _ & _ & Hrun & _ & _ & (D & TC & LC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC & HdomLC2)).
      forwards~ (ts & e' & Hbinds'): Hdelta t.
      asserts* ->: (d = D[t]).
      forwards* Heq: binds_inj Hbinds'.
      inverts Heq.
      asserts* ->: (h = TC[t]).
      apply Hwrite.
      asserts Hcfg: (conflict_free_graph G).
      { forwards Hcflog: conflict_free_last_inv Hcf.
        applys conflict_free_log_describes_conflict_free_graph Hwf Hcflog Hplay. }
      asserts Hwfr: (wf_log (log & event_read t i v)).
      { lets [_ Hback]: Hrun t.
        forwards (Hms & Hmne): Hback.
        { do 3 eexists. eassumption. }
        applys wf_log_read_last Hms Hmne Hwf. }
      asserts* Hdom: (t \indom T).
      forwards~ Hdom': HdomTC Hdom.
      forwards* Hex: conflict_free_last_global_write Hcf Hwfr Hcfg Hplay.
    + exists. constructors*.
    + exists. constructors*.
      forwards* (-> & _): same_expressions_same_domains.
    + asserts* Hex: (exists d h, binds T t' (state_terminated, te_ret r, d, h)).
      apply Hsame in Hex.
      exists. constructors*.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & _ & HunlockedSh & _).
      destruct HdescB as (_ & _ & _ & _ & _ & HunlockedB & _).
      forwards Hiff: HunlockedSh l0.
      forwards Hiff': HunlockedB l0.
      left. apply Hiff. apply* Hiff'.
    + exists. constructors*.
      forwards* (_ & ->): same_expressions_same_domains.
    + exists. constructors*.
      destruct HdescSh as (_ & _ & _ & _ & HlockedSh & _ & _).
      destruct HdescB as (_ & _ & _ & _ & HunlockedB & _ & _).
      forwards* (t' & log' & Hiff): HlockedSh t l0.
      forwards* (t'' & log'' & Hiff'): HunlockedB t l0.
Qed.

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
