From Vcm Require Import Common.
From Vcm Require Import Graph.
From Vcm Require Import GraphFacts.
From Vcm Require Import Linear.
From Vcm Require Import Branching.
From Vcm Require Import Log.
From Vcm Require Import LogFacts.
From Vcm Require Import LoggingBranching.
From Vcm Require Import LoggingBranchingFacts.
From Vcm Require Import BranchingEquivLemmas.

Import Graph.
Import GraphFacts.
Import Linear.
Import Branching.
Import Log.
Import LogFacts.
Import LoggingBranching.


(* Appending an event that is not a write of [x] by [t] preserves "no x-write by
   [t] after [m]".  (Companion to [no_commit_event_snoc].) *)
Lemma no_xwrite_snoc :
  forall (lg : log) E m t x,
    (forall p vp, m < p -> ~ LibList.Nth p lg (event_write t x vp)) ->
    (forall vp, E <> event_write t x vp) ->
    (forall p vp, m < p -> ~ LibList.Nth p (lg & E) (event_write t x vp)).
Proof.
  introv Hno HneqE. introv Hlt HN.
  forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
  - applys Hno Hlt HN'.
  - apply (HneqE vp). congruence.
Qed.

(* Strengthening of [delta_is_uncommitted_write]: the write that put [x = v] into
   [t]'s staging is not only uncommitted ([t] performs no commit event after it)
   but is the *last* x-write by [t] (no [t]-write of [x] after it).  This is what
   makes it a maximal visible source: [D[t]] always reflects the latest staged
   write, so any later x-write would have overwritten [v]. *)
Lemma delta_last_uncommitted_write :
  forall log D TC G LC VC CH t x v,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    t \indom D ->
    binds D[t] x v ->
    exists m,
      LibList.Nth m log (event_write t x v) /\
      (forall p ep, m <= p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep) /\
      (forall p vp, m < p -> ~ LibList.Nth p log (event_write t x vp)).
Proof.
  introv Hplay Hdom Hbinds.
  inductions Hplay.
  - (* PlayNil: D = empty *)
    rew_dom. rew_set in Hdom.
    branches; [forwards*: indom_empty_inv|].
    subst. rewrite read_update_same in Hbinds.
    forwards* Heq: binds_empty_false Hbinds. typeclass.
  - inverts H.
    + (* PlayRead *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayReadVolatile: merge, D unchanged, never a commit event *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayWrite (event_write t0 x0 v0) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        destruct (classic (x = x0)) as [Hei | Hnei].
        { (* same variable: the new event is the last write, hence the witness *)
          subst x. forwards ->: binds_update_same_inv Hbinds.
          match goal with |- exists m, LibList.Nth m (?lg & _) _ /\ _ => exists (length lg) end.
          splits.
          - applys* Nth_app_r'.
          - introv Hle HN Hg.
            forwards [HN' | (Hpe & Hee)]: Nth_last_inv HN.
            + forwards Hib: Nth_inbound HN'. exfalso. nat_math.
            + subst ep. simpl. auto.
          - introv Hlt HN. forwards Hib: Nth_inbound HN. rew_list in Hib. nat_math. }
        { (* different variable: carry the older write forward *)
          forwards Hbd: binds_update_neq_inv Hbinds Hnei.
          lets Hin: (indom_of_binds H12).
          asserts Hb': (binds (D'[t0]) x v). { forwards: read_of_binds H12. subst*. }
          forwards* (wm & wHN & wHns & wHnw): IHHplay.
          exists wm. splits;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros _; simpl; auto
            | applys no_xwrite_snoc wHnw; intros vp Heq; inverts Heq; congruence ]. } }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros _; simpl; auto
          | applys no_xwrite_snoc wHnw; intros vp Heq; inverts Heq; congruence ]. }
    + (* PlayWriteVolatile (event_write t0 x0 v0): flushes D[t0] entirely,
         matching End/Spawn/Unlock's flush pattern; it is a commit event, but
         only for t0. *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
          | applys no_xwrite_snoc wHnw; intros vp Heq; inverts Heq; congruence ]. }
    + (* PlayStart *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayEnd (event_end t0) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
          | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. }
    + (* PlaySpawn (event_spawn t1 t2) *)
      destruct (classic (t = t2)) as [Het2 | Hneq2].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        destruct (classic (t = t1)) as [Het1 | Hneq1].
        { subst t. rewrite read_update_same in Hbinds.
          lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
        { rewrite~ read_update_neq in Hbinds.
          asserts Hin: (t \indom D').
          { lets [Hc2 | Hd2]: (indom_update_inv Hdom). congruence.
            lets [Hc1 | Hd1]: (indom_update_inv Hd2). congruence. exact Hd1. }
          forwards* (wm & wHN & wHns & wHnw): IHHplay.
          exists wm. splits;
            [ applys* Nth_app_l wHN
            | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
            | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. } }
    + (* PlayJoin: merge, D unchanged *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayLock: merge, D unchanged *)
      forwards* (wm & wHN & wHns & wHnw): IHHplay.
      exists wm. splits;
        [ applys* Nth_app_l wHN
        | applys no_commit_event_snoc wHns; intros _; simpl; auto
        | applys no_xwrite_snoc wHnw; intros vp; discriminate ].
    + (* PlayUnlock (event_unlock t0 l) *)
      destruct (classic (t = t0)) as [Het | Hneq].
      { subst t. rewrite read_update_same in Hbinds.
        lets Hi: (indom_of_binds Hbinds). forwards*: indom_empty_inv. }
      { rewrite~ read_update_neq in Hbinds.
        asserts Hin: (t \indom D').
        { lets [Hc | Hd]: (indom_update_inv Hdom). congruence. exact Hd. }
        forwards* (wm & wHN & wHns & wHnw): IHHplay.
        exists wm. splits;
          [ applys* Nth_app_l wHN
          | applys no_commit_event_snoc wHns; intros Hgt; simpl in Hgt; congruence
          | applys no_xwrite_snoc wHnw; intros vp; discriminate ]. }
Qed.

(* The least commit event of [t] in the interval [(a, b]]: given SOME commit of
   [t] at [b > a], there is a first one [f] with no [t]-commit in [(a, f)]. *)
Lemma exists_first_commit :
  forall b lg t a eb,
    a < b -> LibList.Nth b lg eb -> get_thread eb = t -> is_commit_event eb ->
    exists f ef, a < f /\ f <= b /\ LibList.Nth f lg ef /\ get_thread ef = t /\
      is_commit_event ef /\
      (forall p ep, a < p -> p < f -> LibList.Nth p lg ep -> get_thread ep = t ->
                    ~ is_commit_event ep).
Proof.
  intros b. induction b using peano_induction. introv Hab HNb Hgb Hcb.
  destruct (classic (exists p ep, a < p /\ p < b /\ LibList.Nth p lg ep /\
                                  get_thread ep = t /\ is_commit_event ep))
    as [(p & ep & Hap & Hpb & HNp & Hgp & Hcp) | Hno].
  - forwards (f & ef & Haf & Hfp & HNf & Hgf & Hcf & Hcl): (>> H p Hap HNp Hgp Hcp); [ nat_math | ].
    exists f ef. splits; try assumption. nat_math.
  - exists b eb. splits; try assumption; try nat_math.
    introv Hap Hpb HNp Hgp Hcp. applys Hno. exists p ep. splits; assumption.
Qed.

(* A commit is created at a unique position: two commit events recording the same
   commit are the same event.  (The commit is fresh when created, so it cannot
   already be in the graph from an earlier creation.) *)
Lemma CH_commit_event_inj :
  forall log D TC G LC CH i j c ei ej,
    play_log log init_play_cfg (D, TC, G, LC) CH ->
    LibList.Nth i CH c -> LibList.Nth i log ei -> is_commit_event ei ->
    LibList.Nth j CH c -> LibList.Nth j log ej -> is_commit_event ej ->
    i = j.
Proof.
  introv Hplay. gen i j c ei ej. inductions Hplay; introv HNci HNli Hci HNcj HNlj Hcj.
  - forwards*: Nth_nil_inv HNci.
  - rename H into Hpe. forwards Hlen: play_log_CH_length Hplay.
    forwards [HNci0 | (HiN & Hcxi)]: Nth_last_inv HNci;
    forwards [HNcj0 | (HjN & Hcxj)]: Nth_last_inv HNcj.
    + (* both old: recurse *)
      forwards [HNli0 | (HiN' & _)]: Nth_last_inv HNli.
      2:{ forwards Hib: Nth_inbound HNci0. nat_math. }
      forwards [HNlj0 | (HjN' & _)]: Nth_last_inv HNlj.
      2:{ forwards Hib: Nth_inbound HNcj0. nat_math. }
      forwards* Heqij: (>> IHHplay HNci0 HNli0 Hci HNcj0 HNlj0 Hcj).
    + (* i old, j fresh: [c] both fresh at [j] and present from [i] -- contradiction *)
      exfalso.
      forwards [HNli0 | (HiN' & _)]: Nth_last_inv HNli.
      2:{ forwards Hib: Nth_inbound HNci0. nat_math. }
      forwards [HNlj0 | (HjN' & HljE)]: Nth_last_inv HNlj.
      { forwards Hib: Nth_inbound HNlj0. rewrite Hlen in HjN. nat_math. }
      subst ej. forwards Hin: CH_commit_event_indom Hplay HNci0 HNli0 Hci.
      forwards (Hfr & _): play_event_commit_new Hpe Hcj.
      rewrite Hcxj in Hfr. applys commit_fresh_not_indom Hfr Hin.
    + (* i fresh, j old: symmetric *)
      exfalso.
      forwards [HNlj0 | (HjN' & _)]: Nth_last_inv HNlj.
      2:{ forwards Hib: Nth_inbound HNcj0. nat_math. }
      forwards [HNli0 | (HiN' & HliE)]: Nth_last_inv HNli.
      { forwards Hib: Nth_inbound HNli0. rewrite Hlen in HiN. nat_math. }
      subst ei. forwards Hin: CH_commit_event_indom Hplay HNcj0 HNlj0 Hcj.
      forwards (Hfr & _): play_event_commit_new Hpe Hci.
      rewrite Hcxi in Hfr. applys commit_fresh_not_indom Hfr Hin.
    + (* both fresh: same position *)
      nat_math.
Qed.

(* HELPER 1: a write at [m] by [t] with no [t]-commit after [m] leaves [x] in
   [t]'s staging area [D[t]].  [wf_log] is needed only to rule out a re-spawn of
   [t] (which would reset [D[t]] to empty) via [spawned_thread_no_prior_event].
   [x \notin Volatiles] is needed too: a *volatile* write is its own commit
   event (at [m] itself, not strictly after it, so [Hncl] does not exclude it),
   and immediately flushes [D[t]] to empty -- so the conclusion would be false
   if the traced write [event_write t x v] were itself a volatile write. *)
Lemma write_persists_in_delta :
  forall log D TC G LC VC CH t x v m,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \notin Volatiles ->
    LibList.Nth m log (event_write t x v) ->
    (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep) ->
    x \indom (D[t]).
Proof.
  introv Hwf Hplay Hxnvol. gen m t x v. inductions Hplay; introv Hxnvol HNm Hncl.
  - inverts HNm.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HN0 | (HmN & HemE)]: Nth_last_inv HNm.
    + (* the write is in the prefix; E is the last (appended) event, at [length log] > m *)
      forwards Hib: Nth_inbound HN0.
      asserts HNE: (LibList.Nth (length log) (log & E) E).
      { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
      asserts Hncl0:
        (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
      { introv Hlt HNp Hgp. forwards HNp': Nth_app_l HNp. applys Hncl Hlt HNp' Hgp. }
      forwards* Hin0: (>> IHHplay Hwf0 HN0 Hncl0).
      (* now push [x \indom D'[t]] through the last play event to [x \indom D''[t]] *)
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        inverts H.
      * (* spawn s1 s2 : a commit of s1; s2 is freshly spawned so [t <> s2] *)
        forwards Hns2: spawned_thread_no_prior_event Hwf HN0. cbn [get_thread] in Hns2.
        destruct (classic (t = s1)) as [Hs1 | Hs1].
        -- subst s1. exfalso. applys Hncl (length log) (event_spawn t s2); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ | congruence ].
           rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* join : D unchanged *) exact Hin0.
      * (* read : D unchanged *) exact Hin0.
      * (* read volatile : D unchanged *) exact Hin0.
      * (* write wt wj ww : domain only grows *)
        destruct (classic (t = wt)) as [Hwt | Hwt].
        -- subst wt. rewrite read_update_same.
           match goal with Hbd : binds _ t ?dstg |- _ =>
             forwards Hdeq: read_of_binds Hbd end.
           apply indom_update_of_indom; (typeclass || (rewrite <- Hdeq; exact Hin0)).
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* volatile write: flushes D[wt] entirely; if t=wt this write is
           itself a commit event of t, excluded by Hncl; otherwise D[t] is
           unaffected, mirroring spawn/unlock/end's flush pattern *)
        destruct (classic (t = wt)) as [Hwt | Hwt].
        -- subst wt. exfalso. applys Hncl (length log) (event_write t wj ww); try nat_math.
           exact HNE. reflexivity. simpl; assumption.
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* lock (PlayLock) : D unchanged *) exact Hin0.
      * (* unlock ut ul : a commit of ut; if [t = ut] excluded by [Hncl] *)
        destruct (classic (t = ut)) as [Hut | Hut].
        -- subst ut. exfalso. applys Hncl (length log) (event_unlock t ul); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
      * (* start : D unchanged *) exact Hin0.
      * (* end ett : a commit of ett; if [t = ett] excluded by [Hncl] *)
        destruct (classic (t = ett)) as [Het | Het].
        -- subst ett. exfalso. applys Hncl (length log) (event_end t); try nat_math.
           exact HNE. reflexivity. simpl; exact I.
        -- rewrite read_update_neq; [ exact Hin0 | congruence ].
    + (* the write is the last (appended) event *)
      subst E. inverts H.
      * (* PlayWrite, non-volatile *)
        rewrite read_update_same. apply indom_update_same; typeclass.
      * (* PlayWriteVolatile: impossible, since [x] is assumed non-volatile *)
        false.
Qed.

(* HELPER 2: the first commit event [f] of [t] after a write [m] of [x = v]
   (with no [t]-commit in [(m, f)]) flushes [x] into the graph: its commit
   [cf = CH[f]] is an x-writer.  ([v] need not be the flushed value: the delta may
   have been overwritten between [m] and [f], but [x] is still in [t]'s staging
   area at flush time, by [write_persists_in_delta].) *)
Lemma xwrite_flush_writer :
  forall log D TC G LC VC CH t x v m f ef cf,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    x \notin Volatiles ->
    LibList.Nth m log (event_write t x v) ->
    m < f -> LibList.Nth f log ef -> get_thread ef = t -> is_commit_event ef ->
    (forall p ep, m < p -> p < f -> LibList.Nth p log ep -> get_thread ep = t ->
                  ~ is_commit_event ep) ->
    LibList.Nth f CH cf ->
    exists vf, graph_writes G cf x vf.
Proof.
  introv Hwf Hplay Hxnvol. gen m t x v f ef cf. inductions Hplay; introv Hxnvol HNm Hmf HNf Hgf Hcf Hncl HNfch.
  - inverts HNm.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HNf0 | (HfN & HefE)]: Nth_last_inv HNf.
    + (* the commit [f] is in the prefix: recurse there, then lift the graph *)
      forwards Hfib: Nth_inbound HNf0.
      forwards [HNm0 | (HmN & HmE)]: Nth_last_inv HNm.
      2:{ forwards Hib: Nth_inbound HNf0. nat_math. }
      forwards [HNfch0 | (HfchN & _)]: Nth_last_inv HNfch.
      2:{ rewrite Hlen in HfchN. nat_math. }
      asserts Hncl0:
        (forall p ep, m < p -> p < f -> LibList.Nth p log ep -> get_thread ep = t ->
                      ~ is_commit_event ep).
      { introv Hlt Hpf HNp Hgp. forwards HNp': Nth_app_l HNp. applys Hncl Hlt Hpf HNp' Hgp. }
      forwards* (vf & Hgw): (>> IHHplay Hwf0 HNm0 Hmf HNf0 Hgf Hcf Hncl0 HNfch0).
      exists vf. applys play_event_graph_writes_mono H Hgw.
    + (* the commit [f] is the last (appended) event [E], a commit event by [t] *)
      subst ef.
      (* [m] is strictly before [f = length log], hence in the prefix *)
      forwards [HNm0 | (HmN & HmE)]: Nth_last_inv HNm.
      2:{ subst. nat_math. }
      forwards Hmib: Nth_inbound HNm0.
      (* cf = CH[length log] = TC''[get_thread E] *)
      forwards [HNfch0 | (HfchN & Hcxeq)]: Nth_last_inv HNfch.
      { forwards Hib: Nth_inbound HNfch0. rewrite Hlen in Hib. nat_math. }
      (* [x] is in [t]'s staging area in the prefix (no [t]-commit after [m] in prefix) *)
      asserts Hnclp:
        (forall p ep, m < p -> LibList.Nth p log ep -> get_thread ep = t -> ~ is_commit_event ep).
      { introv Hlt HNp Hgp. forwards Hpib: Nth_inbound HNp.
        forwards HNp': Nth_app_l HNp.
        applys Hncl Hlt; [ nat_math | exact HNp' | exact Hgp ]. }
      forwards HxinD: (>> write_persists_in_delta Hwf0 Hplay Hxnvol HNm0 Hnclp).
      (* [E] is a commit event by [t]: spawn (as spawner), unlock, or end *)
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        cbn [get_thread is_commit_event] in Hgf, Hcf; try contradiction;
        cbn [get_thread] in Hcxeq; inverts H.
      * (* PlaySpawn s1 s2, spawner is [t = s1] *)
        subst t.
        match goal with HbD : binds D' s1 d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq.
        destruct (classic (s1 = s2)) as [Heqt | Hnet].
        -- subst s2. rewrite read_update_same.
           applys graph_writes_graph_commit_new Hbxv.
        -- rewrite read_update_neq; [ | congruence ]. rewrite read_update_same.
           applys graph_writes_graph_commit_new Hbxv.
      * (* PlayWrite (non-volatile): contradicts [Hcf : wj \in Volatiles] *)
        congruence.
      * (* PlayWriteVolatile (event_write wt wj ww), [t = wt]: this is [t]'s own
           flush; [x <> wj] since [x] is non-volatile ([Hxnvol]) but [wj] is
           volatile ([Hcf]), so [x]'s value is unaffected by the fold-in. *)
        subst t.
        match goal with HbD : binds D' wt d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hxwj: (x <> wj).
        { intro Heq. subst wj. applys Hxnvol. exact Hcf. }
        asserts Hbxd: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        asserts Hbxv: (binds (d[wj := ww]) x (d[x])).
        { applys~ binds_update_neq Hbxd. }
        eexists. rewrite <- Hcxeq. rewrite read_update_same.
        applys graph_writes_graph_commit_new Hbxv.
      * (* PlayUnlock ut ul, [t = ut] *)
        subst t.
        match goal with HbD : binds D' ut d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq. rewrite read_update_same.
        applys graph_writes_graph_commit_new Hbxv.
      * (* PlayEnd ett, [t = ett] *)
        subst t.
        match goal with HbD : binds D' ett d |- _ =>
          forwards Hdd: read_of_binds HbD end.
        asserts Hxd: (x \indom d). { rewrite <- Hdd. exact HxinD. }
        asserts Hbxv: (binds d x (d[x])).
        { applys binds_of_indom_read Hxd; (reflexivity || typeclass). }
        eexists. rewrite <- Hcxeq. rewrite read_update_same.
        applys graph_writes_graph_commit_new Hbxv.
Qed.

(* HELPER 3: the write feeding a flush commit is the *last* x-write of its thread
   before the flush.  If [cw = CH[fw]] is the commit of a [tw]-flush at [fw] and
   [cw] writes [x = v0] in the graph, then there is a [tw]-write of [x = v0] at some
   [kL < fw] that is the last [tw]-x-write before [fw] (and [tw] does not commit in
   [[kL, fw)]).  The committed diff is [tw]'s staging area at flush time, whose
   [x]-value is pinned to the last x-write by [delta_last_uncommitted_write]. *)
Lemma flush_last_write :
  forall log D TC G LC VC CH tw x0 fw ef cw v0,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth fw CH cw -> LibList.Nth fw log ef ->
    get_thread ef = tw -> is_commit_event ef ->
    graph_writes G cw x0 v0 ->
    exists kL,
      kL <= fw /\ LibList.Nth kL log (event_write tw x0 v0) /\
      (forall p ep, kL <= p -> p < fw -> LibList.Nth p log ep -> get_thread ep = tw ->
                    ~ is_commit_event ep) /\
      (forall p vp, kL < p -> p < fw -> ~ LibList.Nth p log (event_write tw x0 vp)).
Proof.
  introv Hwf Hplay. gen tw x0 fw ef cw v0. inductions Hplay;
    introv HNfch HNf Hgf Hcf Hgw.
  - forwards*: Nth_nil_inv HNfch.
  - forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HNf0 | (HfN & HefE)]: Nth_last_inv HNf.
    + (* flush in the prefix: recurse, then lift graph_writes back *)
      forwards Hfib: Nth_inbound HNf0.
      forwards [HNfch0 | (HfchN & _)]: Nth_last_inv HNfch.
      2:{ rewrite Hlen in HfchN. nat_math. }
      (* the fresh commit is a sink; [cw] is old, so its writes come from the prefix *)
      asserts Hgw0: (graph_writes G' cw x0 v0).
      { forwards Hin: CH_commit_event_indom Hplay HNfch0 HNf0 Hcf.
        rename H into Hpe. inverts Hpe; try exact Hgw;
          match goal with Hfr : commit_fresh G' ?cfresh |- _ =>
            asserts Hne: (cw <> cfresh);
            [ intro Heq; subst cw; applys commit_fresh_not_indom Hfr Hin | ] end;
          first [ applys graph_writes_graph_commit_inv Hne Hgw
                | applys graph_writes_graph_merge_inv Hne Hgw
                | (* PlayWriteVolatile: two fresh layers (merge then commit) *)
                  match goal with
                  | Hfr2 : commit_fresh (graph_merge G' _ _ _) ?cc'' |- _ =>
                    asserts Hne2: (cw <> cc'');
                    [ intro Heq2; subst cw; applys commit_fresh_not_indom Hfr2;
                      applys~ graph_merge_indom Hin
                    | forwards Hgw1: graph_writes_graph_commit_inv Hne2 Hgw;
                      applys graph_writes_graph_merge_inv Hne Hgw1 ]
                  end ].
      }
      forwards* (kL & HkLlt & HNkL & Hnc & Hnw): (>> IHHplay Hwf0 HNfch0 HNf0 Hgf Hcf Hgw0).
      exists kL. splits.
      * exact HkLlt.
      * applys Nth_app_l HNkL.
      * introv Hle Hpf HNp Hgp. forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp.
        -- applys Hnc Hle Hpf HNp0 Hgp.
        -- nat_math.
      * introv Hlt Hpf HNp. forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp.
        -- applys Hnw Hlt Hpf HNp0.
        -- nat_math.
    + (* flush is the last event [E]: a commit by [tw] storing [tw]'s prefix delta *)
      subst ef.
      forwards [HNfch0 | (HfchN & Hcxeq)]: Nth_last_inv HNfch.
      { forwards Hib: Nth_inbound HNfch0. rewrite Hlen in Hib. nat_math. }
      destruct E as [s1 s2 | jt1 jt2 | rt rj rw | wt wj ww | lt ll | ut ul | stt | ett];
        cbn [get_thread is_commit_event] in Hgf, Hcf; try contradiction;
        cbn [get_thread] in Hcxeq; inverts H.
      * (* PlaySpawn s1 s2, spawner [tw = s1] *)
        subst tw.
        match goal with HbTC : binds TC' s1 ?cc, HbD : binds D' s1 d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw;
            (destruct (classic (s1 = s2)) as [Heqt | Hnet];
             [ subst s2; rewrite read_update_same in Hgw
             | rewrite read_update_neq in Hgw; [ rewrite read_update_same in Hgw | congruence ] ]);
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
      * (* PlayWrite (non-volatile): contradicts [Hcf : wj \in Volatiles] *)
        congruence.
      * (* PlayWriteVolatile (event_write wt wj ww), [tw = wt]: either [cw]'s
           value for [x0] came from this write's own fold-in ([x0 = wj], the
           self-flush case), or it was already staged in [d] beforehand
           ([x0 <> wj], same as the Spawn/Unlock/End cases). *)
        subst tw.
        rewrite <- Hcxeq in Hgw. rewrite read_update_same in Hgw.
        forwards Hbdd: graph_writes_graph_commit_same Hgw.
        destruct (classic (x0 = wj)) as [Heqx | Hneqx].
        -- subst x0. forwards Heqv0: binds_update_same_inv Hbdd. subst v0.
           exists (length log). splits.
           ++ nat_math.
           ++ applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ].
           ++ introv Hle Hpf HNp Hgp. forwards Hib: Nth_inbound HNp. nat_math.
           ++ introv Hlt Hpf HNp. forwards Hib: Nth_inbound HNp. nat_math.
        -- forwards Hbdd': binds_update_neq_inv Hbdd Hneqx.
           match goal with HbD : binds D' wt d |- _ =>
             forwards Hdd: read_of_binds HbD;
             rewrite <- Hdd in Hbdd';
             forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd';
             forwards HkLib: Nth_inbound HNkL;
             exists kL; splits;
             [ nat_math
             | applys Nth_app_l HNkL
             | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
               [ applys Hnc Hle HNp0 Hgp | nat_math ]
             | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
               [ applys Hnw Hlt HNp0 | nat_math ] ] end.
      * (* PlayUnlock ut ul, [tw = ut] *)
        subst tw.
        match goal with HbTC : binds TC' ut ?cc, HbD : binds D' ut d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw; rewrite read_update_same in Hgw;
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
      * (* PlayEnd ett, [tw = ett] *)
        subst tw.
        match goal with HbTC : binds TC' ett ?cc, HbD : binds D' ett d |- _ =>
          asserts Hbdd: (binds d x0 v0);
          [ rewrite <- Hcxeq in Hgw; rewrite read_update_same in Hgw;
            applys graph_writes_graph_commit_same Hgw
          | forwards Hdd: read_of_binds HbD;
            rewrite <- Hdd in Hbdd;
            forwards (kL & HNkL & Hnc & Hnw): delta_last_uncommitted_write Hplay (indom_of_binds HbD) Hbdd;
            forwards HkLib: Nth_inbound HNkL;
            exists kL; splits;
            [ nat_math
            | applys Nth_app_l HNkL
            | introv Hle Hpf HNp Hgp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnc Hle HNp0 Hgp | nat_math ]
            | introv Hlt Hpf HNp; forwards [HNp0 | (HpN & _)]: Nth_last_inv HNp;
              [ applys Hnw Hlt HNp0 | nat_math ] ] ] end.
Qed.

(* ============================================================================
   Happens-before consistency (branching): preservation of [hb_consistent] by
   [LoggingBranching.step].

   A read at position [n] is [sourced] (Log.v [sourced_read]) when its value [v]
   of [x] is written by some write at [m] that is (i) not hb-after the read, and
   (ii) a *maximal visible* writer: no other x-write sits hb-strictly between it
   and the read.  This is proved as an invariant of the logging step because
   [play_log]'s [PlayRead] ignores the read value; the constraint is pinned only
   at read-*step* time.

   The eight non-read steps reduce to [hb_consistent_snoc_nonread].  The two read
   steps establish sourcedness of the freshly appended read:
     - StepReadLocal:  source is [t]'s own last uncommitted x-write [D[t][x]].
     - StepReadGlobal: source is the [is_latest_value] maximal x-writing ancestor
       of [TC[t]]; maximality rules out an intervening x-write via the (existing)
       [hb ==> ancestor] direction ([hb_pointer_ancestor]).
   Both directions are UNCONDITIONAL (no [race_free]).
   ============================================================================ *)

Theorem step_preserves_hb_consistent :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    hb_consistent log ->
    hb_consistent log'.
Proof.
  introv Hwf Hdesc Hstep Hhbc.
  inverts Hstep;
    try (applys hb_consistent_snoc_nonread Hhbc; intros; discriminate).
  - (* StepReadLocal: source is [t]'s own last uncommitted write [D[t][x]]. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, ?dd, _), Hd : binds ?dd _ _ |- _ =>
        rename Hb into HbT; rename Hd into Hbd
    end.
    destruct Hdesc as (_ & _ & _ & _ & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    forwards HtinD: HdomD HtinT.
    forwards (m & HNm & Hunc & Hnw): delta_last_uncommitted_write Hplay HtinD Hbd.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + (* an older read: preserved by [sourced_read_snoc] *)
      forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: sourced_read_snoc Hlt (Hhbc n). applys Hsr Hnth.
    + (* the freshly appended read at position [length log] *)
      inverts Heq. subst n.
      exists m t0. splits.
      * applys Nth_app_l HNm.
      * intros Hhb. forwards Hlt: hb_lt Hhb. forwards Hm: Nth_inbound HNm. nat_math.
      * (* maximality: no x-write hb-strictly-between [W = D[t][x]] and the read *)
        introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
        forwards Hm'lt: hb_lt Hhb'.
        forwards [Hmth'' | (Hpe' & Hee')]: Nth_last_inv Hmth'; [| inverts Hee'].
        forwards Hhb_l: hb_app_inv Hhb Hm'lt.
        destruct (classic (t'' = t0)) as [Ht'' | Ht''].
        -- subst t''. forwards Hmm': hb_lt Hhb_l.
           applys Hnw Hmm' Hmth''.
        -- asserts Hgm: (get_thread (event_write t0 x0 v0) = t0). { reflexivity. }
           asserts Hgm': (get_thread (event_write t'' x0 v') <> t0). { simpl. exact Ht''. }
           forwards (f & ef & Hle & HNf & Hgf & Hcf & Hhbf):
             hb_cross_thread_flush Hhb_l HNm Hgm Hmth'' Hgm'.
           forwards Hni: Hunc Hle HNf Hgf. applys Hni Hcf.
  - (* StepReadGlobal: source is the [is_latest_value] maximal x-writing ancestor. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, _, ?cc), Hl : is_latest_value _ ?cc _ _ |- _ =>
        rename Hb into HbT; rename Hl into Hlv
    end.
    destruct Hdesc as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    (* The source is the write [kw] that actually *feeds* [cw] (flushed at
       [fw], with [CH[fw] = cw]). *)
    forwards (fw & ef & tw & kw & HNfw & HNef & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush Hplay Hgw.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: sourced_read_snoc Hlt (Hhbc n). applys Hsr Hnth.
    + inverts Heq. subst n.
      match goal with Hxv : x0 \notin Volatiles |- _ => rename Hxv into Hxnvol end.
      (* The source is the LAST [tw]-write of [x0] before the flush [fw]: [cw]'s
         stored value is [x0]'s delta value at flush, pinned to the last x0-write. *)
      forwards (kL & HkLlt & HNkL & HnclL & HnwL):
        (>> flush_last_write Hwf Hplay HNfw HNef Hgtef Hcef Hgw).
      forwards HlenCH: play_log_CH_length Hplay.
      forwards HkLib: Nth_inbound HNkL.
      exists kL tw. splits.
      * applys Nth_app_l HNkL.
      * intros Hhb. forwards Hlt: hb_lt Hhb. nat_math.
      * (* Maximality *)
        introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
        (* ---- common setup ---- *)
        forwards Hm'lt: hb_lt Hhb'.
        forwards [Hmth'' | (Hpe' & Hee')]: Nth_last_inv Hmth'; [| inverts Hee'].
        forwards HmthL: hb_app_inv Hhb Hm'lt.
        (* reader [t0] is running: it has started and not ended *)
        forwards (HstartT & HnoendT): (proj2 (Hrun t0)).
        { exists (te_exp e) D[t0] TC[t0]. exact HbT. }
        forwards HwfR: wf_log_read_last HstartT HnoendT Hwf.
        (* extended play including the read (a no-op that appends [TC[t0]] to [CH]) *)
        asserts HplayR:
          (play_log (log & event_read t0 x0 v0) init_play_cfg (D, TC, G, LC, VC) (CH & TC[t0])).
        { applys PlaySnoc Hplay. applys* PlayRead. }
        asserts HNRch: (LibList.Nth (length log) (CH & TC[t0]) (TC[t0])).
        { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
        (* the write event at [m'], both in [log] and in [log & read] *)
        asserts Hm'app: (LibList.Nth m' (log & event_read t0 x0 v0) (event_write t'' x0 v')).
        { applys Nth_app_l Hmth''. }
        asserts HNRapp: (LibList.Nth (length log) (log & event_read t0 x0 v0) (event_read t0 x0 v0)).
        { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
        (* a first [t'']-commit [f] after [m'] with [hb f R], in the prefix *)
        asserts Hcommit:
          (exists b eb, m' < b /\ b < length log /\ LibList.Nth b log eb /\
                        get_thread eb = t'' /\ is_commit_event eb /\
                        hb (log & event_read t0 x0 v0) b (length log)).
        { destruct (classic (t'' = t0)) as [Ht0 | Ht0].
          - (* same thread as the reader: [W'] by [t0] *)
            subst t''.
            destruct (classic (exists b eb, m' < b /\ b < length log /\
                      LibList.Nth b log eb /\ get_thread eb = t0 /\ is_commit_event eb))
              as [(b & eb & Hmb & Hblt & HNb & Hgb & Hcb) | Hnone].
            + exists b eb. splits; try assumption.
              asserts HNbapp: (LibList.Nth b (log & event_read t0 x0 v0) eb).
              { applys Nth_app_l HNb. }
              applys HbPo HNbapp HNRapp; [ cbn [get_thread]; congruence | nat_math ].
            + exfalso.
              asserts Hncl0:
                (forall p ep, m' < p -> LibList.Nth p log ep -> get_thread ep = t0 ->
                              ~ is_commit_event ep).
              { introv Hlt HNp Hgp Hcp. forwards Hpib: Nth_inbound HNp.
                applys Hnone. exists p ep. splits; try assumption; try nat_math. }
              forwards HxinD: (>> write_persists_in_delta Hwf Hplay Hxnvol Hmth'' Hncl0).
              false*.
          - (* other thread *)
            forwards (f0 & ef0 & Hle0 & HNf0 & Hgf0 & Hcf0 & Hhbf0):
              (>> hb_cross_thread_flush Hhb' Hm'app (eq_refl : get_thread (event_write t'' x0 v') = t'')
                  HNRapp).
            { cbn [get_thread]. intro HH. applys Ht0. rewrite~ HH. }
            (* [f0 < length log], since the read at [length log] is by [t0 <> t''] *)
            forwards [HNf0' | (Hf0N & Hf0E)]: Nth_last_inv HNf0.
            2:{ subst ef0. cbn [get_thread] in Hgf0. congruence. }
            forwards Hf0lt: Nth_inbound HNf0'.
            asserts Hm'f0: (m' < f0).
            { destruct (classic (m' = f0)) as [He | Hne']; [ | nat_math ].
              subst f0. forwards Heqw: Nth_functional HNf0' Hmth''.
              subst ef0. cbn [is_commit_event] in Hcf0. contradiction. }
            exists f0 ef0. splits; try assumption. }
        destruct Hcommit as (b & eb & Hmb & Hblt & HNb & Hgb & Hcb & Hhbb).
        (* first such commit [f] (no [t'']-commit in [(m', f)]) *)
        forwards (f & ef2 & Hmf & Hfb & HNf2 & Hgf2 & Hcf2 & HnclF):
          (>> exists_first_commit Hmb HNb Hgb Hcb).
        forwards Hflt: Nth_inbound HNf2.
        asserts HfltCH: (f < length CH). { rewrite HlenCH. nat_math. }
        forwards (cf & HNcf): Nth_inbound_inv HfltCH.
        (* [cf] writes [x0] *)
        forwards (vf & Hgwf): (>> xwrite_flush_writer Hwf Hplay Hxnvol Hmth'' Hmf HNf2 Hgf2 Hcf2 HnclF HNcf).
        asserts HhbfR: (hb (log & event_read t0 x0 v0) f (length log)).
        { destruct (classic (f = b)) as [Hfe | Hfne].
          - subst f. exact Hhbb.
          - asserts HNf2app: (LibList.Nth f (log & event_read t0 x0 v0) ef2).
            { applys Nth_app_l HNf2. }
            asserts HNbapp: (LibList.Nth b (log & event_read t0 x0 v0) eb).
            { applys Nth_app_l HNb. }
            asserts Hhbfb: (hb (log & event_read t0 x0 v0) f b).
            { applys HbPo HNf2app HNbapp; [ congruence | nat_math ]. }
            applys HbTrans Hhbfb Hhbb. }
        (* [cf] is an ancestor of [TC[t0]] (the reader's commit) *)
        asserts HNcfapp: (LibList.Nth f (CH & TC[t0]) cf). { applys Nth_app_l HNcf. }
        forwards HancfTC: (>> hb_pointer_ancestor HwfR HplayR HhbfR HNcfapp HNRch).
        destruct (classic (tw = t'')) as [Htweq | Htwne].
        -- (* same thread [tw = t''] *)
           rewrite <- Htweq in Hmth''.
           forwards HmL: hb_lt HmthL.
           asserts Hm'fw: (fw <= m').
           { destruct (classic (m' < fw)) as [Hlt | Hge]; [ | nat_math ].
             exfalso. applys HnwL m' v'; [ nat_math | nat_math | exact Hmth'' ]. }
           asserts Hfwf: (fw < f).
           { nat_math. }
           asserts Hgf2tw: (get_thread ef2 = tw). { rewrite Hgf2. rewrite~ Htweq. }
           asserts Hanccwcf: (ancestor G cw cf).
           { applys (>> CH_thread_monotone Hwf Hplay HNef Hgtef HNf2 Hgf2tw HNfw HNcf).
             nat_math. }
           asserts Hcfne: (cf <> cw).
           { intro Heq. subst cf.
             forwards Heqpos: (>> CH_commit_event_inj Hplay HNcf HNf2 Hcf2 HNfw HNef Hcef).
             nat_math. }
           forwards Heqcf: (>> Hmax cf vf Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
        -- (* different threads *)
           asserts Hanccwcf: (ancestor G cw cf).
           { asserts Hmfle: (m' <= f). { nat_math. }
             applys (>> write_hb_flush_ancestor Hwf Hplay
               (conj HNkL (conj HNfw (conj HNef (conj Hgtef (conj Hcef (conj HkLlt HnclL))))))
               (conj Hmth'' (conj HNcf (conj HNf2 (conj Hgf2 (conj Hcf2 Hmfle)))))
               Htwne HmthL). }
           asserts Hcfne: (cf <> cw).
           { intro Heq. subst cf.
             forwards Heqpos: (>> CH_commit_event_inj Hplay HNcf HNf2 Hcf2 HNfw HNef Hcef).
             subst f. forwards Heqe: Nth_functional HNf2 HNef.
             rewrite Heqe in Hgf2. cbn [get_thread] in Hgf2. applys Htwne. congruence. }
           forwards Heqcf: (>> Hmax cf vf Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
  - (* StepVolatileRead: pulling a volatile read merges [x]'s stored commit
       into a fresh commit [c'']; sourcing is proved directly against the
       post-pull graph [G'] and log [log & event_read t0 x0 v0] (built via
       [PlayReadVolatile]), since (unlike [StepReadGlobal]) the read itself
       changes the graph. Every write of a volatile variable is itself a
       commit event (self-flushing), so an intervening writer's own position
       already is its flush commit ([write_volatile_graph_writes]), with no
       need to search for a later flush. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, _, ?cc), Hl : is_latest_value _ ?cc _ _ |- _ =>
        rename Hb into HbT; rename Hl into Hlv
    end.
    match goal with
    | Hb0 : binds T t (state_running, te_exp _, _, ?cc0) |- _ => rename Hb0 into HbT0
    end.
    match goal with Hxvol0 : x \in Volatiles |- _ => rename Hxvol0 into HxVol end.
    match goal with Hfr0 : commit_fresh G c'' |- _ => rename Hfr0 into Hfresh end.
    destruct Hdesc as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT0).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT0 Hbd'. inverts Heqt.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    forwards (HstartT & HnoendT): (proj2 (Hrun t)).
    { exists (te_exp e) D[t] TC[t]. exact HbT0. }
    forwards HwfR: wf_log_read_last HstartT HnoendT Hwf.
    asserts HbTCc: (binds TC t (TC[t])).
    { applys binds_of_indom_read (HdomTC t HtinT); (reflexivity || typeclass). }
    asserts HG'eq: (G' = graph_merge G (vc_read VC x) (TC[t]) c'').
    { unfold Branching.pull_volatile, Branching.do_merge in H8.
      rewrite (read_of_binds HbT0) in H8. cbn in H8. inverts* H8.
    }
    asserts HplayR:
      (play_log (log & event_read t x v) init_play_cfg (D, TC[t := c''], G', LC, VC) (CH & c'')).
    { rewrite HG'eq.
      forwards Hpe: PlayReadVolatile HxVol HbTCc Hfresh.
      forwards Hp2: PlaySnoc Hplay Hpe.
      rewrite read_update_same in Hp2. exact Hp2. }
    forwards HlenCH0: play_log_CH_length Hplay.
    forwards (fw & ef & tw & kw & HNfw & HNef & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush HplayR Hgw.
    asserts Hfwlt: (fw < length log).
    { forwards [Hfwlt' | (HfwN & HfwE)]: Nth_last_inv HNef.
      - applys Nth_inbound Hfwlt'.
      - subst ef. cbn [is_commit_event] in Hcef. contradiction. }
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: sourced_read_snoc Hlt (Hhbc n). applys Hsr Hnth.
    + inverts Heq. subst n.
      forwards (kL & HkLlt & HNkL & HnclL & HnwL):
        (>> flush_last_write HwfR HplayR HNfw HNef Hgtef Hcef Hgw).
      forwards HkLib: Nth_inbound HNkL.
      asserts HNcc'': (LibList.Nth (length log) (CH & c'') c'').
      { apply Nth_app_r' with (m := 0); [ apply Nth_zero | rew_list; nat_math ]. }
      exists kL tw. splits.
      * exact HNkL.
      * intros Hhb0. forwards Hlt: hb_lt Hhb0. nat_math.
      * (* Maximality *)
        introv (m' & t'' & v' & Hneq & Hmth' & Hhb & Hhb').
        asserts Hcm'commit: (is_commit_event (event_write t'' x0 v')). { simpl. exact HxVol. }
        forwards Hm'lt: Nth_inbound Hmth'.
        asserts Hm'lenCH: (m' < length (CH & c'')).
        { forwards Hlen: play_log_CH_length HplayR. rewrite Hlen. nat_math. }
        forwards (cf & HNcf): Nth_inbound_inv Hm'lenCH.
        forwards Hgwf: (>> write_volatile_graph_writes HplayR HxVol Hmth' HNcf).
        forwards HancfTC: (>> hb_pointer_ancestor HwfR HplayR Hhb' HNcf HNcc'').
        destruct (classic (tw = t'')) as [Htweq | Htwne].
        -- rewrite <- Htweq in Hmth'.
           asserts HkLeqfw: (kL = fw).
           { destruct (classic (kL < fw)) as [Hlt | Hge]; [ | nat_math ].
             exfalso. applys (HnclL kL (event_write tw x0 v0) (le_refl kL) Hlt HNkL (eq_refl tw)).
             simpl. exact HxVol. }
           forwards HmL: hb_lt Hhb.
           asserts Hm'fw: (fw <= m').
           { destruct (classic (m' < fw)) as [Hlt | Hge]; [ | nat_math ].
             exfalso. applys HnwL m' v'; [ nat_math | nat_math | exact Hmth' ]. }
           asserts Hfwltm': (fw < m').
           { asserts Hm'nekL: (m' <> kL). { exact Hneq. } nat_math. }
           asserts Hgm'tw: (get_thread (event_write tw x0 v') = tw). { reflexivity. }
           asserts Hanccwcf: (ancestor G' cw cf).
           { applys~ (>> CH_thread_monotone HwfR HplayR HNef Hgtef Hmth' Hgm'tw HNfw HNcf). }
           asserts Hcfne: (cf <> cw).
           { intro Heqc. subst cf.
             forwards Heqpos: (>> CH_commit_event_inj HplayR HNcf Hmth' Hcm'commit HNfw HNef Hcef).
             nat_math. }
           forwards Heqcf: (>> Hmax cf v' Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
        -- asserts HA: (LibList.Nth kL (log & event_read t0 x0 v0) (event_write tw x0 v0) /\
                        LibList.Nth fw (CH & c'') cw /\
                        LibList.Nth fw (log & event_read t0 x0 v0) ef /\
                        get_thread ef = tw /\ is_commit_event ef /\ kL <= fw /\
                        (forall p ep, kL <= p -> p < fw -> LibList.Nth p (log & event_read t0 x0 v0) ep ->
                                      get_thread ep = tw -> ~ is_commit_event ep)).
           { splits*. }
           asserts HB: (LibList.Nth m' (log & event_read t0 x0 v0) (event_write t'' x0 v') /\
                        LibList.Nth m' (CH & c'') cf /\
                        LibList.Nth m' (log & event_read t0 x0 v0) (event_write t'' x0 v') /\
                        get_thread (event_write t'' x0 v') = t'' /\
                        is_commit_event (event_write t'' x0 v') /\ m' <= m').
           { splits*. }
           asserts Hanccwcf: (ancestor G' cw cf).
           { applys (>> write_hb_flush_ancestor HwfR HplayR HA HB Htwne Hhb). }
           asserts Hcfne: (cf <> cw).
           { intro Heqc. subst cf.
             forwards Heqpos: (>> CH_commit_event_inj HplayR HNcf Hmth' Hcm'commit HNfw HNef Hcef).
             subst m'. forwards Heqe: Nth_functional HNef Hmth'.
             rewrite Heqe in Hgtef. cbn [get_thread] in Hgtef.
             applys Htwne. symmetry. exact Hgtef. }
           forwards Heqcf: (>> Hmax cf v' Hgwf Hanccwcf HancfTC).
           applys Hcfne Heqcf.
Qed.

(* A commit-event witness is never [root_commit]: [root_commit] is present
   from the very first (empty) graph, hence never [commit_fresh], but every
   commit event's own recorded commit is [commit_fresh] w.r.t. the graph
   right before it. *)
Lemma is_commit_event_pos_ne_root :
  forall log D TC G LC VC CH k c e,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth k CH c -> LibList.Nth k log e -> is_commit_event e ->
    c <> root_commit.
Proof.
  introv Hplay. gen k c e.
  inductions Hplay; introv HNch HNlog Hce.
  - forwards*: Nth_nil_inv HNch.
  - forwards Hlen: play_log_CH_length Hplay.
    forwards [HNch0 | (HkN & Hcx)]: Nth_last_inv HNch.
    + forwards [HNlog0 | (HkN' & HeE)]: Nth_last_inv HNlog.
      * applys (IHHplay D' TC' G' LC' VC' eq_refl eq_refl k c e HNch0 HNlog0 Hce).
      * forwards Hib: Nth_inbound HNch0. nat_math.
    + forwards [HNlog0 | (HkN' & HeE)]: Nth_last_inv HNlog.
      * forwards Hib: Nth_inbound HNlog0. nat_math.
      * subst e. intro Heqroot. subst c.
        forwards (Hfr & _): play_event_commit_new H Hce.
        rewrite Heqroot in Hfr.
        forwards Hpgwf: play_log_graph_wf Hplay.
        destruct Hpgwf as (_ & _ & _ & _ & Hrootin).
        applys commit_fresh_not_indom Hfr Hrootin.
Qed.



(* [lc_read]'s companion to [vc_read_graph_indom]: a lock's stored commit
   (or [root_commit], if never taken) is always graph-indom. *)
Lemma lc_read_graph_indom :
  forall D TC G LC VC CH log l,
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    graph_indom G (lc_read LC l).
Proof.
  introv Hplay.
  forwards Hpgwf: play_log_graph_wf Hplay.
  destruct Hpgwf as (_ & _ & HLC & _ & Hroot).
  unfold lc_read. destruct (classic (l \indom LC)) as [Hindom|Hnotin].
  - rewrite (read_default_indom Hindom). applys* HLC.
  - rewrite (read_default_notindom Hnotin). exact Hroot.
Qed.

(* The acting thread of an event that carries no [binds TC _ _] premise of its
   own (only [PlayRead]/[PlayWrite]/[PlayStart]) is still indom [TC]: it must
   already have been spawned (or be root), by [wf_log]'s program-order
   discipline, and [log_thread_indom_TC] turns that into TC-membership. The
   side condition rules out the (vacuous, for these three event shapes) case
   where [E] would itself be the very spawn event of its own acting thread. *)
Lemma play_event_self_indom_TC :
  forall log0 E D' TC' G' LC' VC' CH0,
    wf_log (log0 & E) ->
    play_log log0 init_play_cfg (D', TC', G', LC', VC') CH0 ->
    (forall t1, E <> event_spawn t1 (get_thread E)) ->
    get_thread E \indom TC'.
Proof.
  introv Hwf Hplay Hne.
  forwards Hwf0: wf_log_last_inv Hwf.
  asserts Hmem: (mem E (log0 & E)). { rewrite mem_last_eq. right. reflexivity. }
  forwards Hgtr: event_thread_spawned_or_root Hwf Hmem (eq_refl (get_thread E)).
  destruct Hgtr as [(t1 & Hmemsp) | Hroot].
  - rewrite mem_last_eq in Hmemsp. destruct Hmemsp as [Hmemsp | Heq].
    + applys log_thread_indom_TC Hwf0 Hplay. left. exists t1. exact Hmemsp.
    + exfalso. applys (Hne t1). symmetry. exact Heq.
  - applys log_thread_indom_TC Hwf0 Hplay. right. exact Hroot.
Qed.

(* The "self" recursion step shared by every [play_event] case whose target
   pointer is the acting thread's OWN prior commit [TC'[get_thread E]]
   (carried forward unchanged by Read/Write/Start, or consumed as one merge
   /commit parent by ReadVolatile/WriteVolatile/Lock/Unlock/End/Spawn/Join):
   chase [TC'[get_thread E]] back to its own witness position via
   [tc_read_pointer], recurse there via the (curried) induction hypothesis,
   then bridge forward to [E]'s own position ([length log0]) by plain program
   order ([resolve_witness_hb], since the witness is owned by [get_thread E]
   itself, or its spawn). *)
Lemma ancestor_tc_self_hb :
  forall log0 E D' TC' G' LC' VC' CH0 ka a ea,
    wf_log (log0 & E) ->
    play_log log0 init_play_cfg (D', TC', G', LC', VC') CH0 ->
    LibList.Nth ka CH0 a -> LibList.Nth ka log0 ea -> is_commit_event ea ->
    (forall kb0 b0 eb0,
        LibList.Nth kb0 CH0 b0 -> LibList.Nth kb0 log0 eb0 ->
        ancestor G' a b0 -> ka = kb0 \/ hb log0 ka kb0) ->
    get_thread E \indom TC' ->
    ancestor G' a (TC'[get_thread E]) ->
    hb (log0 & E) ka (length log0).
Proof.
  introv Hwf Hplay HNcha HNloga Hcea IH Htin Hanc.
  asserts HNEapp: (LibList.Nth (length log0) (log0 & E) E).
  { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
  forwards [Hrt | (k' & ek' & HNk' & HNk'ch & Hdisj)]: tc_read_pointer Hplay Htin.
  - exfalso. unfold commit in *. rewrite Hrt in Hanc.
    forwards Heqa: ancestor_into_root Hplay Hanc.
    applys is_commit_event_pos_ne_root Hplay HNcha HNloga Hcea Heqa.
  - forwards HNk'app: Nth_app_l HNk'.
    forwards Hk'lt: Nth_inbound HNk'.
    forwards Hhbend: (>> resolve_witness_hb Hwf HNk'app Hdisj HNEapp (eq_refl (get_thread E)) Hk'lt).
    forwards Hkeq: (>> IH k' (TC'[get_thread E]) ek' HNk'ch HNk' Hanc).
    destruct Hkeq as [Heqk | Hhb].
    + rewrite Heqk. exact Hhbend.
    + forwards Hhblift: (@hb_weaken_snoc log0 E ka k' Hhb).
      applys HbTrans Hhblift Hhbend.
Qed.

(* The [graph_commit]-shaped recursion step: [a]'s ancestry into the freshly
   committed [c'] either collapses to [a = c'] (impossible: [a] is already
   graph-indom [G0], while [c'] is [commit_fresh G0]) or factors through the
   single parent [c], handled by the caller-supplied [Hself]. Conclusion [P]
   is left abstract, and [G0]'s own edge-well-formedness/[a]'s indom-ness are
   taken as EXPLICIT hypotheses (rather than derived internally from a
   [play_log] ending exactly at [G0]) so that callers with a two-layer graph
   ([PlayWriteVolatile]'s outer commit over its own inner merge) can reuse
   this for the outer layer, where [G0] is itself already an extended
   ([graph_merge]) graph, not literally [play_log]'s own end-state. *)
Lemma ancestor_commit_target_hb :
  forall G0 a c c' d (P : Prop),
    (forall x y, graph_edge G0 x y -> graph_indom G0 x /\ graph_indom G0 y) ->
    graph_indom G0 a ->
    commit_fresh G0 c' ->
    graph_indom G0 c ->
    (ancestor G0 a c -> P) ->
    ancestor (graph_commit G0 c c' d) a c' ->
    P.
Proof.
  introv Hedge Hadom Hfresh Hcin Hself Hanc.
  forwards Hdec: ancestor_graph_commit_target_inv Hedge Hfresh Hcin Hanc.
  destruct Hdec as [(_ & [Heq | Hancc]) | (Hneq & _)].
  - exfalso. rewrite Heq in Hadom. applys commit_fresh_not_indom Hfresh Hadom.
  - applys Hself Hancc.
  - exfalso. applys Hneq. reflexivity.
Qed.

(* The [graph_merge]-shaped recursion step: same shape as
   [ancestor_commit_target_hb], for a merge's two parents [p1]/[p2] instead
   of a commit's single parent. *)
Lemma ancestor_merge_target_hb :
  forall G0 a p1 p2 h (P : Prop),
    (forall x y, graph_edge G0 x y -> graph_indom G0 x /\ graph_indom G0 y) ->
    graph_indom G0 a ->
    commit_fresh G0 h ->
    graph_indom G0 p1 -> graph_indom G0 p2 ->
    (ancestor G0 a p1 -> P) ->
    (ancestor G0 a p2 -> P) ->
    ancestor (graph_merge G0 p1 p2 h) a h ->
    P.
Proof.
  introv Hedge Hadom Hfresh Hp1in Hp2in Hself1 Hself2 Hanc.
  forwards Hdec: ancestor_graph_merge_target_inv Hedge Hfresh Hp1in Hp2in Hanc.
  destruct Hdec as [(_ & [Heq | [Hancc1 | Hancc2]]) | (Hneq & _)].
  - exfalso. rewrite Heq in Hadom. applys commit_fresh_not_indom Hfresh Hadom.
  - applys Hself1 Hancc1.
  - applys Hself2 Hancc2.
  - exfalso. applys Hneq. reflexivity.
Qed.

Lemma ancestor_pos_hb :
  forall log D TC G LC VC CH ka a ea kb b eb,
    wf_log log ->
    play_log log init_play_cfg (D, TC, G, LC, VC) CH ->
    LibList.Nth ka CH a -> LibList.Nth ka log ea -> is_commit_event ea ->
    LibList.Nth kb CH b -> LibList.Nth kb log eb ->
    ancestor G a b ->
    ka = kb \/ hb log ka kb.
Proof.
  introv Hwf Hplay. gen ka a ea kb b eb.
  inductions Hplay; introv HNcha HNloga Hcea HNchb HNlogb Hanc.
  - false. applys Nth_nil_inv HNloga.
  - rename H into Hpe.
    forwards Hwf0: wf_log_last_inv Hwf.
    forwards Hpgwf: play_log_graph_wf Hplay.
    destruct Hpgwf as (Hedge & HTCin & HLCin & HVCin & Hrootin).
    forwards Hlen: play_log_CH_length Hplay.
    forwards [HNchb0 | (HkbN & Hcxb)]: Nth_last_inv HNchb.
    + (* [b]'s witness lies in the smaller prefix: peel [Hanc] back through
         [Hpe] via [play_event_ancestor_inv] (needs [graph_indom G' b], from
         [CH_indom]), then recurse. If [a]'s own witness is instead the fresh
         commit of THIS step, that is a contradiction: [a] would be
         [commit_fresh G'] (via [play_event_commit_new]) while also being
         [graph_indom G' a] (via [ancestor_src_indom] on [Hanc'], since [b]
         is old) -- mirrors the two [exfalso] branches of the "b old, a
         fresh" case in [ancestor_creation_order] exactly. *)
      forwards [HNlogb0 | (HkbN' & HeEb)]: Nth_last_inv HNlogb.
      2:{ forwards Hib: Nth_inbound HNchb0. nat_math. }
      forwards Hbdom: CH_indom Hwf0 Hplay HNchb0.
      forwards Hanc': (>> play_event_ancestor_inv Hpe Hedge HTCin HVCin Hrootin Hbdom Hanc).
      forwards [HNcha0 | (HkaN & Hcxa)]: Nth_last_inv HNcha.
      2:{ forwards Hdisj: ancestor_src_indom Hedge Hanc'.
          asserts Hain: (graph_indom G' a).
          { destruct Hdisj as [Hain | Haeq]; [ exact Hain | rewrite Haeq; exact Hbdom ]. }
          forwards Hla: Nth_last_inv HNloga.
          destruct Hla as [HNloga0 | (HkaN'' & HeEa)].
          { forwards Hib: Nth_inbound HNloga0. nat_math. }
          subst ea. forwards (Hfa & _): play_event_commit_new Hpe Hcea.
          rewrite Hcxa in Hfa. exfalso. applys commit_fresh_not_indom Hfa Hain. }
      forwards Hla: Nth_last_inv HNloga.
      destruct Hla as [HNloga0 | (HkaN'' & HeEa)].
      2:{ forwards Hib: Nth_inbound HNcha0. nat_math. }
      destruct (IHHplay D' TC' G' LC' VC' Hwf0 eq_refl eq_refl ka a ea kb b eb HNcha0 HNloga0 Hcea HNchb0 HNlogb0 Hanc') as [Heq | Hhb].
      * left. exact Heq.
      * right. applys* hb_weaken_snoc.
    + (* [b] is exactly this step's own recorded pointer,
         [TC''[get_thread E]]. Case on [Hpe]:
         - PlayRead/PlayWrite/PlayStart (no graph change, [b] merely
           CARRIES FORWARD [TC'[get_thread E]] from the prefix, not
           necessarily anything freshly created here): apply
           [tc_read_pointer] to [get_thread E] within the prefix. If it
           returns [root_commit], get [a = root_commit] via
           [ancestor_into_root], then contradict via [is_commit_event ea]
           (root is graph-indom from the very start, so it can never be
           [commit_fresh], but [play_event_commit_new] would need it to be,
           applied at whatever step actually created [a] -- need a small
           inline argument, or reuse the "a fresh at [ka]" contradiction
           machinery from the [b old] branch's second half applied with
           [b := root_commit] treated as an "old" (indom-from-the-start)
           target). If it returns a witness [(kb', eb', ...)], recurse via
           IHHplay (target [kb', eb', TC'[get_thread E]], same [G'] since
           unchanged) to get [ka = kb' \/ hb log ka kb'], then bridge
           [kb'] (or [ka], if the disjunct was the equality) forward to
           [length log] with [resolve_witness_hb] (using [get_thread E] as
           the destination thread, [p := length log], [ep := E], trivially
           [get_thread E = get_thread E]), composing with [HbTrans]/
           [hb_weaken_snoc] as needed.
         - PlayReadVolatile/PlayLock/PlayJoin (a merge: two parents, [c] the
           puller's own prior pointer and [vc_read VC' x]/[lc_read LC'
           l]/[TC'[t2]] the other party's stored pointer): apply
           [ancestor_graph_merge_target_inv] to [Hanc] (needs
           [graph_indom G' c]/[commit_fresh G' c'']/etc, all from [HTCin]/
           the constructor's own [binds] premise). The ["a = fresh"] disjunct
           is [false] the same way as above ([a] would need to be both
           [commit_fresh] and [graph_indom G'], via [ancestor_src_indom]
           applied one level further back -- actually simpler here: [a] is
           [is_commit_event]-witnessed, and merges are never
           [is_commit_event], so if [ka] = this step's own position that is
           immediately [false] via [Hcea]; if [ka] is in the prefix, [a] is
           [graph_indom G'] while the fresh merge commit is not, contra).
           The "self" parent [c] recurses via [tc_read_pointer] (SAME
           thread) + IHHplay + [resolve_witness_hb] exactly as above. The
           "other" parent recurses via [lc_read_pointer]/[vc_read_pointer]
           (for Lock/Volatile; for Join, [TC'[t2]] needs [tc_read_pointer]
           applied to [t2], NOT a new lemma) + IHHplay, then bridges to
           [length log] with ONE more hop -- [HbLock]/[HbVolatile]/[HbJoin]
           respectively -- composed with [HbTrans] onto whatever
           [resolve_witness_hb]-chain got us from the parent's own witness
           to ITS flush position (mirroring [hb_lock_pointer_ancestor] et
           al.'s case split, but assembling an actual [hb] witness instead
           of consuming one).
         - PlayEnd/PlaySpawn/PlayUnlock/PlayWriteVolatile (a commit, or two
           layers for PlayWriteVolatile: single "self" parent [c], the
           pusher's own prior pointer): apply
           [ancestor_graph_commit_target_inv] (twice, nested, for
           PlayWriteVolatile) to [Hanc]; the ["a = fresh"] disjunct is
           [false] the same way; the "self" parent recurses via
           [tc_read_pointer] + IHHplay + [resolve_witness_hb] exactly as
           above (for PlaySpawn, this sources [t1]'s history, which
           correctly ends up bridging to the spawn event itself regardless
           of whether the ORIGINAL query concerned [t1] or the freshly
           spawned [t2], since [b] here is a bare COMMIT VALUE, not tied to
           either thread's identity). *)
      destruct (classic (ka = kb)) as [Heqk | Hkn]; [ left; exact Heqk | right ].
      forwards [HNcha0 | (HkaN & Hcxa)]: Nth_last_inv HNcha.
      2:{ exfalso. applys Hkn. rewrite HkaN. symmetry. exact HkbN. }
      forwards [HNloga0 | (HkaN' & HeEa)]: Nth_last_inv HNloga.
      2:{ forwards Hib: Nth_inbound HNcha0. nat_math. }
      subst b.
      rewrite HkbN, Hlen.
      asserts IH: (forall kb0 b0 eb0,
          LibList.Nth kb0 CH b0 -> LibList.Nth kb0 log eb0 ->
          ancestor G' a b0 -> ka = kb0 \/ hb log ka kb0).
      { introv H1 H2 H3.
        exact (IHHplay D' TC' G' LC' VC' Hwf0 eq_refl eq_refl ka a ea kb0 b0 eb0 HNcha0 HNloga0 Hcea H1 H2 H3). }
      inverts Hpe.
      * (* PlayRead *)
        asserts Hnesp: (forall t1, event_read t x v <> event_spawn t1 t).
        { introv Heq. discriminate. }
        forwards Htin: play_event_self_indom_TC Hwf Hplay Hnesp.
        applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hanc).
      * (* PlayReadVolatile *)
        match goal with Hb : binds TC' _ _ |- _ => rename Hb into Hbc end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        match goal with Hv : x \in Volatiles |- _ => rename Hv into Hxvol end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hp1in: (graph_indom G' (vc_read VC x)). { applys vc_read_graph_indom Hplay; typeclass. }
        asserts Hp2in: (graph_indom G' c). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hself1: (ancestor G' a (vc_read VC x) ->
                          hb (log & event_read t x v) ka (length log)).
        { intro Hancx.
          forwards [Hvrt | (kw & tw & vw & HNkw & HNkwch)]: vc_read_pointer Hplay.
          - exfalso. unfold commit in *. rewrite Hvrt in Hancx.
            forwards Heqa: ancestor_into_root Hplay Hancx.
            applys is_commit_event_pos_ne_root Hplay HNcha0 HNloga0 Hcea Heqa.
          - forwards Hkeq: (>> IH kw (vc_read VC x) (event_write tw x vw) HNkwch HNkw Hancx).
            forwards HNkwapp: Nth_app_l HNkw.
            asserts HNEapp: (LibList.Nth (length log) (log & event_read t x v) (event_read t x v)).
            { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
            forwards Hkwlt: Nth_inbound HNkw.
            asserts Hacc: (accesses_variable x (event_read t x v)). { reflexivity. }
            forwards Hhbvol: (>> HbVolatile Hxvol HNkwapp HNEapp Hacc Hkwlt).
            destruct Hkeq as [Heqk' | Hhb].
            + rewrite Heqk'. exact Hhbvol.
            + forwards Hhblift: (@hb_weaken_snoc log (event_read t x v) ka kw Hhb).
              applys HbTrans Hhblift Hhbvol. }
        asserts Hself2: (ancestor G' a c -> hb (log & event_read t x v) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_merge_target_hb Hedge Hadom Hfresh Hp1in Hp2in Hself1 Hself2 Hanc).
      * (* PlayWrite *)
        asserts Hnesp: (forall t1, event_write t x v <> event_spawn t1 t).
        { introv Heq. discriminate. }
        forwards Htin: play_event_self_indom_TC Hwf Hplay Hnesp.
        applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hanc).
      * (* PlayWriteVolatile: two layers -- outer [graph_commit] over the
           inner [graph_merge]; the outer's own parent is the inner merge's
           fresh target [c'], so the outer combinator's [Hself] IS the
           inner decomposition. *)
        match goal with Hv0 : x \in Volatiles |- _ => rename Hv0 into Hxvol end.
        match goal with Hb0 : binds D' _ _ |- _ => rename Hb0 into Hbd end.
        match goal with Hb1 : binds TC' _ _ |- _ => rename Hb1 into Hbc end.
        match goal with Hf0 : commit_fresh G' _ |- _ => rename Hf0 into Hfresh1 end.
        match goal with Hf1 : commit_fresh (graph_merge _ _ _ _) _ |- _ => rename Hf1 into Hfresh2 end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hp1in: (graph_indom G' (vc_read VC' x)). { applys vc_read_graph_indom Hplay. }
        asserts Hp2in: (graph_indom G' c). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hmwf: (graph_indom (graph_merge G' (vc_read VC' x) c c') c').
        { applys graph_merge_indom_same. }
        asserts Hself1: (ancestor G' a (vc_read VC' x) ->
                          hb (log & event_write t x v) ka (length log)).
        { intro Hancx.
          forwards [Hvrt | (kw & tw & vw & HNkw & HNkwch)]: vc_read_pointer Hplay.
          - exfalso. unfold commit in *. rewrite Hvrt in Hancx.
            forwards Heqa: ancestor_into_root Hplay Hancx.
            applys is_commit_event_pos_ne_root Hplay HNcha0 HNloga0 Hcea Heqa.
          - forwards Hkeq: (>> IH kw (vc_read VC' x) (event_write tw x vw) HNkwch HNkw Hancx).
            forwards HNkwapp: Nth_app_l HNkw.
            asserts HNEapp: (LibList.Nth (length log) (log & event_write t x v) (event_write t x v)).
            { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
            forwards Hkwlt: Nth_inbound HNkw.
            asserts Hacc: (accesses_variable x (event_write t x v)). { reflexivity. }
            forwards Hhbvol: (>> HbVolatile Hxvol HNkwapp HNEapp Hacc Hkwlt).
            destruct Hkeq as [Heqk' | Hhb].
            + rewrite Heqk'. exact Hhbvol.
            + forwards Hhblift: (@hb_weaken_snoc log (event_write t x v) ka kw Hhb).
              applys HbTrans Hhblift Hhbvol. }
        asserts Hself2: (ancestor G' a c -> hb (log & event_write t x v) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        asserts HselfMerge: (ancestor (graph_merge G' (vc_read VC' x) c c') a c' ->
                              hb (log & event_write t x v) ka (length log)).
        { intro Hancc'.
          applys (>> ancestor_merge_target_hb Hedge Hadom Hfresh1 Hp1in Hp2in Hself1 Hself2 Hancc'). }
        asserts HadomMerge: (graph_indom (graph_merge G' (vc_read VC' x) c c') a).
        { applys graph_merge_indom Hadom. }
        asserts HedgeMerge:
          (forall x0 y0, graph_edge (graph_merge G' (vc_read VC' x) c c') x0 y0 ->
                         graph_indom (graph_merge G' (vc_read VC' x) c c') x0 /\
                         graph_indom (graph_merge G' (vc_read VC' x) c c') y0).
        { forwards HwfgG': play_log_wf_graph Hplay.
          forwards HwfgM: graph_merge_wf HwfgG' Hfresh1 Hp1in Hp2in.
          destruct HwfgM as (_ & _ & HedgeM). exact HedgeM. }
        applys (>> ancestor_commit_target_hb HedgeMerge HadomMerge Hfresh2 Hmwf HselfMerge Hanc).
      * (* PlayStart *)
        asserts Hnesp: (forall t1, event_start t <> event_spawn t1 t).
        { introv Heq. discriminate. }
        forwards Htin: play_event_self_indom_TC Hwf Hplay Hnesp.
        applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hanc).
      * (* PlayEnd *)
        match goal with Hb : binds TC' _ _ |- _ => rename Hb into Hbc end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hcin: (graph_indom G' c). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hself: (ancestor G' a c -> hb (log & event_end t) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_commit_target_hb Hedge Hadom Hfresh Hcin Hself Hanc).
      * (* PlaySpawn *)
        match goal with Hb : binds TC' _ _ |- _ => rename Hb into Hbc end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        cbn [get_thread] in Hanc.
        asserts HTCeq: (TC'[t1 := c'][t2 := c'][t1] = c').
        { destruct (classic (t1 = t2)) as [-> | Hne].
          - rewrite read_update_same. reflexivity.
          - rewrite read_update_neq; [ | congruence ]. rewrite read_update_same. reflexivity. }
        rewrite HTCeq in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hcin: (graph_indom G' c). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hself: (ancestor G' a c -> hb (log & event_spawn t1 t2) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_commit_target_hb Hedge Hadom Hfresh Hcin Hself Hanc).
      * (* PlayJoin *)
        match goal with Hb1 : binds TC' t1 _ |- _ => rename Hb1 into Hbc1 end.
        match goal with Hb2 : binds TC' t2 _ |- _ => rename Hb2 into Hbc2 end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin1: (indom_of_binds Hbc1).
        asserts Hp2in: (graph_indom G' c1). { rewrite <- (read_of_binds Hbc1). applys HTCin Htin1. }
        lets Htin2: (indom_of_binds Hbc2).
        asserts Hp1in: (graph_indom G' c2). { rewrite <- (read_of_binds Hbc2). applys HTCin Htin2. }
        asserts Hself2: (ancestor G' a c1 -> hb (log & event_join t1 t2) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc1) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin1 Hancc). }
        asserts Hself1: (ancestor G' a c2 -> hb (log & event_join t1 t2) ka (length log)).
        { intro Hancc.
          lets (_ & _ & _ & Hjoin & _): Hwf.
          forwards Hmemend: Hjoin log (@nil event) t1 t2
            (eq_refl : log & event_join t1 t2 = log ++ event_join t1 t2 :: nil).
          forwards (m & HNm): mem_Nth Hmemend.
          forwards Hmlt: Nth_inbound HNm.
          asserts Hmlt': (m < length CH). { rewrite Hlen. exact Hmlt. }
          forwards (cm & HNmch): Nth_inbound_inv Hmlt'.
          forwards Hbcm: ended_thread_pointer Hwf0 Hplay HNm HNmch.
          lets Heqcm: (binds_inj Hbcm Hbc2).
          subst cm.
          forwards Hkeq: (>> IH m c2 (event_end t2) HNmch HNm Hancc).
          forwards HNmapp: Nth_app_l HNm.
          asserts HNEapp: (LibList.Nth (length log) (log & event_join t1 t2) (event_join t1 t2)).
          { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
          forwards Hhbjoin: (>> HbJoin HNmapp HNEapp Hmlt).
          destruct Hkeq as [Heqk' | Hhb].
          - rewrite Heqk'. exact Hhbjoin.
          - forwards Hhblift: (@hb_weaken_snoc log (event_join t1 t2) ka m Hhb).
            applys HbTrans Hhblift Hhbjoin. }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_merge_target_hb Hedge Hadom Hfresh Hp1in Hp2in Hself1 Hself2 Hanc).
      * (* PlayLock *)
        match goal with Hb : binds TC' _ _ |- _ => rename Hb into Hbc end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hp1in: (graph_indom G' (lc_read LC l0)). { applys lc_read_graph_indom Hplay. }
        asserts Hp2in: (graph_indom G' c1). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hself1: (ancestor G' a (lc_read LC l0) ->
                          hb (log & event_lock t l0) ka (length log)).
        { intro Hancx.
          forwards [Hlrt | (kw & tw & HNkw & HNkwch)]: lc_read_pointer Hplay.
          - exfalso. unfold commit in *. rewrite Hlrt in Hancx.
            forwards Heqa: ancestor_into_root Hplay Hancx.
            applys is_commit_event_pos_ne_root Hplay HNcha0 HNloga0 Hcea Heqa.
          - forwards Hkeq: (>> IH kw (lc_read LC l0) (event_unlock tw l0) HNkwch HNkw Hancx).
            forwards HNkwapp: Nth_app_l HNkw.
            asserts HNEapp: (LibList.Nth (length log) (log & event_lock t l0) (event_lock t l0)).
            { applys Nth_app_r'; [ applys Nth_zero | rew_list; nat_math ]. }
            forwards Hkwlt: Nth_inbound HNkw.
            forwards Hhblock: (>> HbLock HNkwapp HNEapp Hkwlt).
            destruct Hkeq as [Heqk' | Hhb].
            + rewrite Heqk'. exact Hhblock.
            + forwards Hhblift: (@hb_weaken_snoc log (event_lock t l0) ka kw Hhb).
              applys HbTrans Hhblift Hhblock. }
        asserts Hself2: (ancestor G' a c1 -> hb (log & event_lock t l0) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_merge_target_hb Hedge Hadom Hfresh Hp1in Hp2in Hself1 Hself2 Hanc).
      * (* PlayUnlock *)
        match goal with Hb : binds TC' _ _ |- _ => rename Hb into Hbc end.
        match goal with Hf : commit_fresh G' _ |- _ => rename Hf into Hfresh end.
        cbn [get_thread] in Hanc. rewrite read_update_same in Hanc.
        lets Htin: (indom_of_binds Hbc).
        asserts Hcin: (graph_indom G' c). { rewrite <- (read_of_binds Hbc). applys HTCin Htin. }
        asserts Hself: (ancestor G' a c -> hb (log & event_unlock t l0) ka (length log)).
        { intro Hancc. rewrite <- (read_of_binds Hbc) in Hancc.
          applys (>> ancestor_tc_self_hb Hwf Hplay HNcha0 HNloga0 Hcea IH Htin Hancc). }
        forwards Hadom: CH_indom Hwf0 Hplay HNcha0.
        applys (>> ancestor_commit_target_hb Hedge Hadom Hfresh Hcin Hself Hanc).
Qed.

(* ===========================================================================
   A strictly stronger property than [no_thin_air]: every read's source write
   actually [hb]-precedes it (not merely "not hb-after it, with no closer
   candidate in between"). This is FALSE for [Linear] (an unrelated
   synchronisation action can advance a thread's pointer past a write with no
   hb edge to it), but holds for [Branching] because a thread's commit
   pointer only ever advances along graph ancestry, and graph ancestry always
   corresponds to an [hb] edge ([ancestor_pos_hb], above). This is
   UNCONDITIONAL (no [conflict_free]): [HbVolatile] orders a volatile write
   before every later ACCESS of it (read or write, not just a read -- a
   volatile write is itself a read-modify-write, pulling in the current
   stored commit before pushing its own), which is exactly the edge
   [ancestor_pos_hb] needs to bridge a graph-ancestor volatile write forward
   to the position doing the pulling, whether that position is a read or
   (for [PlayWriteVolatile], inside [ancestor_pos_hb]'s own proof) a write.

   The eight non-read steps reduce to [hb_sourced_snoc_nonread]. The three
   read steps show the freshly appended read is [hb]-sourced:
     - StepReadLocal:  source is [t]'s own last uncommitted x-write; [hb] by
       plain program order (same thread).
     - StepReadGlobal: source is the last write [kL] feeding the flush [fw] of
       the [is_latest_value] ancestor [cw] of [TC[t]]. [ancestor_pos_hb] turns
       [ancestor G cw TC[t]] into [hb log fw k] where [k] witnesses [TC[t]]
       ([tc_read_pointer]); chain [kL <= fw] and [k] to the read itself via
       [resolve_witness_hb].
     - StepReadVolatile: same shape, but everything lives in the already-
       extended play (graph + log both include the read), so the [TC[t]]
       witness step is unnecessary: the read's own freshly merged commit
       [c''] is directly the [b]-witness for [ancestor_pos_hb].
   =========================================================================== *)

Theorem step_preserves_hb_sourced :
  forall cfg cfg' log log',
    wf_log log ->
    describes log cfg ->
    step (cfg, log) (cfg', log') ->
    hb_sourced log ->
    hb_sourced log'.
Proof.
  introv Hwf Hdesc Hstep Hhs.
  inverts Hstep;
    try (applys hb_sourced_snoc_nonread Hhs; intros; discriminate).
  - (* StepReadLocal: source is [t]'s own last uncommitted write [D[t][x]];
       [hb] by program order (same thread, [m < length log]). *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, ?dd, _), Hd : binds ?dd _ _ |- _ =>
        rename Hb into HbT; rename Hd into Hbd
    end.
    destruct Hdesc as (_ & _ & _ & _ & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    forwards HtinD: HdomD HtinT.
    forwards (m & HNm & Hunc & Hnw): delta_last_uncommitted_write Hplay HtinD Hbd.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: hb_sourced_read_snoc Hlt (Hhs n). applys Hsr Hnth.
    + inverts Heq. subst n.
      forwards Hmlt: Nth_inbound HNm.
      forwards HNmapp: Nth_app_l HNm.
      exists m t0. split.
      * exact HNmapp.
      * applys HbPo HNmapp Hnth; [ reflexivity | exact Hmlt ].
  - (* StepReadGlobal: source is the last write [kL] feeding the flush [fw] of
       the [is_latest_value] ancestor [cw] of [TC[t0]]. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, _, ?cc), Hl : is_latest_value _ ?cc _ _ |- _ =>
        rename Hb into HbT; rename Hl into Hlv
    end.
    destruct Hdesc as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT Hbd'. inverts Heqt.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    forwards (fw & ef & tw & kw & HNfw & HNef & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush Hplay Hgw.
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: hb_sourced_read_snoc Hlt (Hhs n). applys Hsr Hnth.
    + inverts Heq. subst n.
      forwards (kL & HkLlt & HNkL & HnclL & HnwL):
        (>> flush_last_write Hwf Hplay HNfw HNef Hgtef Hcef Hgw).
      exists kL tw. split.
      * applys Nth_app_l HNkL.
      * (* [kL] --(same thread [tw], program order)--> [fw]
           --([ancestor_pos_hb] on [Hanc : ancestor G cw TC[t0]])--> [TC[t0]]'s
           witness position [k] --([resolve_witness_hb])--> the read. *)
        forwards (HstartT & HnoendT): (proj2 (Hrun t0)).
        { exists (te_exp e) D[t0] TC[t0]. exact HbT. }
        forwards HwfR: wf_log_read_last HstartT HnoendT Hwf.
        forwards HtinTC: HdomTC HtinT.
        forwards [HTCroot | (k & ek & HNk & HNkCH & Hdisj)]: tc_read_pointer Hplay HtinTC.
        -- (* [TC[t0] = root_commit] is impossible: it would force [cw] itself
              to be [root_commit] ([ancestor_into_root]), contradicting that
              [cw] is witnessed by the genuine commit event [ef]
              ([is_commit_event_pos_ne_root]). *)
           exfalso.
           unfold commit in *.
           rewrite HTCroot in Hanc.
           forwards Heqcw: ancestor_into_root Hplay Hanc.
           applys is_commit_event_pos_ne_root Hplay HNfw HNef Hcef Heqcw.
        -- forwards HNkapp: Nth_app_l HNk.
           forwards Hklt: Nth_inbound HNk.
           forwards Hhbkn: (>> resolve_witness_hb HwfR HNkapp Hdisj Hnth (eq_refl t0) Hklt).
           forwards Hkeq: (>> ancestor_pos_hb Hwf Hplay HNfw HNef Hcef HNkCH HNk Hanc).
           destruct Hkeq as [Heqfk | Hhbfk].
           ++ rewrite <- Heqfk in Hhbkn.
              destruct (classic (kL = fw)) as [-> | Hne].
              ** exact Hhbkn.
              ** asserts HkLltfw: (kL < fw). { nat_math. }
                 forwards HNkLapp: Nth_app_l HNkL.
                 forwards HNfwapp: Nth_app_l HNef.
                 asserts Hhbklfw: (hb (log & event_read t0 x0 v0) kL fw).
                 { applys HbPo HNkLapp HNfwapp; [ cbn [get_thread]; congruence | exact HkLltfw ]. }
                 applys HbTrans Hhbklfw Hhbkn.
           ++ forwards HNkLapp: Nth_app_l HNkL.
              forwards HNfwapp: Nth_app_l HNef.
              forwards Hhbfk': (@hb_weaken_snoc log (event_read t0 x0 v0) fw k Hhbfk).
              destruct (classic (kL = fw)) as [-> | Hne].
              ** applys HbTrans Hhbfk' Hhbkn.
              ** asserts HkLltfw: (kL < fw). { nat_math. }
                 asserts Hhbklfw: (hb (log & event_read t0 x0 v0) kL fw).
                 { applys HbPo HNkLapp HNfwapp; [ cbn [get_thread]; congruence | exact HkLltfw ]. }
                 asserts Hhbfkn: (hb (log & event_read t0 x0 v0) fw (length log)).
                 { applys HbTrans Hhbfk' Hhbkn. }
                 applys HbTrans Hhbklfw Hhbfkn.
  - (* StepReadVolatile: same shape, but entirely within the already-extended
       play [HplayR] (graph [G'] and log [log & read] both already include
       the read), so the read's own freshly merged commit [c''] is directly
       the [b]-witness for [ancestor_pos_hb] -- no separate [TC] lookup. *)
    match goal with
    | Hb : binds _ _ (state_running, te_exp _, _, ?cc), Hl : is_latest_value _ ?cc _ _ |- _ =>
        rename Hb into HbT; rename Hl into Hlv
    end.
    match goal with
    | Hb0 : binds T t (state_running, te_exp _, _, ?cc0) |- _ => rename Hb0 into HbT0
    end.
    match goal with Hxvol0 : x \in Volatiles |- _ => rename Hxvol0 into HxVol end.
    match goal with Hfr0 : commit_fresh G c'' |- _ => rename Hfr0 into Hfresh end.
    destruct Hdesc as (_ & _ & _ & Hrun & _ & _ &
      (D & TC & LC & VC & CH & Hplay & Hdelta & Hlocks & Hveq & HdomD & HdomTC & HdomLC)).
    lets HtinT: (indom_of_binds HbT0).
    forwards (st' & e'' & Hbd'): Hdelta HtinT.
    forwards~ Heqt: binds_inj HbT0 Hbd'. inverts Heqt.
    destruct Hlv as (cw & Hgw & Hanc & Hmax).
    forwards (HstartT & HnoendT): (proj2 (Hrun t)).
    { exists (te_exp e) D[t] TC[t]. exact HbT0. }
    forwards HwfR: wf_log_read_last HstartT HnoendT Hwf.
    asserts HbTCc: (binds TC t (TC[t])).
    { applys binds_of_indom_read (HdomTC t HtinT); (reflexivity || typeclass). }
    asserts HG'eq: (G' = graph_merge G (vc_read VC x) (TC[t]) c'').
    { unfold Branching.pull_volatile, Branching.do_merge in H8.
      rewrite (read_of_binds HbT0) in H8. cbn in H8. inverts* H8.
    }
    asserts HplayR:
      (play_log (log & event_read t x v) init_play_cfg (D, TC[t := c''], G', LC, VC) (CH & c'')).
    { rewrite HG'eq.
      forwards Hpe: PlayReadVolatile HxVol HbTCc Hfresh.
      forwards Hp2: PlaySnoc Hplay Hpe.
      rewrite read_update_same in Hp2. exact Hp2. }
    forwards HlenCH0: play_log_CH_length Hplay.
    forwards (fw & ef & tw & kw & HNfw & HNef & Hgtef & Hcef & Hkwlt & HNkw & Hncl):
      graph_writes_flush HplayR Hgw.
    asserts Hfwlt: (fw < length log).
    { forwards [Hfwlt' | (HfwN & HfwE)]: Nth_last_inv HNef.
      - applys Nth_inbound Hfwlt'.
      - subst ef. cbn [is_commit_event] in Hcef. contradiction. }
    intros n t0 x0 v0 Hnth.
    forwards [Hnth' | (Hp & Heq)]: Nth_last_inv Hnth.
    + forwards Hlt: Nth_inbound Hnth'.
      forwards Hsr: hb_sourced_read_snoc Hlt (Hhs n). applys Hsr Hnth.
    + inverts Heq. subst n.
      forwards (kL & HkLlt & HNkL & HnclL & HnwL):
        (>> flush_last_write HwfR HplayR HNfw HNef Hgtef Hcef Hgw).
      asserts HNcc'': (LibList.Nth (length log) (CH & c'') c'').
      { apply Nth_app_r' with (m := 0); [ apply Nth_zero | rew_list; nat_math ]. }
      exists kL tw. split.
      * exact HNkL.
      * forwards Hkeq: (>> ancestor_pos_hb HwfR HplayR HNfw HNef Hcef HNcc'' Hnth Hanc).
        destruct Hkeq as [Heqfk | Hhbfk].
        -- exfalso. nat_math.
        -- destruct (classic (kL = fw)) as [-> | Hne].
           ++ exact Hhbfk.
           ++ asserts HkLltfw: (kL < fw). { nat_math. }
              asserts Hhbklfw: (hb (log & event_read t0 x0 v0) kL fw).
              { applys HbPo HNkL HNef; [ cbn [get_thread]; congruence | exact HkLltfw ]. }
              applys HbTrans Hhbklfw Hhbfk.
Qed.
