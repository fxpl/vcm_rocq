# Version-Controlled Memory

This repository contains the Rocq mechanisation for the paper "Synchronisation Is State Communication: Reinterpreting Java for Concurrency Safety".

## Building

This project can be built by running `rocq makefile -f _CoqProject -o Makefile´ followed by `make`.

It builds with Rocq 9.1.1 and depends on [TLC](https://github.com/charguer/tlc).


## Organisation

The shared definitions and proofs are organised as follows.

| File      | Contents                              |
|-----------|---------------------------------------|
| Common.v  | Common definitions and proofs         |
| Log.v     | Definitions regarding events and logs |
| Graph.v   | Definitions regarding commit graphs   |
| \*Facts.v | Theorems and proofs about \*          |

The three basic semantics and their progress proofs are in files of their own.

| File             | Contents                                     |
|------------------|----------------------------------------------|
| SharedMemory.v   | Definitions for shared memory baseline       |
| Linear.v         | Definitions for linear model                 |
| Branching.v      | Definitions for branching model              |
| \*Facts.v        | Progress proofs                              |

For the logging versions, we use the following structure.

| File             | Contents                                     |
|------------------|----------------------------------------------|
| Logging\*.v      | Logging versions of the respective semantics |
| \*OOTA.v         | Proof of absence of out-of-thin-air reads    |
| \*EquivLemmas.v  | Helper lemmas for the equivalence proofs     |
| Logging\*Facts.v | Preservation proofs                          |
| \*Equiv.v        | Equivalence proofs                           |

In particular, the theorems and lemmas listed in the paper have
the following correspondence:

| Theorem        | Mechanisation                                                              |
|----------------|----------------------------------------------------------------------------|
| Theorem 5.1    | `step_equiv` in Logging\*Facts.v                                           |
| Theorem 5.3    | `init_log_describes_init_cfg` in Logging\*Facts.v                          |
| Theorem 5.4    | `step_preserves_wf_cfg` and `step_preserves_describes` in Logging\*Facts.v |
| Theorem 5.6    | `step_preserves_no_thin_air` in \*OOTA.v                                   |
| Lemma 5.8      | `is_latest_value_iff_last_write` in \*EquivLemmas.v                        |
| Lemma 5.9      | `is_latest_value_inj` (global reads) in GraphFacts.v, local reads trivial  |
| Lemma 5.10     | `lin_conflict_free_holds` in LinearEquivLemmas.v                           |
| Lemma 5.11     | `conflict_free_merge_holds` in BranchingEquivLemmas.v                      |
| Corollary 5.12 | `branching_join_conflict_sound` in BranchingEquivLemmas.v                  |
| Theorem 5.14   | `branching_equiv` in BranchingEquiv.v and `linear_equiv in LinearEquiv.v   |
