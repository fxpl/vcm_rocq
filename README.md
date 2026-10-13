# Version-Controlled Memory

This repository contains the Rocq mechanisation for the paper "Nothing Is Shared Until You Synchronise: Reinterpreting Java for Data-Race Freedom".

## Building

This project can be built by running `rocq makefile -f _CoqProject -o Makefile` followed by `make`.
We recommend using `make -j` to parallelise the build process.

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
| \*Consistency.v  | Proof of happens-before consistency          |
| \*EquivLemmas.v  | Helper lemmas for the equivalence proofs     |
| Logging\*Facts.v | Preservation proofs                          |
| \*Equiv.v        | Equivalence proofs                           |

In particular, the theorems and lemmas listed (or mentioned) in the paper have
the following correspondence:

| Theorem        | Mechanisation                                                                        |
|----------------|--------------------------------------------------------------------------------------|
| Logging is equivalent to non-logging semantics | `step_equiv` in Logging\*Facts.v                   |
| Theorem 5.3    | `step_preserves_wf_cfg` and `step_preserves_describes` in Logging\*Facts.v           |
| Theorem 5.4    | `step_preserves_hb_consistent` in \*Consistency.v                                    |
| Lemma 5.6      | `is_latest_value_iff_last_write` and `race_free_last_local_write` in \*EquivLemmas.v |
| Lemma 5.7      | `is_latest_value_inj` (global reads) in GraphFacts.v, local reads trivial            |
| Lemma 5.8      | `conflict_free_merge_holds` in BranchingEquivLemmas.v                                |
| Conflict checking succeeds for race-free programs in the linear model | `lin_conflict_free_holds` in LinearEquivLemmas.v |
| Conflict checking is sound | `branching_join_conflict_sound` in BranchingEquivLemmas.v                |
| Theorem 5.10   | `branching_equiv` in BranchingEquiv.v and `linear_equiv in LinearEquiv.v             |

Note that Lemma 5.6 in the paper does apply to volatile variables.
There are corresponding lemmas for volatiles in
`is_latest_value_after_volatile_pull` and
`is_latest_value_after_volatile_pull_inv` in \*EquivLemmas.v.

The file `VolatileExample.v` mechanises the execution of the
example in Figure 8.

## Branches for Variants

There are a number of branches which mechanise variants of our semantics:

- `conflicts-as-exceptions` is a variant where conflicts do not
  halt execution but throw explicit exceptions.
- `non-conflicting-volatiles` is a variant where racing writes to
  volatiles are not considered conflicting.
- `non-pulling-volatile-writes` is a variant where writing to
  volatile variables only pushes (which complicates conflict
  checking).
- `non-conflicting-non-pulling-volatile-writes` is a variant that
  combines the two branches above.