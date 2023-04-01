# Use and abuse of instance parameters in the Lean mathematical library

This repository contains interactive full versions of the source code showcased in the paper "Use and abuse of instance parameters in the Lean mathematical library", submitted to the Journal of Automated Reasoning.

The [Lean mathematical library mathlib](https://github.com/leanprover-community/mathlib) features extensive use of the typeclass pattern for organising mathematical structures, based on Lean's mechanism of instance parameters. Related mechanisms for typeclasses are available in other provers including Agda, Coq and Isabelle with varying degrees of adoption. This paper analyses representative examples of design patterns involving instance parameters in the current Lean 3 version of mathlib, focussing on complications arising at scale and how the mathlib community deals with them.

## Installation instructions

The code showcased in the paper is based on [mathlib commit `3e068ece210`](https://github.com/leanprover-community/mathlib/tree/3e068ece210655b7b9a9477c3aff38a492400aa1), which requires the community fork of Lean 3. To install a full Lean development environment, please follow the "Regular install" instructions at https://leanprover-community.github.io/get_started.html. After installation, you can run the command `leanproject get lean-forward/mathlib-classes` to obtain copies of the source code and precompiled binaries.

When opening a Lean project in VS Code, you must use the "Open Folder" menu option to open the project's root directory. On the command line, you can run `code path/to/mathlib-classes`.

## Code overview

Each section of the paper has a corresponding source code file:
 * [Section 2: Basic instance parameters in Lean 3](src/section02_basics.lean)
 * [Section 3: `has_mul`: notation typeclass](src/section03_notation.lean)
 * [Section 4: `comm_monoid`: algebraic hierarchy class](src/section04_alg_hierarchy.lean)
 * [Section 5: `multiplicative`: multiple instances on a single type](src/section05_multiple_inst.lean)
 * [Section 6: `module`: multi-parameter classes](src/section06_multiparam.lean)
 * [Section 7: `monoid_hom_class`: generic bundled morphisms](src/section07_morphism_class.lean)
 * [Section 8: `nsmul`: ensuring equality of instances](src/section08_diamond.lean)
 * [Section 9: Instance parameters depending on out parameters](src/section09_dependent_out_param.lean)
 * [Section 10: `unique`: proof-carrying mixin](src/section10_mixin.lean)
 * [Section 11: `fact`: interfacing between instances and non-instances](src/section11_ad_hoc.lean)
 * [Section 12: Performance and bundling](src/section12_performance.lean)
 * [Section 13: Instances and tactics](src/section13_tactics.lean)
