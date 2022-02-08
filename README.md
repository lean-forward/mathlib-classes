# Use and abuse of instance parameters in the Lean mathematical library

This repository contains interactive full versions of the source code showcased in the paper "Use and abuse of instance parameters in the Lean mathematical library", submitted to ITP 2022.

The [Lean mathematical library mathlib](https://github.com/leanprover-community/mathlib) features extensive use of the typeclass pattern for organising mathematical structures, based on Lean's mechanism of instance parameters. Related mechanisms for typeclasses are available in other provers including Agda, Coq and Isabelle with varying degrees of adoption. This paper analyses representative examples of design patterns involving instance parameters in the current Lean 3 version of mathlib, focussing on complications arising at scale and how the mathlib community deals with them.

## Installation instructions

The code showcased in the paper is based on [mathlib commit `343cbd9867`](https://github.com/leanprover-community/mathlib/tree/343cbd9867), which requires the community fork of Lean 3. To install a full Lean development environment, please follow the "Regular install" instructions at https://leanprover-community.github.io/get_started.html. After installation, you can run the command `leanproject get lean-forward/mathlib-classes` to obtain copies of the source code and precompiled binaries.

When opening a Lean project in VS Code, you must use the "Open Folder" menu option to open the project's root directory. On the command line, you can run `code path/to/mathlib-classes`.

## Code overview

Each section of the paper has a corresponding source code file:
 * [Section 2: Basic instance parameters in Lean 3](src/section02_basics.lean)
 * [Section 3: `has_mul`: notation typeclass](src/section03_notation.lean)
 * [Section 4: `comm_monoid`: algebraic hierarchy class](src/section04_alg_hierarchy.lean)
 * [Section 5: `module`: multi-parameter classes](src/section05_multiparam.lean)
 * [Section 6: `monoid_hom_class`: generic bundled morphisms](src/section06_morphism_class.lean)
 * [Section 7: `nsmul`: ensuring equality of instances](src/section07_diamond.lean)
 * [Section 8: `unique`: proof-carrying mixin](src/section08_mixin.lean)
 * [Section 9: `fact`: interfacing between instances and non-instances](src/section09_ad_hoc.lean)
 * [Section 10: Performance and bundling](src/section10_performance.lean)
