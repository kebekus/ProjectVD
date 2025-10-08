# Project VD

### Formalizing Value Distribution Theory

This project aims to formalize [value distribution
theory](https://en.wikipedia.org/wiki/Value_distribution_theory_of_holomorphic_functions)
for meromorphic functions in the complex plane, roughly following Serge Lang's
[Introduction to Complex Hyperbolic
Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1). The project
uses the [Lean](https://lean-lang.org/) theorem prover and builds on
[mathlib](https://leanprover-community.github.io/), the Lean mathematical
library.

### Help Wanted

Please be in touch if you would like to join
the fun!

## Current State and Future Plans

### Milestones reached

- Formalized Nevanlinna's [First Main
  Theorem](https://en.wikipedia.org/wiki/Nevanlinna_theory#First_fundamental_theorem).

- Merged the formalization of first main theorem into Lean's mathlib.

### Next Milestones 

- Formalize the Theorem on Logarithmic Differentials
- Formalize the [Second Main
  Theorem](https://en.wikipedia.org/wiki/Nevanlinna_theory#Second_fundamental_theorem)
- Merge formalizations into mathlib
- Establish some of the more immediate applications

These plans might change, depending on feedback from the community and specific
interests of project participants.

## Material Covered

The following concepts have been formalized so far.

- Harmonic functions in the complex plane
    - Laplace operator and associated API
    - Definition and elementary properties of harmonic functions
    - Mean value properties of harmonic functions
    - Real and imaginary parts of holomorphic functions as examples of harmonic
      functions
- Holomorphic functions in the complex plane
    - Existence of holomorphic functions with given real part
- Meromorphic Functions in the complex plane
    - API for continuous extension of meromorphic functions, normal form of
      meromorphic functions up to changes along a discrete set
    - Behavior of pole/zero orders under standard operations
    - Zero/pole divisors attached to meromorphic functions and associated API
    - Extraction of zeros and poles
- Integrals and integrability of special functions
    - Interval integrals and integrability of the logarithm and its combinations
      with trigonometric functions; circle integrability of log ‖z-a‖
    - Circle integrability of log ‖meromorphic‖
- Basic functions of Value Distribution Theory
    - The positive part of the logarithm, API, standard inequalities and
      estimates
    - Logarithmic counting functions of divisors
    - Nevanlinna heights of entire meromorphic functions
    - Proximity functions for entire meromorphic functions
- [Jensen's formula](https://en.wikipedia.org/wiki/Jensen%27s_formula)
- Nevanlinna's [First Main
  Theorem](https://en.wikipedia.org/wiki/Nevanlinna_theory#First_fundamental_theorem)
