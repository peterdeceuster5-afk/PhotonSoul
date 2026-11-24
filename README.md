# PhotonSoul

A fully verified, zero-axiom, zero-`sorry` Lean 4 (`v4.37.0-rc1`) and Mathlib4 formalization of the **Photon Soul Generalized Maxwell Equations** ($d(\star F - P_s) = 0$) from `paper.tex`.

## Overview

`PhotonSoul.lean` mechanizes Section 4 of `paper.tex` on 4D Euclidean spacetime `X = EuclideanSpace ℝ (Fin 4)` equipped with Lebesgue/Haar measure and Mathlib's `ContinuousAlternatingMap` differential forms:

- **Physical setup**: Exterior derivative `d`, field strength `fieldStrength A = d A`, 4D Hodge star `hodgeStar`, background polarization 2-form `P_s`, Lagrangian density `L_tot`, total action `S_tot`, and Gâteaux variation `actionVariation`.
- **Core variational lemmas**:
  1. `deriv_under_integral` — differentiation under the Bochner integral via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
  2. `variation_expansion` — algebraic pointwise variation of `L_tot`.
  3. `stokes_integration_by_parts` — 4D integration by parts for compactly supported $C^1$ test 1-forms `δA`.
  4. `fundamental_lemma_var` — du Bois-Reymond lemma for continuous 3-forms on `ℝ⁴`.
- **Main theorem**: `photon_soul_conservation`, deriving `d (hodgeStar (fieldStrength A) - P_s) = 0` from stationarity `IsStationary P_s A`.

## Verification Audit

- **Custom axioms / `sorry`**: `0`
- **`#print axioms photon_soul_conservation`**:
  ```text
  'photon_soul_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

## Building

Ensure [Lean 4 / elan](https://leanprover-community.github.io/get_started.html) is installed, then fetch prebuilt Mathlib oleans and build:

```bash
lake exe cache get
lake build
```
