module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Support

import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped Topology

/-!
# Photon Soul Framework: Fully Mechanized Variational Proof

Zero-axiom, `sorry`-free formalization of Section 4 of `paper.tex`:
- 4D Euclidean spacetime `X = EuclideanSpace ℝ (Fin 4)` with Lebesgue/Haar measure
- Differential `k`-forms `DifferentialForm k` via `ContinuousAlternatingMap ℝ X ℝ (Fin k)`
- Exterior derivative `d`, field strength `F = dA`, 4D Hodge star `hodgeStar`, polarization `P_s`
- Total Lagrangian density `L_tot`, action functional `S_tot`, and Gâteaux variation
- Full proofs of the four core variational lemmas:
  1. `deriv_under_integral` (differentiation under the integral sign via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
  2. `variation_expansion` (algebraic pointwise variation of `L_tot`)
  3. `stokes_integration_by_parts` (4D Stokes' theorem / integration by parts for compactly supported 1-forms)
  4. `fundamental_lemma_var` (du Bois-Reymond fundamental lemma of calculus of variations for 3-forms)
- Main theorem `photon_soul_conservation`: `d (hodgeStar (fieldStrength A) - P_s) = 0`.
-/

/-! ## 1. Space and Concrete Differential Forms -/

/-- The 4-dimensional Euclidean spacetime coordinate chart `ℝ⁴`. -/
abbrev X : Type := EuclideanSpace ℝ (Fin 4)

/-- A differential `k`-form on `X`, modeled as a field of continuous alternating `k`-forms. -/
abbrev DifferentialForm (k : ℕ) : Type :=
  X → ContinuousAlternatingMap ℝ X ℝ (Fin k)

/-- A differential 1-form on `X`. -/
abbrev Form1 : Type := DifferentialForm 1

/-- A differential 2-form on `X`. -/
abbrev Form2 : Type := DifferentialForm 2

/-- A differential 3-form on `X`. -/
abbrev Form3 : Type := DifferentialForm 3

/-- A differential 4-form on `X`. -/
abbrev Form4 : Type := DifferentialForm 4

/-- A gauge vector potential `A` represented as a differential 1-form on `X`. -/
abbrev GaugeField : Type := Form1

/-- The `i`-th standard orthonormal basis vector of `X = ℝ⁴`. -/
abbrev basisVec (i : Fin 4) : X :=
  EuclideanSpace.basisFun (Fin 4) ℝ i

/-- Continuous linear functional evaluating a continuous alternating `k`-form at a fixed `k`-tuple. -/
def evalAlt {k : ℕ} (v : Fin k → X) : (ContinuousAlternatingMap ℝ X ℝ (Fin k)) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ i : Fin k, ‖v i‖)
    (fun f => by
      change ‖f v‖ ≤ (∏ i : Fin k, ‖v i‖) * ‖f‖
      rw [mul_comm]
      exact f.toContinuousMultilinearMap.le_opNorm v)

@[simp]
lemma evalAlt_apply {k : ℕ} (v : Fin k → X) (f : ContinuousAlternatingMap ℝ X ℝ (Fin k)) :
    evalAlt v f = f v := rfl

/-- Constant basis 1-form `dxᵐ` on `X`. -/
def basisForm1 (m : Fin 4) : ContinuousAlternatingMap ℝ X ℝ (Fin 1) :=
  ContinuousAlternatingMap.ofSubsingleton ℝ X ℝ (0 : Fin 1) (EuclideanSpace.proj (𝕜 := ℝ) m)

@[simp]
lemma basisForm1_apply (m : Fin 4) (v : Fin 1 → X) :
    basisForm1 m v = v 0 m := rfl

/-- The constant basis 2-form `dxⁱ ∧ dxʲ` on `X`, evaluating `(v₀, v₁) ↦ v₀ⁱ v₁ʲ - v₀ʲ v₁ⁱ`. -/
def basisForm2 (i j : Fin 4) : ContinuousAlternatingMap ℝ X ℝ (Fin 2) where
  toFun v := v 0 i * v 1 j - v 0 j * v 1 i
  map_update_add' := fun {_} v k x y => by
    fin_cases k <;> simp [Function.update] <;> ring
  map_update_smul' := fun {_} v k c x => by
    fin_cases k <;> simp [Function.update] <;> ring
  map_eq_zero_of_eq' := fun v a b hv hab => by
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change v 0 = v 1 at hv; rw [hv]; ring
    · change v 1 = v 0 at hv; rw [hv]; ring
    · exact absurd rfl hab
  cont := by
    have h0i : Continuous fun v : Fin 2 → X => v 0 i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp (continuous_apply 0)
    have h1j : Continuous fun v : Fin 2 → X => v 1 j :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (continuous_apply 1)
    have h0j : Continuous fun v : Fin 2 → X => v 0 j :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (continuous_apply 0)
    have h1i : Continuous fun v : Fin 2 → X => v 1 i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp (continuous_apply 1)
    exact (h0i.mul h1j).sub (h0j.mul h1i)

/-- The `i`-th component of a 1-form `α` at `x : X`. -/
def form1Comp (α : Form1) (i : Fin 4) (x : X) : ℝ :=
  α x ![basisVec i]

/-- The `(i, j)`-component of a 2-form `ω` at `x : X`. -/
def form2Comp (ω : Form2) (x : X) (i j : Fin 4) : ℝ :=
  ω x ![basisVec i, basisVec j]

/-- The `(i, j)`-component of a 2-form `ω` as a function `X → ℝ`. -/
def form2CompFn (ω : Form2) (i j : Fin 4) (x : X) : ℝ :=
  ω x ![basisVec i, basisVec j]

/-! ## 2. Physical Quantities -/

/-- Exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X)` acting on differential `k`-forms. -/
def d {k : ℕ} (ω : DifferentialForm k) : DifferentialForm (k + 1) :=
  _root_.extDeriv ω

/-- The electromagnetic field strength 2-form `F = dA`. -/
def fieldStrength (A : Form1) : Form2 :=
  d A

/-- The 4D Euclidean Hodge star operator `⋆ : Ω²(X) → Ω²(X)` on 2-forms. -/
def hodgeStar (ω : Form2) : Form2 := fun x =>
  form2Comp ω x 2 3 • basisForm2 0 1 -
  form2Comp ω x 1 3 • basisForm2 0 2 +
  form2Comp ω x 1 2 • basisForm2 0 3 +
  form2Comp ω x 0 3 • basisForm2 1 2 -
  form2Comp ω x 0 2 • basisForm2 1 3 +
  form2Comp ω x 0 1 • basisForm2 2 3

/-- Type of background "soul polarization" 2-forms `P_s ∈ Ω²(X)`. -/
abbrev PolarizationForm : Type := Form2

/-- Construct a background polarization 2-form `P_s` from its six independent component functions. -/
def mkPolarization (p01 p02 p03 p12 p13 p23 : X → ℝ) : PolarizationForm := fun x =>
  p01 x • basisForm2 0 1 +
  p02 x • basisForm2 0 2 +
  p03 x • basisForm2 0 3 +
  p12 x • basisForm2 1 2 +
  p13 x • basisForm2 1 3 +
  p23 x • basisForm2 2 3

/-- Pointwise 4D volume-normalized pairing `(α ∧ β)(e₀, e₁, e₂, e₃)` of two 2-forms. -/
def wedgePair22 (α β : Form2) (x : X) : ℝ :=
  form2Comp α x 0 1 * form2Comp β x 2 3 -
  form2Comp α x 0 2 * form2Comp β x 1 3 +
  form2Comp α x 0 3 * form2Comp β x 1 2 +
  form2Comp α x 1 2 * form2Comp β x 0 3 -
  form2Comp α x 1 3 * form2Comp β x 0 2 +
  form2Comp α x 2 3 * form2Comp β x 0 1

/-- Pointwise 4D Hodge pairing `⟨α, ⋆β⟩ = -(α ∧ β)(e₀, e₁, e₂, e₃)` of a 1-form and a 3-form. -/
def wedgePair13 (α : Form1) (β : Form3) (x : X) : ℝ :=
  - (α x ![basisVec 0] * β x ![basisVec 1, basisVec 2, basisVec 3] -
     α x ![basisVec 1] * β x ![basisVec 0, basisVec 2, basisVec 3] +
     α x ![basisVec 2] * β x ![basisVec 0, basisVec 1, basisVec 3] -
     α x ![basisVec 3] * β x ![basisVec 0, basisVec 1, basisVec 2])

/-- The total Lagrangian density `L_tot(A) = ½ F ∧ ⋆F - F ∧ P_s` at `x : X`. -/
def L_tot (P_s : PolarizationForm) (A : Form1) (x : X) : ℝ :=
  (1 / 2 : ℝ) * wedgePair22 (fieldStrength A) (hodgeStar (fieldStrength A)) x -
    wedgePair22 (fieldStrength A) P_s x

/-- The total action functional `S_tot[A] = ∫_X L_tot(A)` via Bochner integration over `X`. -/
def S_tot (P_s : PolarizationForm) (A : Form1) : ℝ :=
  ∫ x : X, L_tot P_s A x

/-- The 1-parameter varied action `t ↦ S_tot[A + t • δA]` as a function of `t : ℝ`. -/
def actionVariation (P_s : PolarizationForm) (A δA : Form1) (t : ℝ) : ℝ :=
  S_tot P_s (A + t • δA)

/-- The Gâteaux variation `d/dt|_{t=0} S_tot[A + t • δA]` of the action at `t = 0`. -/
def gateauxVariation (P_s : PolarizationForm) (A δA : Form1) : ℝ :=
  deriv (actionVariation P_s A δA) 0

/-- The pointwise `t`-derivative `d/dt|_{t=0} L_tot(A + t • δA)(x)` of the Lagrangian density. -/
def deriv_L_tot_eval (P_s : PolarizationForm) (A δA : Form1) (x : X) : ℝ :=
  deriv (fun t : ℝ => L_tot P_s (A + t • δA) x) 0

/-- Stationarity condition: `d/dt|_{t=0} S_tot[A + t • δA] = 0` for all `C¹` compactly supported `δA`. -/
def IsStationary (P_s : PolarizationForm) (A : Form1) : Prop :=
  ∀ δA : Form1, ContDiff ℝ 1 δA → HasCompactSupport δA →
    HasDerivAt (actionVariation P_s A δA) 0 0

/-! ## 3. Regularity and Coordinate Algebra Helpers -/

lemma continuous_evalAlt_comp {k : ℕ} {ω : DifferentialForm k} (hω : Continuous ω)
    (v : Fin k → X) : Continuous (fun x => ω x v) :=
  (evalAlt v).continuous.comp hω

lemma contDiff_evalAlt_comp {k : ℕ} {ω : DifferentialForm k} {n : WithTop ℕ∞}
    (hω : ContDiff ℝ n ω) (v : Fin k → X) : ContDiff ℝ n (fun x => ω x v) :=
  (evalAlt v).contDiff.comp hω

lemma continuous_d {k : ℕ} {ω : DifferentialForm k} (h : ContDiff ℝ 1 ω) : Continuous (d ω) := by
  change Continuous (fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ (fderiv ℝ ω x))
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ).continuous.comp
    (h.fderiv_right (m := 0) (by norm_num)).continuous

lemma contDiff_d {k : ℕ} {ω : DifferentialForm k} (h : ContDiff ℝ 2 ω) : ContDiff ℝ 1 (d ω) := by
  change ContDiff ℝ 1 (fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ (fderiv ℝ ω x))
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ).contDiff.comp
    (h.fderiv_right (m := 1) (by norm_num))

lemma hasCompactSupport_d {k : ℕ} {ω : DifferentialForm k} (h : HasCompactSupport ω) :
    HasCompactSupport (d ω) := by
  change HasCompactSupport (fun x => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ (fderiv ℝ ω x))
  exact (h.fderiv (𝕜 := ℝ)).comp_left
    (map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ X ℝ))

lemma continuous_form2Comp (ω : Form2) (hω : Continuous ω) (i j : Fin 4) :
    Continuous (fun x => form2Comp ω x i j) :=
  continuous_evalAlt_comp hω ![basisVec i, basisVec j]

lemma continuous_form1Comp (α : Form1) (hα : Continuous α) (i : Fin 4) :
    Continuous (form1Comp α i) :=
  continuous_evalAlt_comp hα ![basisVec i]

lemma contDiff_form1Comp (α : Form1) (hα : ContDiff ℝ 1 α) (i : Fin 4) :
    ContDiff ℝ 1 (form1Comp α i) :=
  contDiff_evalAlt_comp hα ![basisVec i]

lemma continuous_form2CompFn (ω : Form2) (hω : Continuous ω) (i j : Fin 4) :
    Continuous (form2CompFn ω i j) :=
  continuous_evalAlt_comp hω ![basisVec i, basisVec j]

lemma contDiff_form2CompFn (ω : Form2) (hω : ContDiff ℝ 1 ω) (i j : Fin 4) :
    ContDiff ℝ 1 (form2CompFn ω i j) :=
  contDiff_evalAlt_comp hω ![basisVec i, basisVec j]

lemma continuous_hodgeStar (ω : Form2) (hω : Continuous ω) : Continuous (hodgeStar ω) := by
  unfold hodgeStar
  refine ((((((continuous_form2Comp ω hω 2 3).smul continuous_const).sub
    ((continuous_form2Comp ω hω 1 3).smul continuous_const)).add
    ((continuous_form2Comp ω hω 1 2).smul continuous_const)).add
    ((continuous_form2Comp ω hω 0 3).smul continuous_const)).sub
    ((continuous_form2Comp ω hω 0 2).smul continuous_const)).add
    ((continuous_form2Comp ω hω 0 1).smul continuous_const)

lemma continuous_wedgePair22 (α β : Form2) (hα : Continuous α) (hβ : Continuous β) :
    Continuous (wedgePair22 α β) := by
  unfold wedgePair22
  refine ((((((continuous_form2Comp α hα 0 1).mul (continuous_form2Comp β hβ 2 3)).sub
    ((continuous_form2Comp α hα 0 2).mul (continuous_form2Comp β hβ 1 3))).add
    ((continuous_form2Comp α hα 0 3).mul (continuous_form2Comp β hβ 1 2))).add
    ((continuous_form2Comp α hα 1 2).mul (continuous_form2Comp β hβ 0 3))).sub
    ((continuous_form2Comp α hα 1 3).mul (continuous_form2Comp β hβ 0 2))).add
    ((continuous_form2Comp α hα 2 3).mul (continuous_form2Comp β hβ 0 1))

lemma hasCompactSupport_wedgePair22_left (α β : Form2) (hα : HasCompactSupport α) :
    HasCompactSupport (wedgePair22 α β) := by
  have hc : ∀ i j, HasCompactSupport (fun x => form2Comp α x i j) := fun i j =>
    hα.comp_left (evalAlt ![basisVec i, basisVec j]).map_zero
  unfold wedgePair22
  exact ((((((hc 0 1).mul_right.sub (hc 0 2).mul_right).add
    (hc 0 3).mul_right).add (hc 1 2).mul_right).sub
    (hc 1 3).mul_right).add (hc 2 3).mul_right)

lemma continuous_wedgePair13 (α : Form1) (β : Form3) (hα : Continuous α) (hβ : Continuous β) :
    Continuous (wedgePair13 α β) := by
  unfold wedgePair13
  exact (((((continuous_evalAlt_comp hα ![basisVec 0]).mul
      (continuous_evalAlt_comp hβ ![basisVec 1, basisVec 2, basisVec 3])).sub
    ((continuous_evalAlt_comp hα ![basisVec 1]).mul
      (continuous_evalAlt_comp hβ ![basisVec 0, basisVec 2, basisVec 3]))).add
    ((continuous_evalAlt_comp hα ![basisVec 2]).mul
      (continuous_evalAlt_comp hβ ![basisVec 0, basisVec 1, basisVec 3]))).sub
    ((continuous_evalAlt_comp hα ![basisVec 3]).mul
      (continuous_evalAlt_comp hβ ![basisVec 0, basisVec 1, basisVec 2]))).neg

lemma hasCompactSupport_wedgePair13_left (α : Form1) (β : Form3) (hα : HasCompactSupport α) :
    HasCompactSupport (wedgePair13 α β) := by
  have hc : ∀ i : Fin 4, HasCompactSupport (fun x => α x ![basisVec i]) := fun i =>
    hα.comp_left (evalAlt ![basisVec i]).map_zero
  unfold wedgePair13
  exact (((((hc 0).mul_right.sub (hc 1).mul_right).add
    (hc 2).mul_right).sub (hc 3).mul_right).neg)

lemma basisVec_apply (i j : Fin 4) : basisVec i j = if j = i then (1 : ℝ) else 0 := by
  simp [basisVec, EuclideanSpace.basisFun_apply]

lemma basisForm2_apply (i j k l : Fin 4) :
    basisForm2 i j ![basisVec k, basisVec l] =
      (if k = i then (1 : ℝ) else 0) * (if l = j then (1 : ℝ) else 0) -
      (if k = j then (1 : ℝ) else 0) * (if l = i then (1 : ℝ) else 0) := by
  change (basisVec k) i * (basisVec l) j - (basisVec k) j * (basisVec l) i = _
  simp only [basisVec_apply, eq_comm]

lemma form2Comp_hodgeStar_01 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 0 1 = form2Comp ω x 2 3 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma form2Comp_hodgeStar_02 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 0 2 = -form2Comp ω x 1 3 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma form2Comp_hodgeStar_03 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 0 3 = form2Comp ω x 1 2 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma form2Comp_hodgeStar_12 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 1 2 = form2Comp ω x 0 3 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma form2Comp_hodgeStar_13 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 1 3 = -form2Comp ω x 0 2 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma form2Comp_hodgeStar_23 (ω : Form2) (x : X) :
    form2Comp (hodgeStar ω) x 2 3 = form2Comp ω x 0 1 := by
  simp only [form2Comp, hodgeStar, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, basisForm2_apply]
  norm_num

lemma wedgePair22_hodgeStar_symm (α β : Form2) (x : X) :
    wedgePair22 α (hodgeStar β) x = wedgePair22 β (hodgeStar α) x := by
  simp only [wedgePair22, form2Comp_hodgeStar_01, form2Comp_hodgeStar_02,
    form2Comp_hodgeStar_03, form2Comp_hodgeStar_12, form2Comp_hodgeStar_13,
    form2Comp_hodgeStar_23]
  ring

lemma form2Comp_add (α β : Form2) (x : X) (i j : Fin 4) :
    form2Comp (α + β) x i j = form2Comp α x i j + form2Comp β x i j := rfl

lemma form2Comp_sub (α β : Form2) (x : X) (i j : Fin 4) :
    form2Comp (α - β) x i j = form2Comp α x i j - form2Comp β x i j := rfl

lemma form2Comp_smul (c : ℝ) (α : Form2) (x : X) (i j : Fin 4) :
    form2Comp (c • α) x i j = c * form2Comp α x i j := rfl

lemma wedgePair22_add_left (α₁ α₂ β : Form2) (x : X) :
    wedgePair22 (α₁ + α₂) β x = wedgePair22 α₁ β x + wedgePair22 α₂ β x := by
  simp only [wedgePair22, form2Comp_add]; ring

lemma wedgePair22_smul_left (c : ℝ) (α β : Form2) (x : X) :
    wedgePair22 (c • α) β x = c * wedgePair22 α β x := by
  simp only [wedgePair22, form2Comp_smul]; ring

lemma wedgePair22_sub_right (α β₁ β₂ : Form2) (x : X) :
    wedgePair22 α (β₁ - β₂) x = wedgePair22 α β₁ x - wedgePair22 α β₂ x := by
  simp only [wedgePair22, form2Comp_sub]; ring

lemma hodgeStar_add (α β : Form2) : hodgeStar (α + β) = hodgeStar α + hodgeStar β := by
  ext x v
  simp only [hodgeStar, form2Comp_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

lemma hodgeStar_smul (c : ℝ) (α : Form2) : hodgeStar (c • α) = c • hodgeStar α := by
  ext x v
  simp only [hodgeStar, form2Comp_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply, smul_eq_mul]
  ring

/-! ## 4. Lemma 2: Algebraic Variation of the Action (`variation_expansion`) -/

lemma fieldStrength_variation_eq (A δA : Form1) (x : X)
    (hA : DifferentiableAt ℝ A x) (hδA : DifferentiableAt ℝ δA x) (t : ℝ) :
    fieldStrength (A + t • δA) x = fieldStrength A x + t • d δA x := by
  change extDeriv (A + t • δA) x = extDeriv A x + t • extDeriv δA x
  rw [extDeriv_add hA (hδA.const_smul t), extDeriv_smul]

lemma L_tot_variation_eq (P_s : PolarizationForm) (A δA : Form1) (x : X)
    (hA : DifferentiableAt ℝ A x) (hδA : DifferentiableAt ℝ δA x) (t : ℝ) :
    L_tot P_s (A + t • δA) x =
      L_tot P_s A x +
      t * wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x +
      (1 / 2 : ℝ) * t ^ 2 * wedgePair22 (d δA) (hodgeStar (d δA)) x := by
  have hF : ∀ y, y = x → fieldStrength (A + t • δA) y = (fieldStrength A + t • d δA) y := by
    rintro y rfl; exact fieldStrength_variation_eq A δA y hA hδA t
  have hF_x : fieldStrength (A + t • δA) x = (fieldStrength A + t • d δA) x := hF x rfl
  have hFstar_x : hodgeStar (fieldStrength (A + t • δA)) x =
      hodgeStar (fieldStrength A + t • d δA) x := by
    simp only [hodgeStar, form2Comp, hF_x]
  have h_w1 : wedgePair22 (fieldStrength (A + t • δA)) (hodgeStar (fieldStrength (A + t • δA))) x =
      wedgePair22 (fieldStrength A + t • d δA) (hodgeStar (fieldStrength A + t • d δA)) x := by
    simp only [wedgePair22, form2Comp, hF_x, hFstar_x]
  have h_w2 : wedgePair22 (fieldStrength (A + t • δA)) P_s x =
      wedgePair22 (fieldStrength A + t • d δA) P_s x := by
    simp only [wedgePair22, form2Comp, hF_x]
  have h_symm : wedgePair22 (fieldStrength A) (hodgeStar (d δA)) x =
      wedgePair22 (d δA) (hodgeStar (fieldStrength A)) x :=
    wedgePair22_hodgeStar_symm (fieldStrength A) (d δA) x
  have h_w1_exp :
      wedgePair22 (fieldStrength A + t • d δA) (hodgeStar (fieldStrength A + t • d δA)) x =
        wedgePair22 (fieldStrength A) (hodgeStar (fieldStrength A)) x +
        2 * t * wedgePair22 (d δA) (hodgeStar (fieldStrength A)) x +
        t ^ 2 * wedgePair22 (d δA) (hodgeStar (d δA)) x := by
    rw [hodgeStar_add, hodgeStar_smul]
    rw [wedgePair22_add_left, wedgePair22_smul_left]
    have h_right_add : ∀ γ : Form2,
        wedgePair22 γ (hodgeStar (fieldStrength A) + t • hodgeStar (d δA)) x =
          wedgePair22 γ (hodgeStar (fieldStrength A)) x +
            t * wedgePair22 γ (hodgeStar (d δA)) x := by
      intro γ
      simp only [wedgePair22, form2Comp, Pi.add_apply, Pi.smul_apply,
        ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      ring
    rw [h_right_add, h_right_add, h_symm]
    ring
  rw [L_tot, L_tot, h_w1, h_w2, h_w1_exp, wedgePair22_add_left, wedgePair22_smul_left,
    wedgePair22_sub_right]
  ring

lemma hasDerivAt_L_tot_variation (P_s : PolarizationForm) (A δA : Form1) (x : X)
    (hA : DifferentiableAt ℝ A x) (hδA : DifferentiableAt ℝ δA x) (t : ℝ) :
    HasDerivAt (fun s : ℝ => L_tot P_s (A + s • δA) x)
      (wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x +
        t * wedgePair22 (d δA) (hodgeStar (d δA)) x) t := by
  have hfun : (fun s : ℝ => L_tot P_s (A + s • δA) x) =
      fun s : ℝ =>
        L_tot P_s A x +
        s * wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x +
        (1 / 2 : ℝ) * s ^ 2 * wedgePair22 (d δA) (hodgeStar (d δA)) x := by
    funext s; exact L_tot_variation_eq P_s A δA x hA hδA s
  rw [hfun]
  have hd1 : HasDerivAt (fun s : ℝ => L_tot P_s A x +
      s * wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x)
      (wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x) t := by
    simpa using
      ((hasDerivAt_id t).mul_const (wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x)).const_add
        (L_tot P_s A x)
  have hd2 : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s ^ 2 * wedgePair22 (d δA) (hodgeStar (d δA)) x)
      (t * wedgePair22 (d δA) (hodgeStar (d δA)) x) t := by
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    convert ((hsq.const_mul (1 / 2 : ℝ)).mul_const (wedgePair22 (d δA) (hodgeStar (d δA)) x)) using 1
    ring
  exact hd1.add hd2

/-- **Lemma 2 (`variation_expansion`)**: Pointwise variation of `L_tot` equals `⟨d(δA), ⋆F - P_s⟩`. -/
lemma variation_expansion (P_s : PolarizationForm) (A δA : Form1) (x : X)
    (hA : DifferentiableAt ℝ A x) (hδA : DifferentiableAt ℝ δA x) :
    deriv_L_tot_eval P_s A δA x =
      wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x := by
  have h := (hasDerivAt_L_tot_variation P_s A δA x hA hδA 0).deriv
  simpa [deriv_L_tot_eval] using h

/-! ## 5. Lemma 1: Differentiation Under the Integral Sign (`deriv_under_integral`) -/

/-- **Lemma 1 (`deriv_under_integral`)**: Commutes the `t`-derivative at `t = 0` with the Bochner integral. -/
lemma deriv_under_integral (P_s : PolarizationForm) (A δA : Form1)
    (hA : ContDiff ℝ 1 A) (hδA : ContDiff ℝ 1 δA) (hP : Continuous P_s)
    (h_comp : HasCompactSupport δA) (hL_int : Integrable (L_tot P_s A)) :
    HasDerivAt (actionVariation P_s A δA) (∫ x : X, deriv_L_tot_eval P_s A δA x) 0 := by
  let F : ℝ → X → ℝ := fun t x => L_tot P_s (A + t • δA) x
  let b : X → ℝ := fun x => wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x
  let c : X → ℝ := fun x => wedgePair22 (d δA) (hodgeStar (d δA)) x
  let F' : ℝ → X → ℝ := fun t x => b x + t * c x
  let bound : X → ℝ := fun x => |b x| + |c x|
  have hdA : Continuous (d δA) := continuous_d hδA
  have hF_cont : Continuous (fieldStrength A) := continuous_d hA
  have hb_cont : Continuous b :=
    continuous_wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) hdA
      ((continuous_hodgeStar (fieldStrength A) hF_cont).sub hP)
  have hc_cont : Continuous c :=
    continuous_wedgePair22 (d δA) (hodgeStar (d δA)) hdA (continuous_hodgeStar (d δA) hdA)
  have hcomp_d : HasCompactSupport (d δA) := hasCompactSupport_d h_comp
  have hb_comp : HasCompactSupport b := hasCompactSupport_wedgePair22_left _ _ hcomp_d
  have hc_comp : HasCompactSupport c := hasCompactSupport_wedgePair22_left _ _ hcomp_d
  have hbound_cont : Continuous bound := hb_cont.abs.add hc_cont.abs
  have hbound_comp : HasCompactSupport bound :=
    (hb_comp.comp_left abs_zero).add (hc_comp.comp_left abs_zero)
  have hbound_int : Integrable bound := hbound_cont.integrable_of_hasCompactSupport hbound_comp
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) volume := by
    refine Eventually.of_forall fun t => ?_
    have hAt : ContDiff ℝ 1 (A + t • δA) := hA.add (hδA.const_smul t)
    have hFt_cont : Continuous (fieldStrength (A + t • δA)) := continuous_d hAt
    have hLt_cont : Continuous (F t) := by
      have h1 : Continuous (fun x => (1 / 2 : ℝ) *
          wedgePair22 (fieldStrength (A + t • δA)) (hodgeStar (fieldStrength (A + t • δA))) x) :=
        continuous_const.mul (continuous_wedgePair22 _ _ hFt_cont (continuous_hodgeStar _ hFt_cont))
      have h2 : Continuous (fun x => wedgePair22 (fieldStrength (A + t • δA)) P_s x) :=
        continuous_wedgePair22 _ _ hFt_cont hP
      exact h1.sub h2
    exact hLt_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t x‖ ≤ bound x := by
    refine Eventually.of_forall fun x t ht => ?_
    have ht1 : |t| ≤ 1 := (mem_ball_zero_iff.mp ht).le
    calc
      ‖F' t x‖ = |b x + t * c x| := Real.norm_eq_abs _
      _ ≤ |b x| + |t * c x| := abs_add_le _ _
      _ = |b x| + |t| * |c x| := by rw [abs_mul]
      _ ≤ |b x| + 1 * |c x| := by gcongr
      _ = bound x := by simp [bound]
  have h_diff : ∀ᵐ x ∂volume, ∀ t ∈ Metric.ball (0 : ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    refine Eventually.of_forall fun x t _ => ?_
    exact hasDerivAt_L_tot_variation P_s A δA x
      (hA.differentiable one_ne_zero x) (hδA.differentiable one_ne_zero x) t
  have hF'0_meas : AEStronglyMeasurable (F' 0) volume :=
    (hb_cont.add (continuous_const.mul hc_cont)).aestronglyMeasurable
  have h_main := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    hF_meas
    (by simpa [F] using hL_int)
    hF'0_meas
    h_bound
    hbound_int
    h_diff).2
  have h_eq : (∫ x : X, F' 0 x) = ∫ x : X, deriv_L_tot_eval P_s A δA x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hv := variation_expansion P_s A δA x
      (hA.differentiable one_ne_zero x) (hδA.differentiable one_ne_zero x)
    simp [F', b, hv]
  rw [hasDerivAt_iff_tendsto] at h_main ⊢
  simpa only [smul_eq_mul, actionVariation, S_tot, F, h_eq] using h_main

/-! ## 6. Lemma 3: Stokes' Integration by Parts (`stokes_integration_by_parts`) -/

lemma integral_partialDeriv_eq_zero (f : X → ℝ) (k : Fin 4)
    (hf : ContDiff ℝ 1 f) (hcomp : HasCompactSupport f) :
    ∫ x : X, fderiv ℝ f x (basisVec k) = 0 := by
  let g : X → ℝ := fun x => fderiv ℝ f x (basisVec k)
  have hg_cont : Continuous g := by
    have hfd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := 0) (by norm_num)).continuous
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVec k)).continuous.comp hfd
  have hg_comp : HasCompactSupport g := hcomp.fderiv_apply (𝕜 := ℝ) (basisVec k)
  have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hg_comp
  have h_e1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)) volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).symm
  have h_e2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) k).symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) k).symm
  have h_prod_int : Integrable
      (fun p : ℝ × (Fin 3 → ℝ) => g (WithLp.toLp 2 (k.insertNth p.1 p.2)))
      (volume.prod volume) := by
    have h1 : Integrable (fun y : Fin 4 → ℝ => g (WithLp.toLp 2 y)) volume :=
      (h_e1.integrable_comp_emb (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding).2 hg_int
    exact (h_e2.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) k).symm.measurableEmbedding).2 h1
  rw [← h_e1.integral_comp' g,
    ← h_e2.integral_comp' (fun y : Fin 4 → ℝ => g ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)) y))]
  change ∫ p : ℝ × (Fin 3 → ℝ), g (WithLp.toLp 2 (k.insertNth p.1 p.2)) ∂(volume.prod volume) = 0
  rw [integral_prod_symm _ h_prod_int]
  obtain ⟨R, hR⟩ := hcomp.isCompact.isBounded.subset_closedBall (0 : X)
  have hR_zero : ∀ x : X, R < ‖x‖ → f x = 0 := by
    intro x hx
    by_contra hfx
    have hx_supp : x ∈ tsupport f := subset_tsupport f hfx
    have hx_ball := hR hx_supp
    rw [mem_closedBall_zero_iff] at hx_ball
    linarith
  have h_inner : ∀ y' : Fin 3 → ℝ,
      ∫ s : ℝ, g (WithLp.toLp 2 (k.insertNth s y')) = 0 := by
    intro y'
    let φ : ℝ → ℝ := fun s => f (WithLp.toLp 2 (k.insertNth s y'))
    let φ' : ℝ → ℝ := fun s => g (WithLp.toLp 2 (k.insertNth s y'))
    have h_line : ∀ s : ℝ, WithLp.toLp 2 (k.insertNth s y') =
        WithLp.toLp 2 (k.insertNth 0 y') + s • basisVec k := by
      intro s
      ext j
      rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basisVec_apply]
      by_cases hjk : j = k
      · subst hjk; simp
      · obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq hjk
        subst hm
        simp [Fin.insertNth_apply_succAbove, hjk]
    have h_line_deriv : ∀ s : ℝ,
        HasDerivAt (fun t : ℝ => WithLp.toLp 2 (k.insertNth t y')) (basisVec k) s := by
      intro s
      have h_eq : (fun t : ℝ => WithLp.toLp 2 (k.insertNth t y')) =
          fun t : ℝ => WithLp.toLp 2 (k.insertNth 0 y') + t • basisVec k :=
        funext h_line
      rw [h_eq]
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id s).smul_const (basisVec k)).const_add (WithLp.toLp 2 (k.insertNth 0 y'))
    have h_deriv : ∀ s : ℝ, HasDerivAt φ (φ' s) s := by
      intro s
      have hf_at := (hf.differentiable one_ne_zero (WithLp.toLp 2 (k.insertNth s y'))).hasFDerivAt
      have hd := hf_at.comp_hasDerivAt s (h_line_deriv s)
      rw [hasDerivAt_iff_tendsto] at hd ⊢
      simpa only [smul_eq_mul, φ, φ', g, Function.comp_apply] using hd
    have h_supp_bound : ∀ s : ℝ, R < |s| → φ s = 0 := by
      intro s hs
      apply hR_zero
      refine lt_of_lt_of_le hs ?_
      have hnorm := PiLp.norm_apply_le (WithLp.toLp 2 (k.insertNth (α := fun _ : Fin 4 => ℝ) s y')) k
      simpa [Real.norm_eq_abs] using hnorm
    let M : ℝ := max R 0 + 1
    have hRM : R < M := by linarith [le_max_left R 0]
    have hMpos : 0 < M := by linarith [le_max_right R 0]
    have h_bot : Tendsto φ atBot (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atBot]
      refine ⟨-M, fun s hs => ?_⟩
      symm; apply h_supp_bound
      have hs_neg : s < 0 := by linarith
      rw [abs_of_neg hs_neg]
      linarith
    have h_top : Tendsto φ atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨M, fun s hs => ?_⟩
      symm; apply h_supp_bound
      exact lt_of_lt_of_le (by linarith) (le_abs_self s)
    have h_cont_φ' : Continuous φ' := by
      have hφ'_eq : φ' = fun s => g (WithLp.toLp 2 (k.insertNth 0 y') + s • basisVec k) :=
        funext fun s => by simp [φ', h_line s]
      rw [hφ'_eq]
      exact hg_cont.comp (continuous_const.add (continuous_id'.smul continuous_const))
    have h_comp_φ' : HasCompactSupport φ' := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M)) ?_
      intro s hs
      by_contra h_not
      simp only [Set.mem_Icc, not_and, not_le] at h_not
      have h_r : R < |s| := by
        by_cases hle : s < -M
        · rw [abs_of_neg (by linarith : s < 0)]
          linarith
        · have hgt : M < s := h_not (not_lt.mp hle)
          exact lt_of_lt_of_le (by linarith) (le_abs_self s)
      have h_zero_nhds : φ =ᶠ[𝓝 s] 0 := by
        have h_open : IsOpen {t : ℝ | R < |t|} :=
          isOpen_lt continuous_const continuous_abs
        filter_upwards [h_open.mem_nhds h_r] with t ht
        exact h_supp_bound t ht
      have h_d0 : deriv φ s = 0 := h_zero_nhds.deriv_eq.trans (by simp)
      rw [(h_deriv s).deriv] at h_d0
      exact hs h_d0
    have hφ'_int : Integrable φ' volume := h_cont_φ'.integrable_of_hasCompactSupport h_comp_φ'
    simpa [sub_self] using integral_of_hasDerivAt_of_tendsto h_deriv hφ'_int h_bot h_top
  simp [h_inner]

lemma fderiv_evalAlt {k : ℕ} {ω : DifferentialForm k} {x : X}
    (hω : DifferentiableAt ℝ ω x) (v : Fin k → X) (u : X) :
    fderiv ℝ (fun y => ω y v) x u = fderiv ℝ ω x u v := by
  have hd := (evalAlt v).hasFDerivAt.comp x hω.hasFDerivAt
  change fderiv ℝ (evalAlt v ∘ ω) x u = fderiv ℝ ω x u v
  simpa using congrArg (fun L : X →L[ℝ] ℝ => L u) hd.fderiv

lemma d_form1_apply (α : Form1) (x : X) (hα : DifferentiableAt ℝ α x) (i j : Fin 4) :
    d α x ![basisVec i, basisVec j] =
      fderiv ℝ (form1Comp α j) x (basisVec i) - fderiv ℝ (form1Comp α i) x (basisVec j) := by
  change extDeriv α x ![basisVec i, basisVec j] = _
  rw [extDeriv_apply hα, Fin.sum_univ_two]
  have hr0 : (0 : Fin 2).removeNth ![basisVec i, basisVec j] = ![basisVec j] := by
    ext m; fin_cases m; rfl
  have hr1 : (1 : Fin 2).removeNth ![basisVec i, basisVec j] = ![basisVec i] := by
    ext m; fin_cases m; rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, hr0, hr1]
  change fderiv ℝ (form1Comp α j) x (basisVec i) + -fderiv ℝ (form1Comp α i) x (basisVec j) = _
  ring

lemma d_form2_apply (ω : Form2) (x : X) (hω : DifferentiableAt ℝ ω x) (i j k : Fin 4) :
    d ω x ![basisVec i, basisVec j, basisVec k] =
      fderiv ℝ (form2CompFn ω j k) x (basisVec i) -
      fderiv ℝ (form2CompFn ω i k) x (basisVec j) +
      fderiv ℝ (form2CompFn ω i j) x (basisVec k) := by
  change extDeriv ω x ![basisVec i, basisVec j, basisVec k] = _
  rw [extDeriv_apply hω, Fin.sum_univ_three]
  have hr0 : (0 : Fin 3).removeNth ![basisVec i, basisVec j, basisVec k] =
      ![basisVec j, basisVec k] := by
    ext m; fin_cases m <;> rfl
  have hr1 : (1 : Fin 3).removeNth ![basisVec i, basisVec j, basisVec k] =
      ![basisVec i, basisVec k] := by
    ext m; fin_cases m <;> rfl
  have hr2 : (2 : Fin 3).removeNth ![basisVec i, basisVec j, basisVec k] =
      ![basisVec i, basisVec j] := by
    ext m; fin_cases m <;> rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    Fin.val_two, Matrix.cons_val_zero, Matrix.cons_val_one, hr0, hr1, hr2]
  change fderiv ℝ (form2CompFn ω j k) x (basisVec i) +
      -fderiv ℝ (form2CompFn ω i k) x (basisVec j) +
      ((-1 : ℤ) ^ (2 : ℕ) • fderiv ℝ (form2CompFn ω i j) x (basisVec k)) = _
  norm_num
  ring

/-- **Lemma 3 (`stokes_integration_by_parts`)**: Integration by parts on `ℝ⁴` for compactly supported `δA`. -/
lemma stokes_integration_by_parts (δA : Form1) (ω : Form2)
    (hδA : ContDiff ℝ 1 δA) (hω : ContDiff ℝ 1 ω) (h_comp : HasCompactSupport δA) :
    (∫ x : X, wedgePair22 (d δA) ω x) = - ∫ x : X, wedgePair13 δA (d ω) x := by
  let a : Fin 4 → X → ℝ := fun i => form1Comp δA i
  let w : Fin 4 → Fin 4 → X → ℝ := fun i j => form2CompFn ω i j
  let V0 : X → ℝ := fun x =>
    a 1 x * w 2 3 x - a 2 x * w 1 3 x + a 3 x * w 1 2 x
  let V1 : X → ℝ := fun x =>
    -a 0 x * w 2 3 x + a 2 x * w 0 3 x - a 3 x * w 0 2 x
  let V2 : X → ℝ := fun x =>
    a 0 x * w 1 3 x - a 1 x * w 0 3 x + a 3 x * w 0 1 x
  let V3 : X → ℝ := fun x =>
    -a 0 x * w 1 2 x + a 1 x * w 0 2 x - a 2 x * w 0 1 x
  have ha_cd : ∀ i, ContDiff ℝ 1 (a i) := fun i => contDiff_form1Comp δA hδA i
  have hw_cd : ∀ i j, ContDiff ℝ 1 (w i j) := fun i j => contDiff_form2CompFn ω hω i j
  have ha_comp : ∀ i, HasCompactSupport (a i) := fun i =>
    h_comp.comp_left (evalAlt ![basisVec i]).map_zero
  have hV0_cd : ContDiff ℝ 1 V0 :=
    (((ha_cd 1).mul (hw_cd 2 3)).sub ((ha_cd 2).mul (hw_cd 1 3))).add ((ha_cd 3).mul (hw_cd 1 2))
  have hV1_cd : ContDiff ℝ 1 V1 :=
    ((((ha_cd 0).neg).mul (hw_cd 2 3)).add ((ha_cd 2).mul (hw_cd 0 3))).sub
      ((ha_cd 3).mul (hw_cd 0 2))
  have hV2_cd : ContDiff ℝ 1 V2 :=
    (((ha_cd 0).mul (hw_cd 1 3)).sub ((ha_cd 1).mul (hw_cd 0 3))).add ((ha_cd 3).mul (hw_cd 0 1))
  have hV3_cd : ContDiff ℝ 1 V3 :=
    ((((ha_cd 0).neg).mul (hw_cd 1 2)).add ((ha_cd 1).mul (hw_cd 0 2))).sub
      ((ha_cd 2).mul (hw_cd 0 1))
  have hV0_comp : HasCompactSupport V0 :=
    (((ha_comp 1).mul_right).sub ((ha_comp 2).mul_right)).add ((ha_comp 3).mul_right)
  have hV1_comp : HasCompactSupport V1 :=
    ((((ha_comp 0).neg).mul_right).add ((ha_comp 2).mul_right)).sub ((ha_comp 3).mul_right)
  have hV2_comp : HasCompactSupport V2 :=
    (((ha_comp 0).mul_right).sub ((ha_comp 1).mul_right)).add ((ha_comp 3).mul_right)
  have hV3_comp : HasCompactSupport V3 :=
    ((((ha_comp 0).neg).mul_right).add ((ha_comp 1).mul_right)).sub ((ha_comp 2).mul_right)
  have h_ptwise : ∀ x : X,
      wedgePair22 (d δA) ω x + wedgePair13 δA (d ω) x =
        fderiv ℝ V0 x (basisVec 0) + fderiv ℝ V1 x (basisVec 1) +
        fderiv ℝ V2 x (basisVec 2) + fderiv ℝ V3 x (basisVec 3) := by
    intro x
    have hdA_x := hδA.differentiable one_ne_zero x
    have hω_x := hω.differentiable one_ne_zero x
    have ha_diff : ∀ i, DifferentiableAt ℝ (a i) x :=
      fun i => (ha_cd i).differentiable one_ne_zero x
    have hw_diff : ∀ i j, DifferentiableAt ℝ (w i j) x :=
      fun i j => (hw_cd i j).differentiable one_ne_zero x
    have hfd_prod : ∀ i j k m,
        fderiv ℝ (fun y => a i y * w j k y) x (basisVec m) =
          a i x * fderiv ℝ (w j k) x (basisVec m) +
          w j k x * fderiv ℝ (a i) x (basisVec m) := by
      intro i j k m
      have h := fderiv_mul (ha_diff i) (hw_diff j k)
      change fderiv ℝ (a i * w j k) x (basisVec m) = _
      simpa using congrArg (fun L : X →L[ℝ] ℝ => L (basisVec m)) h
    have hfd_neg_prod : ∀ i j k m,
        fderiv ℝ (fun y => -a i y * w j k y) x (basisVec m) =
          -(a i x * fderiv ℝ (w j k) x (basisVec m) +
            w j k x * fderiv ℝ (a i) x (basisVec m)) := by
      intro i j k m
      have h := fderiv_mul (ha_diff i).neg (hw_diff j k)
      have h1 := congrArg (fun L : X →L[ℝ] ℝ => L (basisVec m)) h
      simp only [fderiv_neg, add_apply, smul_apply, neg_apply, smul_eq_mul, Pi.neg_apply] at h1
      change fderiv ℝ (-a i * w j k) x (basisVec m) = _
      linarith
    have hV0_x : fderiv ℝ V0 x (basisVec 0) =
        (a 1 x * fderiv ℝ (w 2 3) x (basisVec 0) + w 2 3 x * fderiv ℝ (a 1) x (basisVec 0)) -
        (a 2 x * fderiv ℝ (w 1 3) x (basisVec 0) + w 1 3 x * fderiv ℝ (a 2) x (basisVec 0)) +
        (a 3 x * fderiv ℝ (w 1 2) x (basisVec 0) + w 1 2 x * fderiv ℝ (a 3) x (basisVec 0)) := by
      have h1 : DifferentiableAt ℝ (fun y => a 1 y * w 2 3 y) x := (ha_diff 1).mul (hw_diff 2 3)
      have h2 : DifferentiableAt ℝ (fun y => a 2 y * w 1 3 y) x := (ha_diff 2).mul (hw_diff 1 3)
      have h3 : DifferentiableAt ℝ (fun y => a 3 y * w 1 2 y) x := (ha_diff 3).mul (hw_diff 1 2)
      have hV := congrArg (fun L : X →L[ℝ] ℝ => L (basisVec 0))
        (((h1.hasFDerivAt.sub h2.hasFDerivAt).add h3.hasFDerivAt).fderiv)
      change fderiv ℝ V0 x (basisVec 0) = _ at hV
      simpa only [add_apply, sub_apply, hfd_prod] using hV
    have hV1_x : fderiv ℝ V1 x (basisVec 1) =
        -(a 0 x * fderiv ℝ (w 2 3) x (basisVec 1) + w 2 3 x * fderiv ℝ (a 0) x (basisVec 1)) +
        (a 2 x * fderiv ℝ (w 0 3) x (basisVec 1) + w 0 3 x * fderiv ℝ (a 2) x (basisVec 1)) -
        (a 3 x * fderiv ℝ (w 0 2) x (basisVec 1) + w 0 2 x * fderiv ℝ (a 3) x (basisVec 1)) := by
      have h1 : DifferentiableAt ℝ (fun y => -a 0 y * w 2 3 y) x :=
        ((ha_diff 0).neg).mul (hw_diff 2 3)
      have h2 : DifferentiableAt ℝ (fun y => a 2 y * w 0 3 y) x := (ha_diff 2).mul (hw_diff 0 3)
      have h3 : DifferentiableAt ℝ (fun y => a 3 y * w 0 2 y) x := (ha_diff 3).mul (hw_diff 0 2)
      have hV := congrArg (fun L : X →L[ℝ] ℝ => L (basisVec 1))
        (((h1.hasFDerivAt.add h2.hasFDerivAt).sub h3.hasFDerivAt).fderiv)
      change fderiv ℝ V1 x (basisVec 1) = _ at hV
      simpa only [add_apply, sub_apply, hfd_neg_prod, hfd_prod] using hV
    have hV2_x : fderiv ℝ V2 x (basisVec 2) =
        (a 0 x * fderiv ℝ (w 1 3) x (basisVec 2) + w 1 3 x * fderiv ℝ (a 0) x (basisVec 2)) -
        (a 1 x * fderiv ℝ (w 0 3) x (basisVec 2) + w 0 3 x * fderiv ℝ (a 1) x (basisVec 2)) +
        (a 3 x * fderiv ℝ (w 0 1) x (basisVec 2) + w 0 1 x * fderiv ℝ (a 3) x (basisVec 2)) := by
      have h1 : DifferentiableAt ℝ (fun y => a 0 y * w 1 3 y) x := (ha_diff 0).mul (hw_diff 1 3)
      have h2 : DifferentiableAt ℝ (fun y => a 1 y * w 0 3 y) x := (ha_diff 1).mul (hw_diff 0 3)
      have h3 : DifferentiableAt ℝ (fun y => a 3 y * w 0 1 y) x := (ha_diff 3).mul (hw_diff 0 1)
      have hV := congrArg (fun L : X →L[ℝ] ℝ => L (basisVec 2))
        (((h1.hasFDerivAt.sub h2.hasFDerivAt).add h3.hasFDerivAt).fderiv)
      change fderiv ℝ V2 x (basisVec 2) = _ at hV
      simpa only [add_apply, sub_apply, hfd_prod] using hV
    have hV3_x : fderiv ℝ V3 x (basisVec 3) =
        -(a 0 x * fderiv ℝ (w 1 2) x (basisVec 3) + w 1 2 x * fderiv ℝ (a 0) x (basisVec 3)) +
        (a 1 x * fderiv ℝ (w 0 2) x (basisVec 3) + w 0 2 x * fderiv ℝ (a 1) x (basisVec 3)) -
        (a 2 x * fderiv ℝ (w 0 1) x (basisVec 3) + w 0 1 x * fderiv ℝ (a 2) x (basisVec 3)) := by
      have h1 : DifferentiableAt ℝ (fun y => -a 0 y * w 1 2 y) x :=
        ((ha_diff 0).neg).mul (hw_diff 1 2)
      have h2 : DifferentiableAt ℝ (fun y => a 1 y * w 0 2 y) x := (ha_diff 1).mul (hw_diff 0 2)
      have h3 : DifferentiableAt ℝ (fun y => a 2 y * w 0 1 y) x := (ha_diff 2).mul (hw_diff 0 1)
      have hV := congrArg (fun L : X →L[ℝ] ℝ => L (basisVec 3))
        (((h1.hasFDerivAt.add h2.hasFDerivAt).sub h3.hasFDerivAt).fderiv)
      change fderiv ℝ V3 x (basisVec 3) = _ at hV
      simpa only [add_apply, sub_apply, hfd_neg_prod, hfd_prod] using hV
    rw [hV0_x, hV1_x, hV2_x, hV3_x]
    simp only [wedgePair22, wedgePair13, form2Comp, d_form1_apply δA x hdA_x,
      d_form2_apply ω x hω_x]
    change _ = _
    dsimp only [a, w, form1Comp, form2CompFn]
    ring
  have hI1 : Integrable (wedgePair22 (d δA) ω) :=
    (continuous_wedgePair22 (d δA) ω (continuous_d hδA) hω.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_wedgePair22_left _ _ (hasCompactSupport_d h_comp))
  have hI2 : Integrable (wedgePair13 δA (d ω)) :=
    (continuous_wedgePair13 δA (d ω) hδA.continuous (continuous_d hω)).integrable_of_hasCompactSupport
      (hasCompactSupport_wedgePair13_left _ _ h_comp)
  have hIV : ∀ V : X → ℝ, ContDiff ℝ 1 V → HasCompactSupport V → ∀ k : Fin 4,
      Integrable (fun x => fderiv ℝ V x (basisVec k)) := fun V hV hVc k =>
    ((ContinuousLinearMap.apply ℝ ℝ (basisVec k)).continuous.comp
      (hV.fderiv_right (m := 0) (by norm_num)).continuous).integrable_of_hasCompactSupport
      (hVc.fderiv_apply (𝕜 := ℝ) (basisVec k))
  have h_sum_zero : (∫ x : X, wedgePair22 (d δA) ω x) + (∫ x : X, wedgePair13 δA (d ω) x) = 0 := by
    rw [← integral_add hI1 hI2]
    have h_congr : (∫ x : X, wedgePair22 (d δA) ω x + wedgePair13 δA (d ω) x) =
        ∫ x : X, fderiv ℝ V0 x (basisVec 0) + fderiv ℝ V1 x (basisVec 1) +
          fderiv ℝ V2 x (basisVec 2) + fderiv ℝ V3 x (basisVec 3) :=
      integral_congr_ae (Eventually.of_forall h_ptwise)
    have h_split : (∫ x : X, fderiv ℝ V0 x (basisVec 0) + fderiv ℝ V1 x (basisVec 1) +
        fderiv ℝ V2 x (basisVec 2) + fderiv ℝ V3 x (basisVec 3)) =
        (∫ x : X, fderiv ℝ V0 x (basisVec 0)) + (∫ x : X, fderiv ℝ V1 x (basisVec 1)) +
        (∫ x : X, fderiv ℝ V2 x (basisVec 2)) + (∫ x : X, fderiv ℝ V3 x (basisVec 3)) := by
      rw [integral_add
        (f := fun x => fderiv ℝ V0 x (basisVec 0) + fderiv ℝ V1 x (basisVec 1) +
          fderiv ℝ V2 x (basisVec 2))
        (g := fun x => fderiv ℝ V3 x (basisVec 3))
        (((hIV V0 hV0_cd hV0_comp 0).add (hIV V1 hV1_cd hV1_comp 1)).add (hIV V2 hV2_cd hV2_comp 2))
        (hIV V3 hV3_cd hV3_comp 3)]
      rw [integral_add
        (f := fun x => fderiv ℝ V0 x (basisVec 0) + fderiv ℝ V1 x (basisVec 1))
        (g := fun x => fderiv ℝ V2 x (basisVec 2))
        ((hIV V0 hV0_cd hV0_comp 0).add (hIV V1 hV1_cd hV1_comp 1))
        (hIV V2 hV2_cd hV2_comp 2)]
      rw [integral_add
        (f := fun x => fderiv ℝ V0 x (basisVec 0))
        (g := fun x => fderiv ℝ V1 x (basisVec 1))
        (hIV V0 hV0_cd hV0_comp 0) (hIV V1 hV1_cd hV1_comp 1)]
    rw [h_congr, h_split,
      integral_partialDeriv_eq_zero V0 0 hV0_cd hV0_comp,
      integral_partialDeriv_eq_zero V1 1 hV1_cd hV1_comp,
      integral_partialDeriv_eq_zero V2 2 hV2_cd hV2_comp,
      integral_partialDeriv_eq_zero V3 3 hV3_cd hV3_comp]
    ring
  linarith

/-! ## 7. Lemma 4: Fundamental Lemma of Calculus of Variations (`fundamental_lemma_var`) -/

lemma continuous_eq_zero_of_integral_mul_bump_eq_zero (g : X → ℝ) (hg : Continuous g)
    (h : ∀ φ : X → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → (∫ x : X, φ x * g x) = 0) :
    g = 0 := by
  ext x₀
  by_contra hgx₀
  rcases lt_or_gt_of_ne hgx₀ with hneg | hpos
  · have hx₀_pre : x₀ ∈ g ⁻¹' Set.Iio 0 := hneg
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp (hg.isOpen_preimage _ isOpen_Iio) x₀ hx₀_pre
    let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr_pos, half_lt_self hr_pos⟩
    have hb_int : Integrable (fun x => b x * (-g x)) :=
      (b.continuous.mul hg.neg).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
    have hb_nonneg : ∀ x, 0 ≤ b x * (-g x) := by
      intro x
      by_cases hx : x ∈ Metric.ball x₀ r
      · exact mul_nonneg b.nonneg (neg_nonneg.mpr (le_of_lt (hr_sub hx)))
      · have hb0 : b x = 0 := by
          by_contra hne
          have hmem : x ∈ Function.support b := hne
          rw [b.support_eq] at hmem
          exact hx hmem
        simp [hb0]
    have h_pos_int : 0 < ∫ x : X, b x * (-g x) := by
      refine integral_pos_of_integrable_nonneg_ne_zero (x := x₀) (b.continuous.mul hg.neg)
        hb_int hb_nonneg ?_
      have hb_x₀ : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr_pos).le)
      simp [hb_x₀, neg_ne_zero.mpr hneg.ne]
    have h_zero : (∫ x : X, b x * (-g x)) = 0 := by
      have h1 := h b (b.contDiff : ContDiff ℝ 1 b) b.hasCompactSupport
      have h_eq : (fun x => b x * (-g x)) = fun x => -(b x * g x) := by funext x; ring
      rw [h_eq, integral_neg, h1, neg_zero]
    linarith
  · have hx₀_pre : x₀ ∈ g ⁻¹' Set.Ioi 0 := hpos
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp (hg.isOpen_preimage _ isOpen_Ioi) x₀ hx₀_pre
    let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr_pos, half_lt_self hr_pos⟩
    have hb_int : Integrable (fun x => b x * g x) :=
      (b.continuous.mul hg).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
    have hb_nonneg : ∀ x, 0 ≤ b x * g x := by
      intro x
      by_cases hx : x ∈ Metric.ball x₀ r
      · exact mul_nonneg b.nonneg (le_of_lt (hr_sub hx))
      · have hb0 : b x = 0 := by
          by_contra hne
          have hmem : x ∈ Function.support b := hne
          rw [b.support_eq] at hmem
          exact hx hmem
        simp [hb0]
    have h_pos_int : 0 < ∫ x : X, b x * g x := by
      refine integral_pos_of_integrable_nonneg_ne_zero (x := x₀) (b.continuous.mul hg)
        hb_int hb_nonneg ?_
      have hb_x₀ : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr_pos).le)
      simpa [hb_x₀] using ne_of_gt hpos
    have h_zero := h b (b.contDiff : ContDiff ℝ 1 b) b.hasCompactSupport
    linarith

lemma alt3_basis_triples_eq_zero (η : ContinuousAlternatingMap ℝ X ℝ (Fin 3))
    (h0 : η ![basisVec 1, basisVec 2, basisVec 3] = 0)
    (h1 : η ![basisVec 0, basisVec 2, basisVec 3] = 0)
    (h2 : η ![basisVec 0, basisVec 1, basisVec 3] = 0)
    (h3 : η ![basisVec 0, basisVec 1, basisVec 2] = 0)
    (i j k : Fin 4) : η ![basisVec i, basisVec j, basisVec k] = 0 := by
  have h_eq01 : ∀ a b c : Fin 4, a = b → η ![basisVec a, basisVec b, basisVec c] = 0 :=
    fun a b c hab => η.map_eq_zero_of_eq _ (by simp [hab]) (by decide : (0 : Fin 3) ≠ 1)
  have h_eq02 : ∀ a b c : Fin 4, a = c → η ![basisVec a, basisVec b, basisVec c] = 0 :=
    fun a b c hac => η.map_eq_zero_of_eq _ (by simp [hac]) (by decide : (0 : Fin 3) ≠ 2)
  have h_eq12 : ∀ a b c : Fin 4, b = c → η ![basisVec a, basisVec b, basisVec c] = 0 :=
    fun a b c hbc => η.map_eq_zero_of_eq _ (by simp [hbc]) (by decide : (1 : Fin 3) ≠ 2)
  have h_swap01 : ∀ a b c : Fin 4,
      η ![basisVec a, basisVec b, basisVec c] = -η ![basisVec b, basisVec a, basisVec c] := by
    intro a b c
    have h_arg : ![basisVec b, basisVec a, basisVec c] ∘ ⇑(Equiv.swap (0 : Fin 3) 1) =
        ![basisVec a, basisVec b, basisVec c] := by
      ext m; fin_cases m <;> rfl
    change η.toAlternatingMap ![basisVec a, basisVec b, basisVec c] =
      -η.toAlternatingMap ![basisVec b, basisVec a, basisVec c]
    rw [← h_arg]
    exact η.map_swap ![basisVec b, basisVec a, basisVec c] (by decide : (0 : Fin 3) ≠ 1)
  have h_swap12 : ∀ a b c : Fin 4,
      η ![basisVec a, basisVec b, basisVec c] = -η ![basisVec a, basisVec c, basisVec b] := by
    intro a b c
    have h_arg : ![basisVec a, basisVec c, basisVec b] ∘ ⇑(Equiv.swap (1 : Fin 3) 2) =
        ![basisVec a, basisVec b, basisVec c] := by
      ext m; fin_cases m <;> rfl
    change η.toAlternatingMap ![basisVec a, basisVec b, basisVec c] =
      -η.toAlternatingMap ![basisVec a, basisVec c, basisVec b]
    rw [← h_arg]
    exact η.map_swap ![basisVec a, basisVec c, basisVec b] (by decide : (1 : Fin 3) ≠ 2)
  have s01 : ∀ {a b c : Fin 4},
      η ![basisVec b, basisVec a, basisVec c] = 0 →
      η ![basisVec a, basisVec b, basisVec c] = 0 :=
    fun h => by rw [h_swap01, h, neg_zero]
  have s12 : ∀ {a b c : Fin 4},
      η ![basisVec a, basisVec c, basisVec b] = 0 →
      η ![basisVec a, basisVec b, basisVec c] = 0 :=
    fun h => by rw [h_swap12, h, neg_zero]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact h_eq01 _ _ _ rfl
      | exact h_eq02 _ _ _ rfl
      | exact h_eq12 _ _ _ rfl
      | exact h0 | exact h1 | exact h2 | exact h3
      | exact s01 h0 | exact s01 h1 | exact s01 h2 | exact s01 h3
      | exact s12 h0 | exact s12 h1 | exact s12 h2 | exact s12 h3
      | exact s01 (s12 h0) | exact s01 (s12 h1) | exact s01 (s12 h2) | exact s01 (s12 h3)
      | exact s12 (s01 h0) | exact s12 (s01 h1) | exact s12 (s01 h2) | exact s12 (s01 h3)
      | exact s01 (s12 (s01 h0)) | exact s01 (s12 (s01 h1))
      | exact s01 (s12 (s01 h2)) | exact s01 (s12 (s01 h3))

lemma alt3_eq_zero_of_basis_eq_zero (η : ContinuousAlternatingMap ℝ X ℝ (Fin 3))
    (h0 : η ![basisVec 1, basisVec 2, basisVec 3] = 0)
    (h1 : η ![basisVec 0, basisVec 2, basisVec 3] = 0)
    (h2 : η ![basisVec 0, basisVec 1, basisVec 3] = 0)
    (h3 : η ![basisVec 0, basisVec 1, basisVec 2] = 0) :
    η = 0 := by
  ext v
  let b := EuclideanSpace.basisFun (Fin 4) ℝ
  have hv0 : v 0 = ∑ i : Fin 4, inner ℝ (b i) (v 0) • basisVec i := (b.sum_repr' (v 0)).symm
  have hv1 : v 1 = ∑ j : Fin 4, inner ℝ (b j) (v 1) • basisVec j := (b.sum_repr' (v 1)).symm
  have hv2 : v 2 = ∑ k : Fin 4, inner ℝ (b k) (v 2) • basisVec k := (b.sum_repr' (v 2)).symm
  have hv_eq : v = ![v 0, v 1, v 2] := by ext m; fin_cases m <;> rfl
  rw [hv_eq]
  have h_exp : ∀ (x₀ x₁ x₂ : X),
      η ![∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i, x₁, x₂] =
        ∑ i : Fin 4, inner ℝ (b i) x₀ * η ![basisVec i, x₁, x₂] := by
    intro x₀ x₁ x₂
    have h_upd : Function.update ![∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i, x₁, x₂] 0
        (∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i) =
        ![∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i, x₁, x₂] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i, x₁, x₂] = _
    rw [← h_upd, η.toMultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_upd_i : Function.update ![∑ i : Fin 4, inner ℝ (b i) x₀ • basisVec i, x₁, x₂] 0
        (inner ℝ (b i) x₀ • basisVec i) = ![inner ℝ (b i) x₀ • basisVec i, x₁, x₂] := by
      ext m; fin_cases m <;> rfl
    rw [h_upd_i]
    have h_upd_smul : Function.update ![inner ℝ (b i) x₀ • basisVec i, x₁, x₂] 0
        (inner ℝ (b i) x₀ • basisVec i) = ![inner ℝ (b i) x₀ • basisVec i, x₁, x₂] := by
      ext m; fin_cases m <;> rfl
    have h_upd_b : Function.update ![inner ℝ (b i) x₀ • basisVec i, x₁, x₂] 0 (basisVec i) =
        ![basisVec i, x₁, x₂] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![inner ℝ (b i) x₀ • basisVec i, x₁, x₂] = _
    rw [← h_upd_smul, η.toMultilinearMap.map_update_smul, h_upd_b, smul_eq_mul]
    rfl
  have h_exp1 : ∀ (x₀ x₁ x₂ : X),
      η ![x₀, ∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j, x₂] =
        ∑ j : Fin 4, inner ℝ (b j) x₁ * η ![x₀, basisVec j, x₂] := by
    intro x₀ x₁ x₂
    have h_upd : Function.update ![x₀, ∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j, x₂] 1
        (∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j) =
        ![x₀, ∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j, x₂] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![x₀, ∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j, x₂] = _
    rw [← h_upd, η.toMultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h_upd_j : Function.update ![x₀, ∑ j : Fin 4, inner ℝ (b j) x₁ • basisVec j, x₂] 1
        (inner ℝ (b j) x₁ • basisVec j) = ![x₀, inner ℝ (b j) x₁ • basisVec j, x₂] := by
      ext m; fin_cases m <;> rfl
    rw [h_upd_j]
    have h_upd_smul : Function.update ![x₀, inner ℝ (b j) x₁ • basisVec j, x₂] 1
        (inner ℝ (b j) x₁ • basisVec j) = ![x₀, inner ℝ (b j) x₁ • basisVec j, x₂] := by
      ext m; fin_cases m <;> rfl
    have h_upd_b : Function.update ![x₀, inner ℝ (b j) x₁ • basisVec j, x₂] 1 (basisVec j) =
        ![x₀, basisVec j, x₂] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![x₀, inner ℝ (b j) x₁ • basisVec j, x₂] = _
    rw [← h_upd_smul, η.toMultilinearMap.map_update_smul, h_upd_b, smul_eq_mul]
    rfl
  have h_exp2 : ∀ (x₀ x₁ x₂ : X),
      η ![x₀, x₁, ∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k] =
        ∑ k : Fin 4, inner ℝ (b k) x₂ * η ![x₀, x₁, basisVec k] := by
    intro x₀ x₁ x₂
    have h_upd : Function.update ![x₀, x₁, ∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k] 2
        (∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k) =
        ![x₀, x₁, ∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![x₀, x₁, ∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k] = _
    rw [← h_upd, η.toMultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h_upd_k : Function.update ![x₀, x₁, ∑ k : Fin 4, inner ℝ (b k) x₂ • basisVec k] 2
        (inner ℝ (b k) x₂ • basisVec k) = ![x₀, x₁, inner ℝ (b k) x₂ • basisVec k] := by
      ext m; fin_cases m <;> rfl
    rw [h_upd_k]
    have h_upd_smul : Function.update ![x₀, x₁, inner ℝ (b k) x₂ • basisVec k] 2
        (inner ℝ (b k) x₂ • basisVec k) = ![x₀, x₁, inner ℝ (b k) x₂ • basisVec k] := by
      ext m; fin_cases m <;> rfl
    have h_upd_b : Function.update ![x₀, x₁, inner ℝ (b k) x₂ • basisVec k] 2 (basisVec k) =
        ![x₀, x₁, basisVec k] := by
      ext m; fin_cases m <;> rfl
    change η.toMultilinearMap ![x₀, x₁, inner ℝ (b k) x₂ • basisVec k] = _
    rw [← h_upd_smul, η.toMultilinearMap.map_update_smul, h_upd_b, smul_eq_mul]
    rfl
  rw [hv0, h_exp]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hv1, h_exp1]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
  rw [hv2, h_exp2]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
  rw [alt3_basis_triples_eq_zero η h0 h1 h2 h3, mul_zero]

/-- **Lemma 4 (`fundamental_lemma_var`)**: Du Bois-Reymond lemma for continuous 3-forms on `ℝ⁴`. -/
lemma fundamental_lemma_var (ω : Form3) (hω : Continuous ω)
    (h : ∀ δA : Form1, ContDiff ℝ 1 δA → HasCompactSupport δA →
      (∫ x : X, wedgePair13 δA ω x) = 0) :
    ω = 0 := by
  have h_test : ∀ m : Fin 4, ∀ φ : X → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x : X, wedgePair13 (fun y => φ y • basisForm1 m) ω x) = 0 := by
    intro m φ hφ hφ_comp
    exact h (fun y => φ y • basisForm1 m) (hφ.smul contDiff_const) (hφ_comp.smul_right)
  have h_comp0 : (fun x => ω x ![basisVec 1, basisVec 2, basisVec 3]) = 0 := by
    refine continuous_eq_zero_of_integral_mul_bump_eq_zero _
      (continuous_evalAlt_comp hω ![basisVec 1, basisVec 2, basisVec 3]) ?_
    intro φ hφ hφ_comp
    have ht := h_test 0 φ hφ hφ_comp
    have h_eq : (fun x => wedgePair13 (fun y => φ y • basisForm1 0) ω x) =
        fun x => -(φ x * ω x ![basisVec 1, basisVec 2, basisVec 3]) := by
      funext x
      simp [wedgePair13]
    rw [h_eq, integral_neg] at ht
    linarith
  have h_comp1 : (fun x => ω x ![basisVec 0, basisVec 2, basisVec 3]) = 0 := by
    refine continuous_eq_zero_of_integral_mul_bump_eq_zero _
      (continuous_evalAlt_comp hω ![basisVec 0, basisVec 2, basisVec 3]) ?_
    intro φ hφ hφ_comp
    have ht := h_test 1 φ hφ hφ_comp
    have h_eq : (fun x => wedgePair13 (fun y => φ y • basisForm1 1) ω x) =
        fun x => φ x * ω x ![basisVec 0, basisVec 2, basisVec 3] := by
      funext x
      simp [wedgePair13]
    rw [h_eq] at ht
    exact ht
  have h_comp2 : (fun x => ω x ![basisVec 0, basisVec 1, basisVec 3]) = 0 := by
    refine continuous_eq_zero_of_integral_mul_bump_eq_zero _
      (continuous_evalAlt_comp hω ![basisVec 0, basisVec 1, basisVec 3]) ?_
    intro φ hφ hφ_comp
    have ht := h_test 2 φ hφ hφ_comp
    have h_eq : (fun x => wedgePair13 (fun y => φ y • basisForm1 2) ω x) =
        fun x => -(φ x * ω x ![basisVec 0, basisVec 1, basisVec 3]) := by
      funext x
      simp [wedgePair13]
    rw [h_eq, integral_neg] at ht
    linarith
  have h_comp3 : (fun x => ω x ![basisVec 0, basisVec 1, basisVec 2]) = 0 := by
    refine continuous_eq_zero_of_integral_mul_bump_eq_zero _
      (continuous_evalAlt_comp hω ![basisVec 0, basisVec 1, basisVec 2]) ?_
    intro φ hφ hφ_comp
    have ht := h_test 3 φ hφ hφ_comp
    have h_eq : (fun x => wedgePair13 (fun y => φ y • basisForm1 3) ω x) =
        fun x => φ x * ω x ![basisVec 0, basisVec 1, basisVec 2] := by
      funext x
      simp [wedgePair13]
    rw [h_eq] at ht
    exact ht
  funext x
  exact alt3_eq_zero_of_basis_eq_zero (ω x)
    (congrFun h_comp0 x) (congrFun h_comp1 x) (congrFun h_comp2 x) (congrFun h_comp3 x)

/-! ## 8. Main Theorem: Generalized Maxwell Equation (`photon_soul_conservation`) -/

/-- **Main Theorem**: Zero-axiom proof that stationarity of `S_tot` implies `d(⋆F - P_s) = 0`. -/
theorem photon_soul_conservation (P_s : PolarizationForm) (A : Form1)
    (hA : ContDiff ℝ 2 A) (hP : ContDiff ℝ 1 P_s)
    (hL_int : Integrable (L_tot P_s A))
    (h_stat : IsStationary P_s A) :
    d (hodgeStar (fieldStrength A) - P_s) = 0 := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by norm_num)
  have hF_cd : ContDiff ℝ 1 (fieldStrength A) := contDiff_d hA
  have hstar_cd : ContDiff ℝ 1 (hodgeStar (fieldStrength A)) := by
    unfold hodgeStar
    have hc : ∀ i j, ContDiff ℝ 1 (fun x => form2Comp (fieldStrength A) x i j) := fun i j =>
      contDiff_evalAlt_comp hF_cd ![basisVec i, basisVec j]
    refine ((((((hc 2 3).smul contDiff_const).sub
      ((hc 1 3).smul contDiff_const)).add
      ((hc 1 2).smul contDiff_const)).add
      ((hc 0 3).smul contDiff_const)).sub
      ((hc 0 2).smul contDiff_const)).add
      ((hc 0 1).smul contDiff_const)
  have hω_cd : ContDiff ℝ 1 (hodgeStar (fieldStrength A) - P_s) := hstar_cd.sub hP
  refine fundamental_lemma_var (d (hodgeStar (fieldStrength A) - P_s)) (continuous_d hω_cd) ?_
  intro δA hδA h_comp
  have h_deriv_int := deriv_under_integral P_s A δA hA1 hδA hP.continuous h_comp hL_int
  have h_deriv_zero := h_stat δA hδA h_comp
  have h_int_zero : (∫ x : X, deriv_L_tot_eval P_s A δA x) = 0 :=
    h_deriv_int.unique h_deriv_zero
  have h_exp : (∫ x : X, deriv_L_tot_eval P_s A δA x) =
      ∫ x : X, wedgePair22 (d δA) (hodgeStar (fieldStrength A) - P_s) x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact variation_expansion P_s A δA x
      (hA1.differentiable one_ne_zero x) (hδA.differentiable one_ne_zero x)
  rw [h_exp, stokes_integration_by_parts δA (hodgeStar (fieldStrength A) - P_s) hδA hω_cd h_comp]
    at h_int_zero
  linarith

#print axioms photon_soul_conservation
