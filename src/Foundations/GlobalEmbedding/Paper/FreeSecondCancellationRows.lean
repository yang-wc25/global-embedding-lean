import GlobalEmbedding.Paper.FreePolynomialResidual
import GlobalEmbedding.Paper.BalancedDirectionalCalculus
import GlobalEmbedding.Paper.PlanarOrbitDerivativeSmooth
import GlobalEmbedding.Paper.FreeSecondCancellation
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Tactic.LinearCombination

/-!
# Actual metric rows in the second cancellation

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 472–475.
DAG node: `free-second-cancellation-rows`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The actual old free-pairing equations cancel every old quadratic metric row.
Differentiate both first-pairing equations with the already accepted genuine native
inner-product rule. Actual old second-column commutation identifies the two second
terms. Substituting the exact second-pairing equation then leaves minus the genuine
Gram of Z. In the induction, the actual W_H construction discharges both pairing
inputs; this lemma does not assume the desired complete W cancellation.
Source: the old metric rows at lines 472–473. -/
theorem free_old_metric_rows_cancel {a K N : ℕ}
    (F W : M → EuclideanSpace ℝ (Fin K))
    (Z : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ F)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin K)) ∞ W)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (w : Fin a → M → ℝ)
    (hfirst : ∀ x i, inner ℝ (balancedDirectionalDerivative F (D i) x) (W x) = w i x)
    (hcomm : ∀ x i j,
      balancedDirectionalDerivative (balancedDirectionalDerivative F (D j)) (D i) x =
        balancedDirectionalDerivative (balancedDirectionalDerivative F (D i)) (D j) x)
    (hsecond : ∀ x i j,
      2 * inner ℝ
          (balancedDirectionalDerivative (balancedDirectionalDerivative F (D j)) (D i) x)
          (W x) =
        balancedScalarDirectionalDerivative (w j) (D i) x +
          balancedScalarDirectionalDerivative (w i) (D j) x +
          inner ℝ (balancedDirectionalDerivative Z (D i) x)
            (balancedDirectionalDerivative Z (D j) x)) :
    ∀ x, freeMetricCrossTerm F W D x + balancedGeometry Z hZ D x = 0 := by
  intro x
  ext i j
  have hi := balanced_directional_inner
    (balancedDirectionalDerivative F (D j)) W (D i) x
    ((balanced_directional_contMDiff F hF (D j)).mdifferentiableAt (by norm_num))
    (hW.mdifferentiableAt (by norm_num))
  have hj := balanced_directional_inner
    (balancedDirectionalDerivative F (D i)) W (D j) x
    ((balanced_directional_contMDiff F hF (D i)).mdifferentiableAt (by norm_num))
    (hW.mdifferentiableAt (by norm_num))
  have hpi : (fun y ↦ inner ℝ (balancedDirectionalDerivative F (D i) y) (W y)) =
      w i := funext fun y ↦ hfirst y i
  have hpj : (fun y ↦ inner ℝ (balancedDirectionalDerivative F (D j) y) (W y)) =
      w j := funext fun y ↦ hfirst y j
  rw [hpj] at hi
  rw [hpi, ← hcomm x i j] at hj
  have hs := hsecond x i j
  have hsym : inner ℝ (balancedDirectionalDerivative W (D i) x)
      (balancedDirectionalDerivative F (D j) x) =
      inner ℝ (balancedDirectionalDerivative F (D j) x)
        (balancedDirectionalDerivative W (D i) x) := real_inner_comm _ _
  change inner ℝ (balancedDirectionalDerivative F (D i) x)
      (balancedDirectionalDerivative W (D j) x) +
    inner ℝ (balancedDirectionalDerivative W (D i) x)
      (balancedDirectionalDerivative F (D j) x) +
    inner ℝ (balancedDirectionalDerivative Z (D i) x)
      (balancedDirectionalDerivative Z (D j) x) = 0
  linarith

/-- The literal planar component of W, using its actual unit velocity v and the
actual scalar u,b. Source: W=(W_H,uv+bJ₂v,0_m) at line 473. -/
noncomputable def freePlanarSecondCorrection (v : M → Planar) (u b : M → ℝ) : M → Planar :=
  fun x ↦ u x • v x + b x • planarQuarterTurn (v x)

omit [IsManifold I ∞ M] in
/-- The actual planar correction is native smooth. Its quarter-turn coordinates
are exactly (-v₁,v₀); the genuine fixed PiLp coordinate equivalence then supplies
native smoothness, followed by the genuine scalar multiplication and addition.
Source: the actual planar component in line 473. -/
theorem freePlanarSecondCorrection_contMDiff (v : M → Planar) (u b : M → ℝ)
    (hv : ContMDiff I 𝓘(ℝ, Planar) ∞ v)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) :
    ContMDiff I 𝓘(ℝ, Planar) ∞ (freePlanarSecondCorrection v u b) := by
  have hJ : ContMDiff I 𝓘(ℝ, Planar) ∞ (fun x ↦ planarQuarterTurn (v x)) := by
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
    apply e.contDiff.contMDiff.comp
    apply contMDiff_pi_module_iff.mpr
    intro i
    fin_cases i
    · exact ((EuclideanSpace.proj 1).contDiff.contMDiff.comp hv).neg
    · exact (EuclideanSpace.proj 0).contDiff.contMDiff.comp hv
  exact (hu.smul hv).add (hb.smul hJ)

omit [IsManifold I ∞ M] in
/-- Differentiating the literal planar component of W gives its actual active
metric row 2Xu−2κb. Apply genuine HasDerivAt rules to both real coordinates of
uv+bJv, use the actual equation Xv=κJv, and the actual Euclidean norm |v|=1.
In particular no derivative of b, and no division by κ, remains in this pairing.
Source: the active row in lines 473–474. -/
theorem freePlanarSecondCorrection_active_row
    (R : PeriodOneSmoothFlow I M) (v : M → Planar) (u b κ : M → ℝ)
    (hv : ContMDiff I 𝓘(ℝ, Planar) ∞ v)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ x, ‖v x‖ = 1)
    (hacc : ∀ x, orbitDeriv R.flow v x = κ x • planarQuarterTurn (v x)) (x : M) :
    2 * inner ℝ (v x) (orbitDeriv R.flow (freePlanarSecondCorrection v u b) x) =
      2 * orbitDeriv R.flow u x - 2 * κ x * b x := by
  have du : HasDerivAt (fun t : ℝ ↦ u (R.flow t x)) (orbitDeriv R.flow u x) 0 := by
    simpa only [R.flow_zero] using hasDerivAt_orbit R.flow R.smooth R.flow_add u hu 0 x
  have db : HasDerivAt (fun t : ℝ ↦ b (R.flow t x)) (orbitDeriv R.flow b x) 0 := by
    simpa only [R.flow_zero] using hasDerivAt_orbit R.flow R.smooth R.flow_add b hb 0 x
  have dv : HasDerivAt (fun t : ℝ ↦ v (R.flow t x)) (orbitDeriv R.flow v x) 0 := by
    simpa only [R.flow_zero] using hasDerivAt_orbit R.flow R.smooth R.flow_add v hv 0 x
  have dv0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt 0 dv
  have dv1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt 0 dv
  have hw := freePlanarSecondCorrection_contMDiff v u b hv hu hb
  have dw : HasDerivAt (fun t : ℝ ↦ freePlanarSecondCorrection v u b (R.flow t x))
      (orbitDeriv R.flow (freePlanarSecondCorrection v u b) x) 0 := by
    simpa only [R.flow_zero] using
      hasDerivAt_orbit R.flow R.smooth R.flow_add _ hw 0 x
  have dw0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp_hasDerivAt 0 dw
  have dw1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp_hasDerivAt 0 dw
  have heq0 : (fun t : ℝ ↦ freePlanarSecondCorrection v u b (R.flow t x) 0) =
      fun t ↦ u (R.flow t x) * v (R.flow t x) 0 - b (R.flow t x) * v (R.flow t x) 1 := by
    funext t
    simp [freePlanarSecondCorrection, planarQuarterTurn, sub_eq_add_neg]
  have heq1 : (fun t : ℝ ↦ freePlanarSecondCorrection v u b (R.flow t x) 1) =
      fun t ↦ u (R.flow t x) * v (R.flow t x) 1 + b (R.flow t x) * v (R.flow t x) 0 := by
    funext t
    rfl
  change HasDerivAt (fun t : ℝ ↦ freePlanarSecondCorrection v u b (R.flow t x) 0) _ 0 at dw0
  change HasDerivAt (fun t : ℝ ↦ freePlanarSecondCorrection v u b (R.flow t x) 1) _ 0 at dw1
  rw [heq0] at dw0
  rw [heq1] at dw1
  have h0 := dw0.unique ((du.mul dv0).sub (db.mul dv1))
  have h1 := dw1.unique ((du.mul dv1).add (db.mul dv0))
  have ha0 := congrArg (fun y : Planar ↦ y 0) (hacc x)
  have ha1 := congrArg (fun y : Planar ↦ y 1) (hacc x)
  change orbitDeriv R.flow v x 0 = κ x * -v x 1 at ha0
  change orbitDeriv R.flow v x 1 = κ x * v x 0 at ha1
  have hn : v x 0 ^ 2 + v x 1 ^ 2 = 1 := by
    have hh := congrArg (fun r : ℝ ↦ r ^ 2) (hunit x)
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, one_pow] using hh
  simp only [Function.comp_apply, EuclideanSpace.coe_proj, R.flow_zero] at h0 h1
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    star_trivial]
  rw [h0, h1, ha0, ha1]
  linear_combination (2 * orbitDeriv R.flow u x - 2 * κ x * b x) * hn

omit [IsManifold I ∞ M] in
/-- Along an old factor, the actual planar contribution to the mixed metric row
is exactly Y_i u. The new-factor velocity v is unchanged by that old flow. Hence
inner(v(x),W_planar(S_t x))=u(S_t x), using its unit norm and orthogonality to Jv.
Differentiate this actual scalar function with the genuine fixed inner-product CLM.
Source: the planar contribution Y_i u to the mixed row at line 473. -/
theorem freePlanarSecondCorrection_old_row (S : PeriodOneSmoothFlow I M)
    (v : M → Planar) (u b : M → ℝ)
    (hv : ContMDiff I 𝓘(ℝ, Planar) ∞ v)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ x, ‖v x‖ = 1) (hbasic : ∀ t x, v (S.flow t x) = v x) (x : M) :
    inner ℝ (v x) (orbitDeriv S.flow (freePlanarSecondCorrection v u b) x) =
      orbitDeriv S.flow u x := by
  have hJ : inner ℝ (v x) (planarQuarterTurn (v x)) = 0 := by
    simp [planarQuarterTurn, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two]
    ring
  have hself : inner ℝ (v x) (v x) = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit x]
    norm_num
  have heq : (fun t : ℝ ↦ inner ℝ (v x)
      (freePlanarSecondCorrection v u b (S.flow t x))) =
      fun t ↦ u (S.flow t x) := by
    funext t
    simp only [freePlanarSecondCorrection, hbasic, inner_add_right,
      real_inner_smul_right, hJ, hself, mul_one, mul_zero, add_zero]
  have hw := freePlanarSecondCorrection_contMDiff v u b hv hu hb
  have dw : HasDerivAt (fun t : ℝ ↦ freePlanarSecondCorrection v u b (S.flow t x))
      (orbitDeriv S.flow (freePlanarSecondCorrection v u b) x) 0 := by
    simpa only [S.flow_zero] using hasDerivAt_orbit S.flow S.smooth S.flow_add _ hw 0 x
  have hd := (innerSL ℝ (v x)).hasFDerivAt.comp_hasDerivAt 0 dw
  change HasDerivAt (fun t : ℝ ↦ inner ℝ (v x)
    (freePlanarSecondCorrection v u b (S.flow t x))) _ 0 at hd
  rw [heq] at hd
  have du : HasDerivAt (fun t : ℝ ↦ u (S.flow t x)) (orbitDeriv S.flow u x) 0 := by
    simpa only [S.flow_zero] using hasDerivAt_orbit S.flow S.smooth S.flow_add u hu 0 x
  exact hd.unique du

section Ordinary

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [TopologicalSpace Q] [ChartedSpace P Q]
  [IsManifold 𝓘(ℝ, P) ∞ Q]

/-- The actual planar component built from the literal u and b cancels the whole
active energy e, including the curvature-zero set. Native smoothness and the true
primitive derivative come from the already constructed scalar correction, so u, b
and the desired cancellation are not extra input data.
Source: the active row of the genuine W in lines 473–474. -/
theorem freePlanarSecondCorrection_active_cancel
    (R : PeriodOneSmoothFlow 𝓘(ℝ, P) Q) (v : Q → Planar) (κ e : Q → ℝ)
    (hv : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Planar) ∞ v)
    (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0)
    (hunit : ∀ x, ‖v x‖ = 1)
    (hacc : ∀ x, orbitDeriv R.flow v x = κ x • planarQuarterTurn (v x)) (x : Q) :
    2 * inner ℝ (v x) (orbitDeriv R.flow
        (freePlanarSecondCorrection v (freeCancellationU R.flow κ e)
          (freeCancellationB R.flow κ e)) x) = -e x := by
  rw [freePlanarSecondCorrection_active_row R v _ _ κ hv
    (freeCancellationU_contMDiff R κ e hκ he hn)
    (freeCancellationB_contMDiff R κ e hκ he hn) hunit hacc x]
  exact freeCancellationU_active_row R κ e hκ he hn x

/-- The literal w_i and actual old derivative of the planar W component cancel
the actual mixed energy g_i. Along an old flow v is basic, so its real planar
pairing is Y_i u by the preceding actual derivative theorem. The true primitive
construction then gives Xw_i+Y_i u=-g_i from the actual mixed zero period.
No desired antiderivative or planar cancellation is assumed.
Source: the whole mixed row in lines 473–474. -/
theorem freePlanarSecondCorrection_mixed_cancel
    (R S : PeriodOneSmoothFlow 𝓘(ℝ, P) Q)
    (hcomm : ∀ t s x, R.flow t (S.flow s x) = S.flow s (R.flow t x))
    (v : Q → Planar) (κ e g : Q → ℝ)
    (hv : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Planar) ∞ v)
    (hκ : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ κ)
    (he : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ e)
    (hg : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, ℝ) ∞ g)
    (hn : ∀ x, ∃ s : ℝ, κ (R.flow s x) ≠ 0)
    (hunit : ∀ x, ‖v x‖ = 1) (hbasic : ∀ t x, v (S.flow t x) = v x)
    (hmean : ∀ x, orbitAverage R.flow g x = 0) (x : Q) :
    orbitDeriv R.flow (freeCancellationW R.flow S.flow κ e g) x +
        inner ℝ (v x) (orbitDeriv S.flow
          (freePlanarSecondCorrection v (freeCancellationU R.flow κ e)
            (freeCancellationB R.flow κ e)) x) = -g x := by
  rw [freePlanarSecondCorrection_old_row S v _ _ hv
    (freeCancellationU_contMDiff R κ e hκ he hn)
    (freeCancellationB_contMDiff R κ e hκ he hn) hunit hbasic x]
  exact freeCancellationW_mixed_row R S hcomm κ e g hκ he hg hn hmean x

end Ordinary

#print axioms free_old_metric_rows_cancel
#print axioms freePlanarSecondCorrection_contMDiff
#print axioms freePlanarSecondCorrection_active_row
#print axioms freePlanarSecondCorrection_old_row
#print axioms freePlanarSecondCorrection_active_cancel
#print axioms freePlanarSecondCorrection_mixed_cancel

end GlobalEmbedding.Paper
