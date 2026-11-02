import GlobalEmbedding.Offline.ImmersionRescaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact metric identity for an update of the actual map

Source: `literature/parallelizable-stable-plus-one/main.tex`, equations (6.6)
and (6.9), and the original DAG node `repair-one-step`.

All metrics below are the original `GlobalEmbedding.Paper.inducedMetric`.
The map `S` may later be instantiated by the actual smoothed map. No smoothing
operator or analytic estimates are assumed in this algebraic identity. In
particular the second-order term `γ(U)` cancels exactly between the two updates;
there is no term `γ(G-S)`.

This is an isolated offline candidate, not a claim of main-library acceptance.
-/

noncomputable section

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Offline

open GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}

/-- The actual bilinear cross term of two map differentials, with the exact
target-tangent casts used by `inducedMetric`. Its value on `v,w` is
`⟪dF v,dU w⟫ + ⟪dU v,dF w⟫`. This is the symmetric cross tensor in (6.6).
No arbitrary derivative data are parameters of this definition. -/
def metricCrossTerm (F U : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  let DF :=
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)
  let DU :=
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (U x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) U x)
  LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      DF.toLinearMap DU.toLinearMap +
    LinearMap.BilinForm.comp (innerₗ (EuclideanSpace ℝ (Fin N)))
      DU.toLinearMap DF.toLinearMap

/-- The actual ambient differential of a sum is the sum of the two ambient
differentials. Proof: the native manifold derivative addition rule, evaluated
through the original canonical Euclidean target casts. Source: (6.6). -/
theorem ambientDerivative_add
    (F U : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : M) :
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ((F + U) x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F + U) x) =
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x) +
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (U x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) U x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun
    (mfderiv_add ((hF x).mdifferentiableAt (by simp))
      ((hU x).mdifferentiableAt (by simp))) v

/-- The analogous actual ambient derivative subtraction identity.
Proof: the native manifold derivative subtraction rule. Source: (6.6). -/
theorem ambientDerivative_sub
    (F S : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hS : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : M) :
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ((F - S) x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F - S) x) =
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x) -
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (S x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) S x) := by
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun
    (mfderiv_sub ((hF x).mdifferentiableAt (by simp))
      ((hS x).mdifferentiableAt (by simp))) v

/-- Exact quadratic expansion of the original induced metric of the sum map.
Proof: expand both entries of the real inner product after the actual derivative
addition identity. Equality is of the entire tangent bilinear form.
Source: the quadratic metric expansion used in (6.6). -/
theorem inducedMetric_add
    (F U : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : M) :
    inducedMetric (I := I) (F + U) x = inducedMetric (I := I) F x +
      metricCrossTerm (I := I) F U x + inducedMetric (I := I) U x := by
  unfold inducedMetric metricCrossTerm
  rw [ambientDerivative_add F U hF hU]
  ext v w
  simp only [LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe,
    add_apply, LinearMap.add_apply, innerₗ_apply_apply, inner_add_left, inner_add_right]
  ring

/-- Linearity in the first map of the actual cross tensor for a difference of
smooth maps. Proof: expand the two real-inner-product subtraction identities
after the actual derivative subtraction formula. Source: (6.6). -/
theorem metricCrossTerm_sub_left
    (G S U : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (hS : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (x : M) :
    metricCrossTerm (I := I) (G - S) U x =
      metricCrossTerm (I := I) G U x - metricCrossTerm (I := I) S U x := by
  unfold metricCrossTerm
  rw [ambientDerivative_sub G S hG hS]
  ext v w
  simp only [LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe,
    sub_apply, LinearMap.add_apply, LinearMap.sub_apply,
    innerₗ_apply_apply, inner_sub_left, inner_sub_right]
  ring

/-- The actual-map identity underlying (6.6): comparing the same increment at
`G` and at `S` leaves exactly `Cross(G-S,U)`. Both occurrences of `γ(U)` cancel.
Proof: subtract the two exact expansions and use linearity of the cross tensor.
No derivative or metric of the smoothing error is supplied as a hypothesis.
Source: (6.6), the true-map update, before defect normalization. -/
theorem inducedMetric_actual_update
    (G S U : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (hS : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : M) :
    inducedMetric (I := I) (G + U) x - inducedMetric (I := I) G x -
        (inducedMetric (I := I) (S + U) x - inducedMetric (I := I) S x) =
      metricCrossTerm (I := I) (G - S) U x := by
  rw [inducedMetric_add G U hG hU, inducedMetric_add S U hS hU,
    metricCrossTerm_sub_left G S U hG hS]
  abel

/-- Equation (6.6) for the actual maps and any exact representations of their
normalized defects. The only increment premise is the finite solver's metric
identity at the smoothed map `S`; the update itself is the actual `G+U`.

Proof: use `inducedMetric_actual_update`, substitute the finite increment,
cancel `delta²*(deltaNext/delta)²=deltaNext²`, and then substitute both defect
identities. The result is an exact equality of the original bilinear forms.
Source: (6.6), with `S=S_ell G` and `Hslow=S_ell H`. -/
theorem repair_defect_identity
    (G S U : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (hS : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : M) (delta deltaNext : ℝ) (hdelta : delta ≠ 0)
    (hstar h0 Hcurrent Hslow Hnext error : LinearMap.BilinForm ℝ (TangentSpace I x))
    (hcurrent : delta ^ 2 • Hcurrent = hstar - inducedMetric (I := I) G x)
    (hnext : deltaNext ^ 2 • Hnext = hstar - inducedMetric (I := I) (G + U) x)
    (hincrement : inducedMetric (I := I) (S + U) x = inducedMetric (I := I) S x +
      delta ^ 2 • (Hslow - (deltaNext / delta) ^ 2 • h0) + error) :
    deltaNext ^ 2 • (Hnext - h0) =
      delta ^ 2 • (Hcurrent - Hslow) - error - metricCrossTerm (I := I) (G - S) U x := by
  have hscale : delta ^ 2 * (deltaNext / delta) ^ 2 = deltaNext ^ 2 := by
    field_simp
  have hscaled : delta ^ 2 • (Hslow - (deltaNext / delta) ^ 2 • h0) =
      delta ^ 2 • Hslow - deltaNext ^ 2 • h0 := by
    ext v w
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    rw [mul_sub, ← mul_assoc, hscale]
  have hinc : inducedMetric (I := I) (S + U) x - inducedMetric (I := I) S x =
      delta ^ 2 • Hslow - deltaNext ^ 2 • h0 + error := by
    rw [hincrement, hscaled]
    abel
  have hupdate := inducedMetric_actual_update G S U hG hS hU x
  rw [hinc] at hupdate
  have htotal : inducedMetric (I := I) (G + U) x =
      metricCrossTerm (I := I) (G - S) U x +
        (delta ^ 2 • Hslow - deltaNext ^ 2 • h0 + error) + inducedMetric (I := I) G x := by
    ext v w
    have h := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) ↦ B v w) hupdate
    simp only [LinearMap.sub_apply, LinearMap.add_apply] at h ⊢
    linarith
  ext v w
  have hc := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) ↦ B v w) hcurrent
  have hn := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) ↦ B v w) hnext
  have ht := congrArg (fun B : LinearMap.BilinForm ℝ (TangentSpace I x) ↦ B v w) htotal
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.sub_apply, LinearMap.add_apply]
    at hc hn ht ⊢
  linear_combination hn - hc - ht

/-- The same exact equation with both normalized defects defined from the
actual maps, rather than supplied as separate data.
Proof: nonzero scales cancel their inverse squares; apply the actual-map defect
identity above. Source: the literal definitions in (6.5) and (6.6). -/
theorem repair_normalized_defect_identity
    (G S U : M → EuclideanSpace ℝ (Fin N))
    (hG : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ G)
    (hS : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (x : M) (delta deltaNext : ℝ) (hdelta : delta ≠ 0) (hdeltaNext : deltaNext ≠ 0)
    (hstar h0 Hslow error : LinearMap.BilinForm ℝ (TangentSpace I x))
    (hincrement : inducedMetric (I := I) (S + U) x = inducedMetric (I := I) S x +
      delta ^ 2 • (Hslow - (deltaNext / delta) ^ 2 • h0) + error) :
    let Hcurrent := (delta ^ 2)⁻¹ • (hstar - inducedMetric (I := I) G x)
    let Hnext := (deltaNext ^ 2)⁻¹ • (hstar - inducedMetric (I := I) (G + U) x)
    deltaNext ^ 2 • (Hnext - h0) =
      delta ^ 2 • (Hcurrent - Hslow) - error - metricCrossTerm (I := I) (G - S) U x := by
  dsimp only
  apply repair_defect_identity G S U hG hS hU x delta deltaNext hdelta
    hstar h0 _ Hslow _ error
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hdelta), one_smul]
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hdeltaNext), one_smul]
  · exact hincrement

/-- The initial square-root contraction has exactly the claimed metric.
Proof: apply actual metric scaling and the real nonnegative square-root square
identity. Source: the definition of `G_0` in (6.9). -/
theorem repair_initial_metric
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (delta : ℝ) (hdelta : delta ^ 2 ≤ 1) (x : M) :
    inducedMetric (I := I) (Real.sqrt (1 - delta ^ 2) • F) x =
      (1 - delta ^ 2) • inducedMetric (I := I) F x := by
  rw [inducedMetric_const_rescale F hF, Real.sq_sqrt (sub_nonneg.mpr hdelta)]

/-- The literal normalized initial defect in (6.9), with the original induced
metric and the actual contracted map.
Proof: substitute `repair_initial_metric`, expand scalar multiplication and
cancel the nonzero square. This proves the normalization, not an assumption of
an already-normalized defect. Source: equation (6.9). -/
theorem repair_initial_normalized_defect
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (delta : ℝ) (hdelta : delta ≠ 0) (hsmall : delta ^ 2 ≤ 1) (x : M)
    (hstar : LinearMap.BilinForm ℝ (TangentSpace I x)) :
    (delta ^ 2)⁻¹ • (hstar -
        inducedMetric (I := I) (Real.sqrt (1 - delta ^ 2) • F) x) =
      inducedMetric (I := I) F x +
        (delta ^ 2)⁻¹ • (hstar - inducedMetric (I := I) F x) := by
  rw [repair_initial_metric F hF delta hsmall]
  ext v w
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.sub_apply, LinearMap.add_apply]
  field_simp
  ring

#print axioms ambientDerivative_add
#print axioms ambientDerivative_sub
#print axioms inducedMetric_add
#print axioms metricCrossTerm_sub_left
#print axioms inducedMetric_actual_update
#print axioms repair_defect_identity
#print axioms repair_normalized_defect_identity
#print axioms repair_initial_metric
#print axioms repair_initial_normalized_defect

end GlobalEmbedding.Offline
