import Initialization.Phase.ChartPhaseDefinitions
import Initialization.Phase.SelectorReference
import Initialization.Phase.SelectorSecondBounds

/-!
# Actual positive phase margin in a rescaled chart

The chart representative need only have a smooth germ at the point under
consideration. Its derivative, Hessian, derivative-range normal projection and
the original `bestPhaseSupremum` are all literal. This avoids treating an inverse
chart's arbitrary values outside its target as a globally smooth map.

The tolerance is fixed from the selector and uniform coefficient reserves before
any scale, chart or point. The final colored construction supplies its two error
budgets using the actual producers in the other initialization files.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance chartPhaseRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance chartPhaseSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- C² regularity of just this germ identifies the entire canonical operator
with the actual projected Hessian on every symmetric product. -/
theorem chartNormalSecondJet_product {N : ℕ}
    {u : E → EuclideanSpace ℝ (Fin N)} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    chartNormalSecondJet u x (symmetricSquareProduct E v w) =
      (LinearMap.range (fderiv ℝ u x).toLinearMap)ᗮ.starProjection
        (fderiv ℝ (fderiv ℝ u) x v w) := by
  rw [chartNormalSecondJet, ContinuousLinearMap.comp_apply, coordinateHessianJet_product hu]

private theorem exists_chart_jet_tolerance (lam bound ε L : ℝ)
    (hlam : 0 < lam) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.sqrt lam / 2 ∧
      (1 + (3 / Real.sqrt lam) * max 0 bound) * δ < ε / (2 * (1 + L ^ 2)) := by
  let reserve : ℝ := 1 + L ^ 2
  let gain : ℝ := 1 + (3 / Real.sqrt lam) * max 0 bound
  have hreserve : 0 < reserve := by dsimp [reserve]; positivity
  have hgain : 0 < gain := by dsimp [gain]; positivity
  let δ := min (Real.sqrt lam / 2) (ε / (4 * reserve * gain))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  have hproduct : gain * δ ≤ ε / (4 * reserve) := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * reserve * gain)).mp
      (min_le_right (Real.sqrt lam / 2) (ε / (4 * reserve * gain)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * reserve)).mpr
    nlinarith
  apply hproduct.trans_lt
  apply (div_lt_div_iff₀ (by positivity : 0 < 4 * reserve)
    (by positivity : 0 < 2 * reserve)).mpr
  nlinarith

private theorem restriction_injective_of_positive_lower
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ E) (R : SymmetricSquare E →L[ℝ] V)
    (ξ : E →L[ℝ] ℝ) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ≤ ‖covectorRestriction R ξ u‖) :
    Function.Injective (covectorRestriction R ξ) := by
  have : Nontrivial ξ.ker := covector_kernel_nontrivial hdim ξ
  have : Nontrivial (SymmetricSquare ξ.ker) := symmetric_square_nontrivial
  have hleast := (least_singular_norm_bound (E := SymmetricSquare ξ.ker) (F := V)
    (covectorRestriction (E := E) (F := V) R ξ)).2.2 a |>.mpr hlower
  exact (covector_restriction_bound hdim R ξ).2.2.mp (ha.trans_le hleast)

private theorem injective_of_positive_square_lower
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : U →L[ℝ] V) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ u, a * ‖u‖ ^ 2 ≤ ‖A u‖ ^ 2) : Function.Injective A := by
  apply (injective_iff_map_eq_zero A).mpr
  intro u hu
  have h := hlower u
  rw [hu, norm_zero, zero_pow (by decide)] at h
  have hn : ‖u‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

variable {m : ℕ} {C : Fin (m + 1) → ℕ} [∀ i, Fact (0 < C i)]

/-- Uniform actual chartwise phase stability. The sphere argument, coframe,
their derivatives and the selected map are the very same functions throughout.
Only a smooth germ of the sphere argument is required; no global smooth inverse
chart, desired margin, formal hyperplane or independently prescribed jet occurs. -/
theorem selector_chart_phase_stability
    (hdim : 2 ≤ Module.finrank ℝ E) (P : SelectorPhaseReference C)
    (A L Rbound : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (z : E → FreeHopfProduct C)
      (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) (x : E)
      (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))),
      e.toContinuousLinearMap = c x →
      ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x →
      ‖e.toContinuousLinearMap‖ ≤ A → ‖e.symm.toContinuousLinearMap‖ ≤ L →
      ‖actualHessianLift (fderiv ℝ c x)‖ ≤ Rbound →
      ‖(selectorIdealFirstJet C P.selector (z x)).comp (c x) -
        fderiv ℝ (P.selector ∘ z) x‖ ≤ δ →
      ‖coordinateHessianJet (P.selector ∘ z) x -
        ((selectorIdealSecondJet C P.selector (z x)).comp (symmetricSquareMapL (c x)) +
          (selectorIdealFirstJet C P.selector (z x)).comp (actualHessianLift (fderiv ℝ c x)))‖ ≤ δ →
      Function.Injective (fderiv ℝ (P.selector ∘ z) x) ∧
      P.retainedMargin L ≤ chartPhaseMargin (P.selector ∘ z) x ∧
      Function.Injective (covectorRestriction (chartNormalSecondJet (P.selector ∘ z) x)
        (unitCoefficientCovector e (lastCoordinateCovector m))) ∧
      ∀ v w, chartNormalSecondJet (P.selector ∘ z) x (symmetricSquareProduct E v w) =
        (LinearMap.range (fderiv ℝ (P.selector ∘ z) x).toLinearMap)ᗮ.starProjection
          (fderiv ℝ (fderiv ℝ (P.selector ∘ z)) x v w) := by
  let lam : ℝ := (1 / (1 + L)) ^ 2
  let bound : ℝ := P.secondBound * A ^ 2 + Rbound
  have hlam : 0 < lam := by dsimp [lam]; positivity
  obtain ⟨δ, hδ, hδfirst, hsmall⟩ :=
    exists_chart_jet_tolerance lam bound P.margin L hlam P.margin_pos
  refine ⟨δ, hδ, ?_⟩
  intro z c x e heq hz hcnorm hcinv hR hfirst hsecond
  let idealFirst := (selectorIdealFirstJet C P.selector (z x)).comp e.toContinuousLinearMap
  let correction := actualHessianLift (fderiv ℝ c x)
  let idealSecond := selectorCoframeSecondJet C P.selector (z x) e correction
  let candidateFirst := fderiv ℝ (P.selector ∘ z) x
  let candidateSecond := coordinateHessianJet (P.selector ∘ z) x
  let ξ := unitCoefficientCovector e (lastCoordinateCovector m)
  let transport := coframeOldHyperplaneEquiv e
  let oldForm := (selectorOldSecondForm C P.selector P.smooth (z x)).toContinuousLinearMap
  have hcoercive (v : E) : lam * ‖v‖ ^ 2 ≤ ‖idealFirst v‖ ^ 2 := by
    have hv := idealFirstJet_lower_bound (fun i ↦ freeHopfDeriv C i P.selector (z x))
      (P.gram (z x)) e L hcinv v
    have hs := (sq_le_sq₀ (show 0 ≤ (1 / (1 + L)) * ‖v‖ by positivity)
      (norm_nonneg ((gramFrame (fun i ↦ freeHopfDeriv C i P.selector (z x))).comp
        e.toContinuousLinearMap v))).2 hv
    simpa only [mul_pow, lam, idealFirst, selectorIdealFirstJet] using hs
  have hbound : ‖idealSecond‖ ≤ bound := by
    apply (selectorCoframeSecondJet_norm_le C P.selector P.gram (z x) e correction).trans
    apply add_le_add _ hR
    exact ((mul_le_mul_of_nonneg_right (P.second_norm (z x)) (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg e.toContinuousLinearMap) hA).2 hcnorm) P.secondBound_pos.le)
  have hAB : ‖idealFirst - candidateFirst‖ ≤ δ := by
    simpa only [idealFirst, candidateFirst, heq] using hfirst
  have hQQ : ‖candidateSecond - idealSecond‖ ≤ δ := by
    simpa only [candidateSecond, idealSecond, selectorCoframeSecondJet, correction, heq] using hsecond
  have hp := pointwise_projected_jet_estimate idealFirst candidateFirst idealSecond candidateSecond
    lam bound hlam hcoercive (hAB.trans hδfirst) hbound
  let referenceProjected := (LinearMap.range idealFirst.toLinearMap)ᗮ.starProjection.comp idealSecond
  let candidateProjected := chartNormalSecondJet (P.selector ∘ z) x
  have herr : ‖candidateProjected - referenceProjected‖ < P.retainedMargin L := by
    apply hp.2.trans_lt
    apply lt_of_le_of_lt _ hsmall
    have hcoef : (3 / Real.sqrt lam) * bound ≤ (3 / Real.sqrt lam) * max 0 bound :=
      mul_le_mul_of_nonneg_left (le_max_right 0 bound) (by positivity)
    calc
      _ ≤ δ + ((3 / Real.sqrt lam) * max 0 bound) * δ :=
        add_le_add hQQ
          ((mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hAB (by positivity)))
      _ = _ := by ring
  have hrestriction : covectorRestriction referenceProjected ξ =
      oldForm.comp (symmetricSquareMapL transport.toContinuousLinearMap) :=
    selectorCoframe_restriction C P.selector P.smooth P.gram (z x) e correction
  have hrestrict : ‖covectorRestriction candidateProjected ξ -
      covectorRestriction referenceProjected ξ‖ ≤ ‖candidateProjected - referenceProjected‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    have h := (candidateProjected - referenceProjected).le_opNorm
      (symmetricSquareMapL ξ.ker.subtypeL u)
    rw [symmetric_square_subspace_isometry ξ.ker u] at h
    exact h
  have htrans := (phase_stability_transport_uniform_lower_bound transport oldForm
    (covectorRestriction candidateProjected ξ) P.margin L P.margin_pos
    ((coframeOldHyperplaneEquiv_inverse_norm_le e).trans hcinv) (P.lower (z x))
    (by rw [← hrestriction]; exact hrestrict.trans_lt herr)).2
  have hunit : ‖ξ‖ = 1 := unitCoefficientCovector_norm e (lastCoordinateCovector m)
    (lastCoordinateCovector_ne_zero m)
  have hmargin : P.retainedMargin L ≤ chartPhaseMargin (P.selector ∘ z) x :=
    (best_phase_supremum_specification hdim candidateProjected).2.2.2
      ξ _ hunit htrans
  refine ⟨?_, hmargin, ?_, ?_⟩
  · exact injective_of_positive_square_lower candidateFirst (lam / 4)
      (by positivity) hp.1
  · exact restriction_injective_of_positive_lower hdim candidateProjected ξ
      (P.retainedMargin L) (P.retainedMargin_pos L) htrans

  · intro v w
    exact chartNormalSecondJet_product
      ((selectorSource_contDiffAt C P.selector P.smooth z hz).of_le (by simp)) v w

end GlobalEmbedding.Initialization
