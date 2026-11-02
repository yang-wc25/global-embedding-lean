import Initialization.Colored.ActualPhaseRows
import Initialization.Assembly.ActualRateBounds

/-!
# Actual scalar rate-error budgets

This is the literal coordinate projection of the internally proved vector
rate discrepancy. The equality is proved on an actual neighborhood before
differentiation. The preparation hypotheses of the wave estimate are therefore
outputs of the original metric and actual geometry, not assumptions.
-/

noncomputable section
open Set Function Filter Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

section Rows
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Exact projection of the actual frequency-weighted derivative discrepancy. -/
theorem scalarPhaseRate_eq_row {n : ℕ} (ℓ : E → EuclideanSpace ℝ (Fin n))
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ℝ) (x : E)
    (hℓ : DifferentiableAt ℝ ℓ x) (l : Fin n) :
    T • fderiv ℝ (fun y ↦ ℓ y l) x - (EuclideanSpace.proj l).comp (c x) =
      realCovectorRow l (T • fderiv ℝ ℓ x - c x) := by
  have hp := ((EuclideanSpace.proj l).hasFDerivAt.comp x hℓ.hasFDerivAt).fderiv
  change T • fderiv ℝ ((EuclideanSpace.proj l) ∘ ℓ) x - _ = _
  rw [hp]
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- Genuine jet comparison follows from the neighborhood identity, so every
scalar order keeps exactly the actual vector rate-error bound. -/
theorem scalarPhaseRate_jet_norm_le {n : ℕ} (ℓ : E → EuclideanSpace ℝ (Fin n))
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : ℝ) (x : E)
    (hℓ : ContDiffAt ℝ ∞ ℓ x) (hc : ContDiffAt ℝ ∞ c x) (j : ℕ) (l : Fin n) :
    ‖iteratedFDeriv ℝ j
      (fun y ↦ T • fderiv ℝ (fun z ↦ ℓ z l) y - (EuclideanSpace.proj l).comp (c y)) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun y ↦ T • fderiv ℝ ℓ y - c y) x‖ := by
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ℓ y :=
    ((hℓ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).mono
      (fun _ hy ↦ hy.differentiableAt_one)
  have heq : (fun y ↦ T • fderiv ℝ (fun z ↦ ℓ z l) y - (EuclideanSpace.proj l).comp (c y)) =ᶠ[𝓝 x]
      realCovectorRow l ∘ (fun y ↦ T • fderiv ℝ ℓ y - c y) := by
    filter_upwards [hnear] with y hy
    exact scalarPhaseRate_eq_row ℓ c T y hy l
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact covectorRow_jet_norm_le _ x
    (((hℓ.fderiv_right (m := ∞) (by simp)).const_smul T).sub hc) j l

end Rows

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

/-- The complete actual scalar rate budget used by the literal wave estimates.
Every bound is generated before K,T from the original metric and fixed charts. -/
theorem exists_actual_scalarRate_error_budgets :
    ∃ A : ℕ → ℝ, (∀ j, 1 ≤ A j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (i : Fin F.count) (l : Fin n) (j : ℕ)
        (y : EuclideanSpace ℝ (Fin n)),
        y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius →
        ((Q.boundedAtlas (hK.trans hKT)).chart p).symm y ∈ tsupport (F.cutoff i) →
        ∀ k ≤ j,
        ‖iteratedFDeriv ℝ k (fun z ↦
          T • fderiv ℝ (preparedFrozenPhase F (preparedCoframe G g f) l i ∘
            ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) z -
          coframeRows (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) z l) y‖ ≤
            A j * (K⁻¹ + K / T) := by
  obtain ⟨B, hB, hb⟩ := exists_actualPhaseRateError_jet_bounds G g f
  let A : ℕ → ℝ := fun j ↦ 1 + ∑ k ∈ Finset.range (j+1), B k
  have hA (j : ℕ) : 1 ≤ A j := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (j+1), B k :=
      Finset.sum_nonneg fun k _ ↦ (hB k).le
    dsimp [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro K T hK hKT F Q p i l j y hy hi k hkj
  have hcore := Q.scaledPoint_in_open_core (hK.trans hKT) p hy
  have htarget : Q.center p + T⁻¹ • y ∈ (G.chart (Q.parent p)).target :=
    G.buffered (Q.parent p) ((closedBall_subset_closedBall
      (by linarith [G.radius_pos (Q.parent p)])) (ball_subset_closedBall hcore))
  have hsupport : (G.chart (Q.parent p)).symm (Q.center p + T⁻¹ • y) ∈ F.enlargedSupport i := by
    have h := F.support_subset i hi
    simpa only [ChartCutoffFamily.boundedAtlas_chart_symm_apply,
      add_comm (T⁻¹ • y) (Q.center p), ChartCutoffFamily.enlargedSupport] using h
  have hp := actualPhaseCoordinate_contDiffAt G g f F (Q.parent p) (Q.center p) T i
    htarget hsupport.1
  have hc := actualReferenceCoframe_contDiffAt G g f (Q.parent p) (Q.center p) T htarget
  have hrow := scalarPhaseRate_jet_norm_le
    (actualPhaseCoordinate G g f F (Q.parent p) (Q.center p) T i)
    (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T) T y hp hc k l
  rw [preparedFrozenPhase_pullback_eq G g f]
  have hb' := hb K T hK hKT F (Q.parent p) (Q.center p) i k y
    (ball_subset_closedBall hcore) hsupport
  have hBA : B k ≤ A j := by
    have hs : B k ≤ ∑ k ∈ Finset.range (j+1), B k :=
      Finset.single_le_sum (fun k _ ↦ (hB k).le) (by simp; omega)
    dsimp [A]
    linarith
  exact hrow.trans (hb'.trans (mul_le_mul_of_nonneg_right hBA
    (initialization_error_scale_bounds hK hKT).2.2.1))

end GlobalEmbedding.Initialization
