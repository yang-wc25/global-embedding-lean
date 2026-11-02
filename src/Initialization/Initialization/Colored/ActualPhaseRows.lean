import Initialization.Colored.MetricMapDefinitions
import Initialization.Colored.ActualCutoffBudgets
import Initialization.Colored.SourceMetricCj
import Initialization.Assembly.ActualRateError

/-!
# Actual scalar phases from the actual metric coframe

The vector phase constructed from g is projected to its native real Euclidean
coordinates. Coordinate projection has operator norm at most one. All phase
reference bounds and local smooth neighborhoods are consequently produced from
the same actual phase and the actual fixed-radius atlas.
-/

noncomputable section
open Set Function Filter Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

section Rows
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realEuclideanProjection_norm_le_one {n : ℕ} (l : Fin n) :
    ‖(EuclideanSpace.proj l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [one_mul, EuclideanSpace.proj, PiLp.proj_apply] using PiLp.norm_apply_le v l

def realCovectorRow {n : ℕ} (l : Fin n) :
    (E →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ E _ _ (EuclideanSpace.proj l)

theorem realCovectorRow_norm_le_one {n : ℕ} (l : Fin n) :
    ‖realCovectorRow (E := E) l‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖(EuclideanSpace.proj l).comp A‖ ≤ 1 * ‖A‖
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (realEuclideanProjection_norm_le_one l) (norm_nonneg A))

/-- Projecting the actual vector phase does not increase any genuine jet norm. -/
theorem scalarPhase_jet_norm_le {n : ℕ} (ℓ : E → EuclideanSpace ℝ (Fin n))
    (x : E) (hℓ : ContDiffAt ℝ ∞ ℓ x) (j : ℕ) (l : Fin n) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (ℓ y) l) x‖ ≤ ‖iteratedFDeriv ℝ j ℓ x‖ := by
  have h := (EuclideanSpace.proj l).norm_iteratedFDeriv_comp_left hℓ
    (by simp : (j : ℕ∞ω) ≤ ∞)
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (realEuclideanProjection_norm_le_one l))

/-- Projecting an actual covector field also does not increase its genuine
iterated derivative norm. -/
theorem covectorRow_jet_norm_le {n : ℕ}
    (R : E → E →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : E) (hR : ContDiffAt ℝ ∞ R x) (j : ℕ) (l : Fin n) :
    ‖iteratedFDeriv ℝ j (realCovectorRow l ∘ R) x‖ ≤ ‖iteratedFDeriv ℝ j R x‖ := by
  exact ((realCovectorRow l).norm_iteratedFDeriv_comp_left hR
    (by simp : (j : ℕ∞ω) ≤ ∞)).trans
      (mul_le_of_le_one_left (norm_nonneg _) (realCovectorRow_norm_le_one l))

end Rows

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

@[simp] theorem preparedFrozenPhase_eq_vectorRow {K : ℝ} (F : ChartCutoffFamily G K)
    (l : Fin n) (i : Fin F.count) (x : M) :
    preparedFrozenPhase F (preparedCoframe G g f) l i x =
      F.frozenVectorPhase G g f i x l := rfl

/-- The scalar phase used in the same constructed H is exactly the appropriate
row of the root worker's actual vector cross-chart phase. -/
theorem preparedFrozenPhase_pullback_eq {K T : ℝ}
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) (i : Fin F.count) (l : Fin n) :
    preparedFrozenPhase F (preparedCoframe G g f) l i ∘ ((Q.boundedAtlas hT).chart p).symm =
      fun y ↦ actualPhaseCoordinate G g f F (Q.parent p) (Q.center p) T i y l := by
  funext y
  simp only [Function.comp_apply, preparedFrozenPhase_eq_vectorRow,
    ChartCutoffFamily.boundedAtlas_chart_symm_apply, actualPhaseCoordinate]
  rw [add_comm (T⁻¹ • y) (Q.center p)]

/-- The actual reference coframe is smooth on the entire fixed coordinate ball. -/
theorem actualReferenceCoframe_contDiffOn_ball {T : ℝ}
    (Q : ChartCutoffFamily G T) (hT : 1 ≤ T) (p : Fin Q.count) :
    ContDiffOn ℝ ∞ (actualReferenceCoframe G g f (Q.parent p) (Q.center p) T)
      (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) := by
  intro y hy
  have hc := Q.scaledPoint_in_open_core hT p hy
  have ht : Q.center p + T⁻¹ • y ∈ (G.chart (Q.parent p)).target :=
    G.buffered (Q.parent p) ((closedBall_subset_closedBall
      (by linarith [G.radius_pos (Q.parent p)])) (ball_subset_closedBall hc))
  exact (actualReferenceCoframe_contDiffAt G g f (Q.parent p) (Q.center p) T ht).contDiffWithinAt

/-- Every active scalar phase has an actual open smooth overlap neighborhood
inside the fixed reference ball. This supplies zero-extension consumers directly. -/
theorem exists_actual_phase_smooth_neighborhood {K T : ℝ}
    (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T) (hT : 1 ≤ T)
    (p : Fin Q.count) (i : Fin F.count) (l : Fin n)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius)
    (hi : ((Q.boundedAtlas hT).chart p).symm y ∈ tsupport (F.cutoff i)) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ y ∈ O ∧
      O ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius ∧
      ContDiffOn ℝ ∞ (F.cutoff i ∘ ((Q.boundedAtlas hT).chart p).symm) O ∧
      ContDiffOn ℝ ∞
        (preparedFrozenPhase F (preparedCoframe G g f) l i ∘ ((Q.boundedAtlas hT).chart p).symm) O := by
  let e := (Q.boundedAtlas hT).chart p
  let O := e.target ∩ e.symm ⁻¹' (G.chart (F.parent i)).source
  have hO : IsOpen O := e.symm.isOpen_inter_preimage (G.chart (F.parent i)).open_source
  have hyO : y ∈ O := ⟨hy, (F.support_subset i hi).1⟩
  have hsub : O ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius := inter_subset_left
  have hφ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e.symm O :=
    (contMDiffOn_symm_of_mem_maximalAtlas ((Q.boundedAtlas_smooth hT).chart_mem p)).mono
      inter_subset_left
  refine ⟨O, hO, hyO, hsub, ?_, ?_⟩
  · exact ((F.cutoff_smooth i).comp_contMDiffOn hφ).contDiffOn
  · have hp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (F.frozenVectorPhase G g f i ∘ e.symm) O :=
      (F.frozenVectorPhase_contMDiffOn G g f i).comp hφ (fun z hz ↦ hz.2)
    exact ((EuclideanSpace.proj l).contDiff.comp_contDiffOn hp.contDiffOn)

/-- No phase reference budget is assumed: fixed compact-source geometry and
the actual normalized metric coframe produce it, uniformly on every active
patch of every real-scale map. -/
theorem exists_actual_scalarPhase_reference_budgets [CompactSpace M] :
    ∃ L : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (i : Fin F.count) (l : Fin n) (j : ℕ)
        (y : EuclideanSpace ℝ (Fin n)), y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius →
        ((Q.boundedAtlas (hK.trans hKT)).chart p).symm y ∈ tsupport (F.cutoff i) →
        ∀ k, 1 ≤ k → k ≤ j →
        |T| * ‖iteratedFDeriv ℝ k
          (preparedFrozenPhase F (preparedCoframe G g f) l i ∘
            ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y‖ ≤ L j := by
  obtain ⟨B, hB, hb⟩ := exists_actual_frozenPhase_rescaled_bounds G g f
  let L : ℕ → ℝ := fun j ↦ 1 + ∑ k ∈ Finset.range (j+1), B k
  have hL (j : ℕ) : 1 ≤ L j := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (j+1), B k := Finset.sum_nonneg fun k _ ↦ hB k
    dsimp [L]
    linarith
  refine ⟨L, hL, ?_⟩
  intro K T hK hKT F Q p i l j y hy hi k hk hkj
  have hcore := Q.scaledPoint_in_open_core (hK.trans hKT) p hy
  have htarget : Q.center p + T⁻¹ • y ∈ (G.chart (Q.parent p)).target :=
    G.buffered (Q.parent p) ((closedBall_subset_closedBall
      (by linarith [G.radius_pos (Q.parent p)])) (ball_subset_closedBall hcore))
  have hsupport : (G.chart (Q.parent p)).symm (Q.center p + T⁻¹ • y) ∈ F.enlargedSupport i := by
    have h := F.support_subset i hi
    simpa only [ChartCutoffFamily.boundedAtlas_chart_symm_apply,
      add_comm (T⁻¹ • y) (Q.center p), ChartCutoffFamily.enlargedSupport] using h
  have hphase := actualPhaseCoordinate_contDiffAt G g f F (Q.parent p) (Q.center p) T i
    htarget hsupport.1
  rw [preparedFrozenPhase_pullback_eq G g f]
  have hrow := scalarPhase_jet_norm_le
    (actualPhaseCoordinate G g f F (Q.parent p) (Q.center p) T i) y hphase k l
  have hb' := (hb K T hK (hK.trans hKT) F (Q.parent p) (Q.center p) i k hk y
    (ball_subset_closedBall hcore) hsupport).2
  have hBL : B k ≤ L j := by
    have hs : B k ≤ ∑ k ∈ Finset.range (j+1), B k :=
      Finset.single_le_sum (fun k _ ↦ hB k) (by simp; omega)
    dsimp [L]
    linarith
  exact (mul_le_mul_of_nonneg_left hrow (abs_nonneg T)).trans (hb'.trans hBL)

end GlobalEmbedding.Initialization
