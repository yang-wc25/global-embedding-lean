import Initialization.Colored.ActualSelectedJets
import Initialization.Geometry.ScaledMetricGeometry

/-!
# The actual colored approximation: complete metric C^j estimate

The map is the literal native selector evaluated on the colored phase product.
Every error and reference constant is now generated internally from the fixed
compact geometry, the actual metric-normalized frame, and the fixed selector.
In particular this theorem takes no cutoff, phase, derivative, or metric-error
budget as a hypothesis.  The comparison field is the exact native pullback of
T²g, by `scaledTargetMetricOperator_inner`.
-/

noncomputable section
open Set Function Filter Metric Manifold IsManifold Bundle
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [CompactSpace M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The same actual map has the original all-order colored metric error on
each complete fixed-radius scaled chart.  All constants precede K and T. -/
theorem exists_actual_colored_metric_cj_bounds
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ
      (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (F : ChartCutoffFamily G K) (Q : ChartCutoffFamily G T)
        (p : Fin Q.count) (j : ℕ),
        finiteCjNorm j
          (fun y ↦ actualMetricOperator
              (actualSelectedCoordinate G g f S F Q (hK.trans hKT) p) y -
            scaledTargetMetricOperator G g f Q p y)
          (ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius) ≤
          C j * (K⁻¹ + K / T) := by
  obtain ⟨R, A, hR, hA, hbound⟩ := exists_actualSelectedSource_jet_bounds G g f S hS
  let B : ℕ → ℝ := fun k ↦ R (k+1) + 2 * A k
  have hB (k : ℕ) : 0 ≤ B k :=
    add_nonneg (hR (k+1)).le (mul_nonneg (by norm_num) (hA k).le)
  let L : ℕ → ℝ := fun j ↦ 1 + coloredSelectorOuterEnvelope B j
  have hL (j : ℕ) : 0 ≤ L j := by
    dsimp [L]
    linarith [coloredSelectorOuterEnvelope_nonneg B hB j]
  have hBL {k j : ℕ} (hkj : k ≤ j) : B k ≤ L j := by
    have h := le_coloredSelectorOuterEnvelope B hB hkj
    dsimp [L]
    linarith
  let C : ℕ → ℝ := fun j ↦ max 1 ((j+1 : ℝ) * (2 * 2^j * L j) * A j)
  refine ⟨C, fun _ ↦ lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K T hK hKT F Q p j
  let z := actualColoredSource G g f F Q (hK.trans hKT) p
  let c := actualReferenceCoframe G g f (Q.parent p) (Q.center p) T
  let r := coframeRows c
  let O := ball (0 : EuclideanSpace ℝ (Fin n)) G.scaleRadius
  have hZ := actualColoredSource_ambient_contDiffOn G g f F Q (hK.trans hKT) p
  have hc := actualReferenceCoframe_contDiffOn_ball G g f Q (hK.trans hKT) p
  have hH : ContDiffOn ℝ ∞ (S ∘ z) O := by
    intro y hy
    exact (selectorSource_contDiffAt (fun _ : Fin n ↦ G.palette) S hS z
      (hZ.contDiffAt (isOpen_ball.mem_nhds hy))).contDiffWithinAt
  have hDH := hH.fderiv_of_isOpen isOpen_ball (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))
  have hEH : ContDiffOn ℝ ∞
      (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z r) O := by
    intro y hy
    exact (selectorSourceFirstError_contDiffAt (fun _ : Fin n ↦ G.palette) S hS z r
      (hZ.contDiffAt (isOpen_ball.mem_nhds hy))
      (fun l ↦ (coframeRows_contDiffOn c O hc l).contDiffAt
        (isOpen_ball.mem_nhds hy))).contDiffWithinAt
  have hδ := (initialization_error_scale_bounds hK hKT).2.2.1
  have hδtwo := (initialization_error_scale_bounds hK hKT).2.2.2.2
  have hactual (k : ℕ) (hk : k ≤ j) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (fderiv ℝ (S ∘ z)) y‖ ≤ L j := by
    rw [norm_iteratedFDeriv_fderiv]
    have hb := ((hbound K T hK hKT F Q p (k+1)).1 y hy).1
    exact hb.trans ((show R (k+1) ≤ B k from
      le_add_of_nonneg_right (mul_nonneg (by norm_num) (hA k).le)).trans (hBL hk))
  have hideal (k : ℕ) (hk : k ≤ j) (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k
        (selectorSourceIdealFirst (fun _ : Fin n ↦ G.palette) S z r) y‖ ≤ L j := by
    have heq : selectorSourceIdealFirst (fun _ : Fin n ↦ G.palette) S z r =
        fderiv ℝ (S ∘ z) - selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z r := by
      funext x
      simp only [Pi.sub_apply, selectorSourceFirstError]
      abel
    rw [heq, iteratedFDeriv_sub_apply
      ((hDH.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by simp))
      ((hEH.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by simp))]
    have hfirst : ‖iteratedFDeriv ℝ k (fderiv ℝ (S ∘ z)) y‖ ≤ R (k+1) := by
      rw [norm_iteratedFDeriv_fderiv]
      exact ((hbound K T hK hKT F Q p (k+1)).1 y hy).1
    have herr := ((hbound K T hK hKT F Q p k).1 y hy).2
    have herr' : ‖iteratedFDeriv ℝ k
        (selectorSourceFirstError (fun _ : Fin n ↦ G.palette) S z r) y‖ ≤ 2 * A k :=
      herr.trans ((mul_le_mul_of_nonneg_left hδtwo (hA k).le).trans_eq (mul_comm _ _))
    exact (norm_sub_le _ _).trans ((add_le_add hfirst herr').trans (hBL hk))
  have hb := selectorSource_metric_cj_bound S hS hGram z c j O isOpen_ball hZ hc
    (L j) (A j) (K⁻¹ + K/T) (hL j) (hA j).le hδ hactual hideal
    ((hbound K T hK hKT F Q p j).2)
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ)

/-- The preceding estimate applies to the actual globally defined H_(K,T),
with its canonical internally chosen K-net, in every actual T-scale chart. -/
theorem exists_metricInitializationMap_cj_bounds
    (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) → V)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ G.palette)) 𝓘(ℝ, V) ∞ S)
    (hGram : ∀ z, Matrix.gram ℝ
      (fun l ↦ freeHopfDeriv (fun _ : Fin n ↦ G.palette) l S z) = 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T)
        (Q : ChartCutoffFamily G T) (p : Fin Q.count) (j : ℕ),
        finiteCjNorm j
          (fun y ↦ actualMetricOperator
              (metricInitializationMap G g f S K T hK ∘
                ((Q.boundedAtlas (hK.trans hKT)).chart p).symm) y -
            scaledTargetMetricOperator G g f Q p y)
          (((Q.boundedAtlas (hK.trans hKT)).chart p).target) ≤
          C j * (K⁻¹ + K / T) := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_colored_metric_cj_bounds G g f S hS hGram
  exact ⟨C, hC, fun K T hK hKT Q p j ↦
    hbound K T hK hKT (preparedCutoffsAt G K hK) Q p j⟩

end GlobalEmbedding.Initialization
