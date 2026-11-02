import Initialization.Geometry.RawCutoffGeometry
import Initialization.Geometry.CoordinateExtensionJets
import GlobalEmbedding.Offline.CutoffChartTransfer

/-!
# Actual all-order raw cutoff bounds in every fixed chart core

The true zero-extended cutoff equals its fixed profile applied to the actual
global coordinate extension near its support. This proves the chart-transfer
input, rather than assuming bounded transitions. Outside the topological
support, the actual derivative is zero at every order. The resulting sequence
is fixed before K and the net size.
-/

open Set Metric Filter Manifold IsManifold Topology Function
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Offline

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- The actual profile germ at an active support point, including boundary
points of that support. Global extension values away from the core are unused. -/
theorem ChartCutoffFamily.rawCutoff_eventuallyEq_extension
    {G : PreparedCharts M n} {K : ℝ} (F : ChartCutoffFamily G K) (hK : 1 ≤ K)
    (ext : Fin G.count → M → EuclideanSpace ℝ (Fin n))
    (hext : ∀ i x, x ∈ (G.chart i).source →
      G.chart i x ∈ closedBall (G.center i) (2 * G.radius i) → ext i x = G.chart i x)
    (i : Fin F.count) {x : M} (hx : x ∈ tsupport (F.rawCutoff i)) :
    F.rawCutoff i =ᶠ[𝓝 x]
      (fun z ↦ scaledCutoffProfile G.scaleRadius K (ext (F.parent i) z - F.center i)) := by
  have hs := F.rawCutoff_support_subset hK i hx
  have hc := F.enlargedSupport_in_open_core hK i hs
  have he := prepared_coordinate_extension_eventuallyEq G ext hext (F.parent i) hs.1 hc
  filter_upwards [he, (G.chart (F.parent i)).open_source.mem_nhds hs.1] with z hz hzs
  change scaledChartCutoff G.scaleRadius K (translatedChart (G.chart (F.parent i)) (F.center i)) z = _
  rw [scaledChartCutoff_on_source G.scaleRadius K
    (translatedChart (G.chart (F.parent i)) (F.center i)) hzs, translatedChart_apply, hz]

/-- All actual raw cutoff jets in every fixed compact chart core obey A_j K^j.
The entire derivative sequence is generated internally from the compact
manifold, fixed profile, and real scale radius. -/
theorem exists_prepared_rawCutoff_derivative_bounds [CompactSpace M] (G : PreparedCharts M n) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ K : ℝ, 1 ≤ K → ∀ F : ChartCutoffFamily G K,
        ∀ p i j y, y ∈ closedBall (G.center p) (2 * G.radius p) →
          ‖iteratedFDeriv ℝ j (F.rawCutoff i ∘ (G.chart p).symm) y‖ ≤ A j * K ^ j := by
  obtain ⟨ext, C, hC, hext, heq, hjets⟩ := exists_prepared_coordinate_extension_jets G
  obtain ⟨B, hB, hprofile⟩ := exists_scaledCutoffProfile_derivative_bounds
    (E := EuclideanSpace ℝ (Fin n)) G.scaleRadius G.scaleRadius_pos
  obtain ⟨A, hA, hcompose⟩ := exists_scaled_composition_derivative_bounds
    (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin n)) B C hB hC
  refine ⟨A, hA, ?_⟩
  intro K hK F p i j y hy
  have hyt : y ∈ (G.chart p).target :=
    G.buffered p ((closedBall_subset_closedBall (by linarith [G.radius_pos p])) hy)
  have hcontinuous : ContinuousAt (G.chart p).symm y := (G.chart p).symm.continuousAt hyt
  by_cases hactive : (G.chart p).symm y ∈ tsupport (F.rawCutoff i)
  · have hgerm := (F.rawCutoff_eventuallyEq_extension hK ext heq i hactive).comp_tendsto hcontinuous
    rw [(hgerm.iteratedFDeriv ℝ j).eq_of_nhds]
    let q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun z ↦ ext (F.parent i) ((G.chart p).symm z) - F.center i
    have hbase : ContDiffOn ℝ ∞ (ext (F.parent i) ∘ (G.chart p).symm) (G.chart p).target :=
      ((hext (F.parent i)).comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth p))).contDiffOn
    have hq : ContDiffOn ℝ ∞ q (G.chart p).target := hbase.sub contDiffOn_const
    apply hcompose K hK (scaledCutoffProfile G.scaleRadius K) q (G.chart p).target univ
      (G.chart p).open_target isOpen_univ (scaledCutoffProfile_contDiff _ _).contDiffOn
      hq (fun _ _ ↦ Set.mem_univ _) y hyt (fun l ↦ hprofile K hK l (q y))
    intro l hl
    change ‖iteratedFDeriv ℝ l
      (fun z ↦ (ext (F.parent i) ∘ (G.chart p).symm) z - F.center i) y‖ ≤ C l
    rw [iteratedFDeriv_sub_fixed_center _ _ (by omega) y
      ((hbase.contDiffAt ((G.chart p).open_target.mem_nhds hyt)).of_le (by simp))]
    exact hjets p (F.parent i) l y hy
  · rw [iteratedFDeriv_comp_eq_zero_off_tsupport _ _ _ hcontinuous hactive j, norm_zero]
    exact mul_nonneg (hA j) (pow_nonneg (zero_le_one.trans hK) j)

end GlobalEmbedding.Initialization
