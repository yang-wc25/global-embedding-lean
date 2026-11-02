import Upgrade.CompactFixedAtlasJets
import Upgrade.CompactAtlasSupport
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Original atlas control on compact coordinate plots

The uniform diagonal-separation theorem uses its own finite centered charts.
Its derivative tolerance must be related to the original probe atlas norm.
Here the actual transition derivative is retained explicitly, and compactness
provides a finite bound before the perturbed map is chosen. This is a norm
comparison consumer, not a new local injectivity argument.
-/

noncomputable section
open Function Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The derivative on another actual plot contains the actual coordinate
transition derivative. No equality of the two source frames is assumed. -/
theorem actual_plot_fderiv_in_atlas
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (h : X → M) (z : X) (hh : ContMDiffAt 𝓘(ℝ, X) IM ∞ h z)
    (hz : h z ∈ (A.chart i).source) :
    fderiv ℝ (F ∘ h) z = (probeAtlasFirstJet A F i (h z)).comp
      (fderiv ℝ ((A.chart i) ∘ h) z) := by
  have ht : ContDiffAt ℝ ∞ ((A.chart i) ∘ h) z :=
    ((contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hz).comp z hh).contDiffAt
  have hc := (probeAtlas_fixed_coordinate_smooth A hA F hF i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hz))
  have heq : (F ∘ h) =ᶠ[𝓝 z] (F ∘ (A.chart i).symm) ∘ ((A.chart i) ∘ h) := by
    filter_upwards [hh.continuousAt.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hz)] with w hw
    simp only [Function.comp_apply, (A.chart i).left_inv hw]
  rw [heq.fderiv_eq, fderiv_comp z (hc.differentiableAt (by simp))
    (ht.differentiableAt (by simp))]
  rfl

/-- An actual plot has a neighborhood with one original support label and
one finite transition-derivative bound. The neighborhood is chosen before
either of the maps whose difference will be estimated. -/
theorem exists_actual_plot_atlas_neighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ p : M, ∃ i, p ∈ interior (A.support i))
    (h : X → M) {U : Set X} (hU : IsOpen U)
    (hh : ContMDiffOn 𝓘(ℝ, X) IM ∞ h U) (z : X) (hz : z ∈ U) :
    ∃ (i : Fin A.count) (W : Set X) (C : ℝ), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧
      0 < C ∧ (∀ w ∈ W, h w ∈ A.support i) ∧
      ∀ w ∈ W, ‖fderiv ℝ ((A.chart i) ∘ h) w‖ < C := by
  obtain ⟨i, hi⟩ := hcover (h z)
  have hhz := hh.contMDiffAt (hU.mem_nhds hz)
  have ht : ContDiffAt ℝ ∞ ((A.chart i) ∘ h) z :=
    ((contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i)
      (hA.support_subset i (interior_subset hi))).comp z hhz).contDiffAt
  let C := ‖fderiv ℝ ((A.chart i) ∘ h) z‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hnorm : ∀ᶠ w in 𝓝 z, ‖fderiv ℝ ((A.chart i) ∘ h) w‖ < C :=
    (ht.continuousAt_fderiv (by simp)).norm.eventually_lt_const (by
      dsimp only [C]; linarith)
  have hsupp : ∀ᶠ w in 𝓝 z, h w ∈ interior (A.support i) :=
    hhz.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hi)
  have hev : ∀ᶠ w in 𝓝 z, w ∈ U ∧ h w ∈ interior (A.support i) ∧
      ‖fderiv ℝ ((A.chart i) ∘ h) w‖ < C := by
    filter_upwards [hU.mem_nhds hz, hsupp, hnorm] with w hw hs hd
    exact ⟨hw, hs, hd⟩
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp hev
  exact ⟨i, W, C, hW, hzW, fun w hw ↦ (hWsub hw).1, hC,
    fun w hw ↦ interior_subset (hWsub hw).2.1, fun w hw ↦ (hWsub hw).2.2⟩

/-- One compact plot has a uniform bound converting the original atlas C²
displacement into its literal derivative discrepancy. Empty compact sets are
allowed. The constant depends only on the fixed atlas, plot and compact set. -/
theorem exists_originalC2_compact_plot_derivative_bound
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ p : M, ∃ i, p ∈ interior (A.support i))
    (h : X → M) {U K : Set X} (hU : IsOpen U)
    (hh : ContMDiffOn 𝓘(ℝ, X) IM ∞ h U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C > 0, ∀ (F G : M → V), ContMDiff IM 𝓘(ℝ, V) ∞ F →
      ContMDiff IM 𝓘(ℝ, V) ∞ G → ∀ b : ℝ, 0 ≤ b →
      probeAtlasCj A 2 (G - F) ≤ ENNReal.ofReal b →
      ∀ z ∈ K, ‖fderiv ℝ (G ∘ h) z - fderiv ℝ (F ∘ h) z‖ ≤ C * b := by
  classical
  choose lab W C hW hzW hWU hC hsupp hder using fun z : K ↦
    exists_actual_plot_atlas_neighborhood A hA hcover h hU hh z.1 (hKU z.2)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover W hW (fun z hz ↦
    mem_iUnion.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩)
  obtain ⟨Cmax, hCmax⟩ := Finite.exists_le (fun k : S ↦ C k.1)
  let Ctotal := probeAtlasDerivativeConstant n N 1 * (|Cmax| + 1) + 1
  have htotal : 0 < Ctotal := by
    dsimp only [Ctotal]
    have hconst := probeAtlasDerivativeConstant_nonneg n N 1
    positivity
  refine ⟨Ctotal, htotal, ?_⟩
  intro F G hF hG b hb hclose z hz
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hS hz)
  obtain ⟨hkS, hzk⟩ := mem_iUnion.mp hk
  have hzs := hsupp k z hzk
  have hzU := hWU k hzk
  have hhz := hh.contMDiffAt (hU.mem_nhds hzU)
  have hjet := (probeAtlas_original_two_jet_difference A hA F G hF hG
    hb hclose (lab k) (h z) hzs).1
  have htrans : ‖fderiv ℝ ((A.chart (lab k)) ∘ h) z‖ ≤ |Cmax| + 1 :=
    (hder k z hzk).le.trans ((hCmax ⟨k, hkS⟩).trans
      ((le_abs_self Cmax).trans (by linarith)))
  rw [actual_plot_fderiv_in_atlas A hA (lab k) G hG h z hhz (hA.support_subset _ hzs),
    actual_plot_fderiv_in_atlas A hA (lab k) F hF h z hhz (hA.support_subset _ hzs),
    ← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖probeAtlasFirstJet A G (lab k) (h z) - probeAtlasFirstJet A F (lab k) (h z)‖ *
        ‖fderiv ℝ ((A.chart (lab k)) ∘ h) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (probeAtlasDerivativeConstant n N 1 * b) * (|Cmax| + 1) :=
      mul_le_mul hjet htrans (norm_nonneg _) (mul_nonneg
        (probeAtlasDerivativeConstant_nonneg n N 1) hb)
    _ ≤ Ctotal * b := by
      dsimp only [Ctotal]
      nlinarith

#print axioms actual_plot_fderiv_in_atlas
#print axioms exists_originalC2_compact_plot_derivative_bound

end GlobalEmbedding.Upgrade
