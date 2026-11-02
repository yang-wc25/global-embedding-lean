import NormalPolar.OriginalWaveSeedRescaledGeometry
import NormalPolar.OriginalWaveSeedScaleJets
import NormalPolar.OriginalWaveSeedObserverBounds

/-! Actual uniform raw bounds for a compact interval of positive contractions.
The compact scalar interval is fixed before the eventual probe scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

theorem originalWave_contraction_ne_zero (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) : c ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hc.1)

namespace OriginalWaveSeedBuffer

def rescaleSample (b : OriginalWaveSeedBuffer d i) : Set (ℝ × D) :=
  Icc (1/2 : ℝ) 1 ×ˢ (Prod.snd '' b.compactTarget)

theorem rescaleSample_compact (b : OriginalWaveSeedBuffer d i) : IsCompact b.rescaleSample :=
  isCompact_Icc.prod (b.compact.image continuous_snd)

theorem rescaleSample_in_outer (b b' : OriginalWaveSeedBuffer d i)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget) :
    b.rescaleSample ⊆ Ioo (1/4 : ℝ) 2 ×ˢ b'.spatialChart.target := by
  rintro ⟨c,y⟩ ⟨hc,⟨z,hz,rfl⟩⟩
  exact ⟨⟨by linarith [hc.1],by linarith [hc.2]⟩,(b.compact_in_outer b' hbb hz).2⟩

/-- Every spatial slice, with every passive parameter derivative, is bounded
by the actual joint scalar/spatial field on one fixed compact set. -/
theorem exists_rescaled_prefix_profile {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b b' : OriginalWaveSeedBuffer d i)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget)
    (f : ℝ × D → Y)
    (hf : ContDiffOn ℝ ∞ f (Ioo (1/4 : ℝ) 2 ×ˢ b'.spatialChart.target)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ (c : ℝ), c ∈ Icc (1/2 : ℝ) 1 →
      ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ n k, k ≤ n → ∀ z : Z × D, z ∈ b.chart.target →
        ell^k * ‖iteratedFDeriv ℝ k (fun y : Z × D => f (c,y.2)) z‖ ≤ C n := by
  let O := Ioo (1/4 : ℝ) 2 ×ˢ b'.spatialChart.target
  have hO : IsOpen O := isOpen_Ioo.prod b'.spatialChart.open_target
  have hSO : b.rescaleSample ⊆ O := b.rescaleSample_in_outer b' hbb
  obtain ⟨C,hC,hbound⟩ := exists_compact_native_prefix b.rescaleSample O
    b.rescaleSample_compact hO hSO f hf
  refine ⟨C,hC,?_⟩
  intro c hc ell hell hell1 n k hk z hz
  have hzL : z ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz
  have hs : (c,z.2) ∈ b.rescaleSample := ⟨hc,⟨z,hzL,rfl⟩⟩
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fun y : Z × D => f (c,y.2)) z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
    _ ≤ ‖iteratedFDeriv ℝ k f (c,z.2)‖ := by
      simpa only [one_mul] using fixedParameter_iteratedFDeriv_norm_le c f O hO hf z (hSO hs) k
    _ ≤ C n := hbound n k hk (c,z.2) hs

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_rescaled_prefix_profile

