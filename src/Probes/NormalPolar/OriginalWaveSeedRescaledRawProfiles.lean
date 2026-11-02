import NormalPolar.OriginalWaveSeedRescaledBounds
import NormalPolar.ParameterDisplacementPrescribedRaw

/-! The full prescribed raw-profile input is produced from an arbitrary
original legal wave, its immersion and its actual finite adapted refinement.
No solver coefficient, reconstructed amplitude or output estimate is assumed.
All prefix constants are fixed before both requested orders and scale. -/

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
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

/-- Restrict the genuine joint contraction geometry to the same inner chart. -/
theorem rescaled_slice_smooth {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b b' : OriginalWaveSeedBuffer d i)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget)
    (f : ℝ × D → Y)
    (hf : ContDiffOn ℝ ∞ f (Ioo (1/4 : ℝ) 2 ×ˢ b'.spatialChart.target))
    (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) :
    ContDiffOn ℝ ∞ (fun z : X => f (c,z.2)) b.chart.target := by
  apply hf.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
  intro z hz
  have hzL : z ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz
  exact ⟨⟨by linarith [hc.1],by linarith [hc.2]⟩,
    (b.compact_in_outer b' hbb hzL).2⟩

/-- All eight primitive raw profiles are selected uniformly over a fixed
positive contraction interval. The finite charts and every prefix budget
are chosen before the eventual probe scale and contraction. -/
theorem exists_rescaled_raw_full_profiles (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    ∃ b' : OriginalWaveSeedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget ∧
    ∃ Mg Bchi Bnu : ℕ → ℝ,
      (∀ n, 0 < Mg n ∧ 0 < Bchi n ∧ 0 < Bnu n) ∧
      ∀ (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
        ∃ raw : ActualPrescribedSpatialRawProfiles
          (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c) (fun _ => b'.spatialChart.symm)
          (d.cutoffCoordinates i) (fun _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
            (b'.spatialChart.symm x) (w.normal (b'.spatialChart.symm x)))
          b.chart univ (tsupport (d.cutoff i)) n j ell
          (Mg (max n j)) (Bchi n) (Bnu n), raw.sample = b.chart.target := by
  obtain ⟨b',hbb⟩ := b.exists_outer
  let e := b'.spatialChart
  obtain ⟨hG,hJ,hT,hA,hB,hBR⟩ := b'.rescaled_geometry hweight hImm
  obtain ⟨CA,hCA,bA⟩ := b.exists_rescaled_prefix_profile b' hbb _ hA
  obtain ⟨CB,hCB,bB⟩ := b.exists_rescaled_prefix_profile b' hbb _ hB
  obtain ⟨CG,hCG,bG⟩ := b.exists_rescaled_prefix_profile b' hbb _ hG
  obtain ⟨CJ,hCJ,bJ⟩ := b.exists_rescaled_prefix_profile b' hbb _ hJ
  obtain ⟨CT,hCT,bT⟩ := b.exists_rescaled_prefix_profile b' hbb _ hT
  obtain ⟨CR,hCR,bR⟩ := b.exists_rescaled_prefix_profile b' hbb _ hBR
  obtain ⟨Cchi,hchi,bchi⟩ := b.exists_prefix_profile (d.chart i).target
    (d.chart i).open_target b.contained _ (d.cutoffCoordinates_smooth i)
  obtain ⟨Cnu,hnu,bnu⟩ := b.exists_prefix_profile (d.chart i).target
    (d.chart i).open_target b.contained _ (d.normalCoordinates_smooth i)
  let Mg (k : ℕ) := CA k + CB k + CG k + CJ k + CT k + CR k
  have hMg (k : ℕ) : 0 < Mg k := by
    dsimp only [Mg]
    linarith [hCA k,hCB k,hCG k,hCJ k,hCT k,hCR k]
  have hbounds (k : ℕ) : CA k ≤ Mg k ∧ CB k ≤ Mg k ∧ CG k ≤ Mg k ∧
      CJ k ≤ Mg k ∧ CT k ≤ Mg k ∧ CR k ≤ Mg k := by
    dsimp only [Mg]
    exact ⟨by linarith [hCB k,hCG k,hCJ k,hCT k,hCR k],
      by linarith [hCA k,hCG k,hCJ k,hCT k,hCR k],
      by linarith [hCA k,hCB k,hCJ k,hCT k,hCR k],
      by linarith [hCA k,hCB k,hCG k,hCT k,hCR k],
      by linarith [hCA k,hCB k,hCG k,hCJ k,hCR k],
      by linarith [hCA k,hCB k,hCG k,hCJ k,hCT k]⟩
  have hnuEq : (fun z : X => (w.normal (e.symm z.2) : V)) = d.normalCoordinates i := by
    funext z
    rw [b'.spatial_inverse_original z]
    rfl
  have htargetOld : b.chart.target ⊆ (d.chart i).target := by
    rw [b.chart_target]
    exact interior_subset.trans b.contained
  refine ⟨b',hbb,Mg,Cchi,Cnu,fun n => ⟨hMg n,hchi n,hnu n⟩,?_⟩
  intro c hc n j ell hell hell1
  refine ⟨{
    sample := b.chart.target
    sample_subset := Subset.rfl
    closed_support := (isClosed_tsupport _).preimage continuous_subtype_val
    support_source := b.cutoff_support
    chart_smooth := b.chart_smooth
    cutoff_support := ?_
    A_smooth := b.rescaled_slice_smooth b' hbb _ hA c hc
    B_smooth := b.rescaled_slice_smooth b' hbb _ hB c hc
    G_smooth := b.rescaled_slice_smooth b' hbb _ hG c hc
    J_smooth := b.rescaled_slice_smooth b' hbb _ hJ c hc
    T_smooth := b.rescaled_slice_smooth b' hbb _ hT c hc
    BR_smooth := b.rescaled_slice_smooth b' hbb _ hBR c hc
    cutoff_smooth := (d.cutoffCoordinates_smooth i).mono htargetOld
    normal_smooth := ?_
    A_jets := fun k hk z hz => (bA c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz).trans (hbounds _).1
    B_jets := fun k hk z hz => (bB c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz).trans (hbounds _).2.1
    G_jets := fun k hk z hz => (bG c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.1
    J_jets := fun k hk z hz => (bJ c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.2.1
    T_jets := fun k hk z hz => (bT c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.2.2.1
    BR_jets := fun k hk z hz => (bR c hc ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz).trans (hbounds _).2.2.2.2.2
    cutoff_jets := bchi ell hell hell1 n
    normal_jets := ?_ },rfl⟩
  · intro z hz hcut
    exact d.cutoffCoordinates_support i z (htargetOld hz) hcut
  · change ContDiffOn ℝ ∞ (fun z : X => (w.normal (e.symm z.2) : V)) b.chart.target
    rw [hnuEq]
    exact (d.normalCoordinates_smooth i).mono htargetOld
  · change ∀ k ≤ n, ∀ z ∈ b.chart.target,
      ell^k * ‖iteratedFDeriv ℝ k (fun z : X => (w.normal (e.symm z.2) : V)) z‖ ≤ Cnu n
    rw [hnuEq]
    exact bnu ell hell hell1 n

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_rescaled_raw_full_profiles
