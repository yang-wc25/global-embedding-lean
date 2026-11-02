import NormalPolar.OriginalWaveSeedRawBounds
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
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

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

/-- The complete actual raw input of a piece. Geometry bounds are common
finite-prefix constants; the original normal and cutoff retain their own
budgets. These choices depend on the seed, never on a later scale. -/
theorem exists_actual_raw_full_profiles (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    ∃ b' : OriginalWaveSeedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget ∧
    ∃ Mg Bchi Bnu : ℕ → ℝ,
      (∀ n, 0 < Mg n ∧ 0 < Bchi n ∧ 0 < Bnu n) ∧
      ∀ (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
        ∃ raw : ActualPrescribedSpatialRawProfiles
          (fun _ : Z => F) (fun _ => hF) (fun _ => b'.spatialChart.symm)
          (d.cutoffCoordinates i) (fun _ x => w.normal (b'.spatialChart.symm x))
          b.chart univ (tsupport (d.cutoff i)) n j ell
          (Mg (max n j)) (Bchi n) (Bnu n), raw.sample = b.chart.target := by
  obtain ⟨b',hbb⟩ := b.exists_outer
  let e := b'.spatialChart
  let O : Set X := univ ×ˢ e.target
  have hO : IsOpen O := isOpen_univ.prod e.open_target
  have hBO : b.compactTarget ⊆ O := b.compact_in_outer b' hbb
  have htarget : b.chart.target ⊆ O := by
    rw [b.chart_target]
    exact interior_subset.trans hBO
  obtain ⟨_,_,hG,hJ,hT,hA,hB,hBR⟩ := b'.original_geometry hweight hImm
  obtain ⟨CA,hCA,bA⟩ := b.exists_prefix_profile O hO hBO _ hA
  obtain ⟨CB,hCB,bB⟩ := b.exists_prefix_profile O hO hBO _ hB
  obtain ⟨CG,hCG,bG⟩ := b.exists_prefix_profile O hO hBO _ hG
  obtain ⟨CJ,hCJ,bJ⟩ := b.exists_prefix_profile O hO hBO _ hJ
  obtain ⟨CT,hCT,bT⟩ := b.exists_prefix_profile O hO hBO _ hT
  obtain ⟨CR,hCR,bR⟩ := b.exists_prefix_profile O hO hBO _ hBR
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
  intro n j ell hell hell1
  refine ⟨{
    sample := b.chart.target
    sample_subset := Subset.rfl
    closed_support := (isClosed_tsupport _).preimage continuous_subtype_val
    support_source := b.cutoff_support
    chart_smooth := b.chart_smooth
    cutoff_support := ?_
    A_smooth := hA.mono htarget
    B_smooth := hB.mono htarget
    G_smooth := hG.mono htarget
    J_smooth := hJ.mono htarget
    T_smooth := hT.mono htarget
    BR_smooth := hBR.mono htarget
    cutoff_smooth := (d.cutoffCoordinates_smooth i).mono htargetOld
    normal_smooth := ?_
    A_jets := fun k hk z hz => (bA ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz).trans (hbounds _).1
    B_jets := fun k hk z hz => (bB ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz).trans (hbounds _).2.1
    G_jets := fun k hk z hz => (bG ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.1
    J_jets := fun k hk z hz => (bJ ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.2.1
    T_jets := fun k hk z hz => (bT ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz).trans (hbounds _).2.2.2.2.1
    BR_jets := fun k hk z hz => (bR ell hell hell1 (max n j) k
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

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_actual_raw_full_profiles
