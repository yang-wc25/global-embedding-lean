import NormalPolar.JointSecondarySignedRescaledGeometry
import NormalPolar.JointSecondarySignedRescaledBounds
import Probes.ActualSecondaryQuadraticConstruction

/-! The complete raw signed secondary geometry is uniform for every reference
contraction in [1/2,1]. One fixed finite refinement, inner/outer chart and
profile is chosen before the contraction and all orders/scales. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer

theorem exists_actual_secondary_rescaled_raw_geometry (b : JointSecondarySignedBuffer d i)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hK : IsClosed K) (hO : IsOpen O) (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hgood : ∀ x ∈ O, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    ∃ b' : JointSecondarySignedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget ∧
    ∃ Mg : ℕ → ℝ, (∀ k, 0 < Mg k) ∧ ∀ (scale : ℝ), scale ∈ Icc (1/2 : ℝ) 1 →
      ∀ n j ell, 0 ≤ ell → ell ≤ 1 →
      ∃ raw : ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
        (fun _ => contMDiff_const_rescale F hF scale) n j ell (Mg (max n j)) univ,
        raw.c = (fun _ y => b'.chart.symm y) ∧
        raw.chart = (OpenPartialHomeomorph.refl Ep).prod b.chart ∧
        raw.phase = (fun z : Ep × M => phase z.2) ∧
        raw.sample = univ ×ˢ b.chart.target ∧
        raw.support = univ ×ˢ (tsupport (d.cutoff i) ∩ K) ∧
        raw.spatialChart = (fun _ => b'.chart) := by
  obtain ⟨b',hbb⟩ := b.exists_outer
  let e := b'.chart
  have hBU : b.compactTarget ⊆ e.target := by rw [b'.chart_target]; exact hbb
  have htarget : b.chart.target ⊆ e.target := by rw [b.chart_target]; exact interior_subset.trans hBU
  obtain ⟨hG,hJ,hT,hA,hB,hBR⟩ := actual_phase_rescaled_geometry e b'.maximal
    b'.source_domain b'.inverse_phase F hF hImm hO hphase hgood
  obtain ⟨CG,hCG,bG⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hG
  obtain ⟨CJ,hCJ,bJ⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hJ
  obtain ⟨CT,hCT,bT⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hT
  obtain ⟨CA,hCA,bA⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hA
  obtain ⟨CB,hCB,bB⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hB
  obtain ⟨CR,hCR,bR⟩ := b.exists_rescaled_prefix_profile (Ep := Ep) b' hbb _ hBR
  let Mg (k : ℕ) := CG k+CJ k+CT k+CA k+CB k+CR k
  have hMg (k : ℕ) : 0 < Mg k := by
    dsimp only [Mg]
    linarith [hCG k,hCJ k,hCT k,hCA k,hCB k,hCR k]
  have hb (k : ℕ) : CG k ≤ Mg k ∧ CJ k ≤ Mg k ∧ CT k ≤ Mg k ∧
      CA k ≤ Mg k ∧ CB k ≤ Mg k ∧ CR k ≤ Mg k := by
    dsimp only [Mg]
    exact ⟨by linarith [hCJ k,hCT k,hCA k,hCB k,hCR k],
      by linarith [hCG k,hCT k,hCA k,hCB k,hCR k],
      by linarith [hCG k,hCJ k,hCA k,hCB k,hCR k],
      by linarith [hCG k,hCJ k,hCT k,hCB k,hCR k],
      by linarith [hCG k,hCJ k,hCT k,hCA k,hCR k],
      by linarith [hCG k,hCJ k,hCT k,hCA k,hCB k]⟩
  refine ⟨b',hbb,Mg,hMg,?_⟩
  intro scale hscale n j ell hell hell1
  have hscale0 : scale ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hscale.1)
  have hgram (y : D) (hy : y ∈ e.target) :=
    actual_increment_transverse_gram_of_good_phase (scale • F)
      (contMDiff_const_rescale F hF scale) phase e b'.maximal
      e.target e.open_target Subset.rfl y hy
      ((hphase.contMDiffAt (hO.mem_nhds (b'.source_domain (e.map_target hy)))).mdifferentiableAt (by simp))
      b'.inverse_phase ((goodCovector_const_rescale_iff F hF scale hscale0 _ _).mpr
        (hgood _ (b'.source_domain (e.map_target hy))))
  have hpower {k : ℕ} {v C : ℝ} (hv : ell^k*v ≤ C) (hC : 0 ≤ C) : ell^(k+1)*v ≤ C := by
    calc
      _ = ell*(ell^k*v) := by ring
      _ ≤ ell*C := mul_le_mul_of_nonneg_left hv hell
      _ ≤ C := (mul_le_mul_of_nonneg_right hell1 hC).trans_eq (one_mul _)
  let raw : ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
        (fun _ => contMDiff_const_rescale F hF scale) n j ell (Mg (max n j)) univ := {
    c := fun _ y => e.symm y
    chart := (OpenPartialHomeomorph.refl Ep).prod b.chart
    sample := univ ×ˢ b.chart.target
    sample_subset := fun _ hz => hz
    support := univ ×ˢ (tsupport (d.cutoff i) ∩ K)
    support_closed := (isClosed_univ.prod ((isClosed_tsupport _).inter hK)).preimage continuous_subtype_val
    support_source := fun z hz => ⟨mem_univ _,b.support_source hz.2.1⟩
    source_domain := subset_univ _
    chart_smooth := ?_
    inverse := fun _ _ => rfl
    phase := fun z => phase z.2
    phase_smooth := hphase.comp contMDiff_snd.contMDiffOn (fun z hz => b.source_domain hz.2)
    adaptation := fun z hz => b.adaptation z.2 hz.2
    brows_smooth := b.rescaled_slice_smooth b' hbb _ hBR scale hscale
    inverse_smooth := b.rescaled_slice_smooth b' hbb _ hG scale hscale
    transverse_smooth := b.rescaled_slice_smooth b' hbb _ hJ scale hscale
    value_smooth := b.rescaled_slice_smooth b' hbb _ hT scale hscale
    coefficientA_smooth := b.rescaled_slice_smooth b' hbb _ hA scale hscale
    coefficientB_smooth := b.rescaled_slice_smooth b' hbb _ hB scale hscale
    brows_bound := fun k hk z hz => (bR scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz.2).trans (hb _).2.2.2.2.2
    transverse_bound := fun k hk z hz => (bJ scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz.2).trans (hb _).2.1
    inverse_bound := fun k hk z hz => (bG scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz.2).trans (hb _).1
    value_bound := fun k hk z hz => hpower ((bT scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_right _ _)) z hz.2).trans (hb _).2.2.1) (hMg _).le
    coefficientA_bound := fun k hk z hz => (bA scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz.2).trans (hb _).2.2.2.1
    coefficientB_bound := fun k hk z hz => hpower ((bB scale hscale ell hell hell1 (max n j) k
      (hk.trans (le_max_left _ _)) z hz.2).trans (hb _).2.2.2.2.1) (hMg _).le
    spatialChart := fun _ => e
    coordinate := rfl
    maximal := fun _ => b'.maximal
    target := fun z hz => htarget hz.2
    immersion := fun z _ => (immersion_const_rescale_iff F hF scale hscale0 _).mpr
      (hImm (e.symm z.2))
    gram := fun z hz => hgram z.2 (htarget hz.2) }
  · exact ⟨raw,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · have hc : ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,D) ∞
        (fun z : Ep × M => b.chart z.2) (univ ×ˢ b.chart.source) :=
      (contMDiffOn_of_mem_maximalAtlas b.maximal).comp
        contMDiffOn_snd (fun z hz => hz.2)
    exact contMDiffOn_fst.prodMk_space hc

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_actual_secondary_rescaled_raw_geometry
