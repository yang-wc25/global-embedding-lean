import GlobalEmbedding.Paper.ManifoldFlatOn
import GlobalEmbedding.Paper.GeneralMaximalChartTargetOpen
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Actual manifold flatness is preserved by smooth scalar multiplication.

Proof: in every actual smooth chart both pullbacks are smooth on the actual
open target. The native within-set Leibniz bound has a vanishing scalar jet in
every term; open-target within jets are the genuine ordinary chart jets. Global
smoothness follows from smooth bilinear scalar multiplication. Source:
`prop:matrix`, flatness of cutoff-weighted angle corrections. -/
theorem manifold_flat_on_smul
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → ℝ} {Z : Set M} (hf : ManifoldFlatOn (I := I) f Z)
    (g : M → F) (hg : ContMDiff I 𝓘(ℝ, F) ∞ g) :
    ManifoldFlatOn (I := I) (fun x ↦ f x • g x) Z := by
  have hmul : ContDiff ℝ ∞ (fun p : ℝ × F ↦ p.1 • p.2) :=
    contDiff_fst.smul contDiff_snd
  have hpair : ContMDiff I 𝓘(ℝ, ℝ × F) ∞ (fun x ↦ (f x, g x)) := hf.1.prodMk_space hg
  refine ⟨hmul.contMDiff.comp hpair, ?_⟩
  intro x hx e he hex k
  have he2 : e ∈ IsManifold.maximalAtlas I 2 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hopen := general_maximal_chart_target_open e he2
  have hInv : ContMDiffOn 𝓘(ℝ, E) I ∞ (e.extend I).symm (e.extend I).target := by
    simpa only [OpenPartialHomeomorph.extend_target, I.image_eq] using
      contMDiffOn_extend_symm (e := e) he
  have hfi : ContDiffOn ℝ ∞ (f ∘ (e.extend I).symm) (e.extend I).target :=
    (hf.1.comp_contMDiffOn hInv).contDiffOn
  have hgi : ContDiffOn ℝ ∞ (g ∘ (e.extend I).symm) (e.extend I).target :=
    (hg.comp_contMDiffOn hInv).contDiffOn
  have hmem : e.extend I x ∈ (e.extend I).target :=
    (e.extend I).map_source (by simpa only [OpenPartialHomeomorph.extend_source] using hex)
  have hbound := norm_iteratedFDerivWithin_smul_le hfi hgi hopen.uniqueDiffOn hmem
    (show (k : ℕ∞ω) ≤ ∞ by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hopen hmem] at hbound
  have hflat := hf.2 x hx e he hex
  change iteratedFDeriv ℝ k
    (fun y ↦ f ((e.extend I).symm y) • g ((e.extend I).symm y)) (e.extend I x) = 0
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  simpa only [hflat, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero,
    Function.comp_apply] using hbound

end GlobalEmbedding.Paper
