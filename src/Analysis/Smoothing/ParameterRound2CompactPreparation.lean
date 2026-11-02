import Smoothing.ParameterRound2CompactNorms
import Smoothing.TensorPreparedProduct
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Actual raw jet profiles from compact chart extensions

Source: the finite buffered coordinate preparations in setup:uniform and the
compact-parameter-manifold clause of thm:repair. The own-cutoff and active
transition profiles are proved from the true smooth functions on compact
control sets. No high-order numerical bound is assumed. Each receiving chart
must have a genuine compact extension inside a smooth parent chart. This
avoids falsely inferring whole-target transition bounds from compactness of
the manifold alone.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- Genuine precompact chart extensions and actual raw bumps produce every
finite-order geometric input profile. The profiles are selected once, before
any map/tensor field, smoothing scale, order or entrance budget is used. -/
theorem parameterRound2_exists_rawPreparation_of_compact_chart_extensions
    (A : BufferedAtlas X E)
    (parent : Fin A.count → OpenPartialHomeomorph X E)
    (hparent : ∀ i, parent i ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (hforward : ∀ i, (A.chart i : X → E) = parent i)
    (hinverse : ∀ i, ((A.chart i).symm : E → X) = (parent i).symm)
    (hinnerParent : ∀ i, A.inner i ⊆ (parent i).source)
    (K : Fin A.count → Set E) (hK : ∀ i, IsCompact (K i))
    (htargetK : ∀ i, (A.chart i).target ⊆ K i)
    (hKparent : ∀ i, K i ⊆ (parent i).target)
    (raw : Fin A.count → X → ℝ)
    (hraw : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (raw i))
    (hplateau : ∀ x, ∃ i, raw i x = 1)
    (hinner : ∀ i, tsupport (raw i) ⊆ A.inner i)
    (hsupport : ∀ i, tsupport (raw i) ⊆ A.support i) :
    ∃ B₀ T : ℕ → ℝ, (∀ k, 0 ≤ B₀ k) ∧ (∀ k, 0 ≤ T k) ∧
      Nonempty (TensorRawCutoffPreparation A B₀ T A.supportDegree) := by
  classical
  have hown : ∀ i k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (A.chart i).target,
      ‖iteratedFDeriv ℝ k (raw i ∘ (A.chart i).symm) y‖ ≤ C := by
    intro i k
    have hf : ContDiffOn ℝ ∞ (raw i ∘ (parent i).symm) (parent i).target :=
      ((hraw i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hparent i))).contDiffOn
    obtain ⟨C, hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (raw i ∘ (parent i).symm) (parent i).target (A.chart i).target (K i)
      (parent i).open_target (hK i) (htargetK i) (hKparent i) hf k
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro y hy
    rw [hinverse i]
    exact (hC ⟨⟨y, hy⟩, rfl⟩).trans (le_max_left _ _)
  have htransition : ∀ p i k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (raw i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ C := by
    intro p i k
    let O := (parent p).target ∩ (parent p).symm ⁻¹' (parent i).source
    let L := K p ∩ (parent p).symm ⁻¹' tsupport (raw i)
    have hO : IsOpen O := (parent p).isOpen_inter_preimage_symm (parent i).open_source
    have hLclosed : IsClosed L :=
      ((parent p).continuousOn_symm.mono (hKparent p)).preimage_isClosed_of_isClosed
        (hK p).isClosed (isClosed_tsupport _)
    have hL : IsCompact L := (hK p).of_isClosed_subset hLclosed inter_subset_left
    have hLO : L ⊆ O := fun y hy =>
      ⟨hKparent p hy.1, hinnerParent i (hinner i hy.2)⟩
    have hf : ContDiffOn ℝ ∞ (parent i ∘ (parent p).symm) O :=
      ((contMDiffOn_of_mem_maximalAtlas (hparent i)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas (hparent p)).mono inter_subset_left)
        (fun _ hy => hy.2)).contDiffOn
    obtain ⟨C, hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (parent i ∘ (parent p).symm) O L L hO hL Subset.rfl hLO hf k
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro y hy hactive
    have hyL : y ∈ L := ⟨htargetK p hy, by simpa only [hinverse p, Set.mem_preimage] using hactive⟩
    rw [hforward i, hinverse p]
    exact (hC ⟨⟨y, hyL⟩, rfl⟩).trans (le_max_left _ _)
  choose C hC hownC using hown
  choose Q hQ htransitionQ using htransition
  let B₀ : ℕ → ℝ := fun k => ∑ i, C i k
  let T : ℕ → ℝ := fun k => ∑ p, ∑ i, Q p i k
  have hB₀ : ∀ k, 0 ≤ B₀ k := fun k => Finset.sum_nonneg (fun i _ => hC i k)
  have hT : ∀ k, 0 ≤ T k := fun k =>
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => hQ p i k))
  refine ⟨B₀, T, hB₀, hT, ⟨{
    raw := raw
    smooth := hraw
    plateau_cover := hplateau
    inner_support := hinner
    enlarged_support := hsupport
    degree := le_rfl
    own_jets := ?_
    transition_jets := ?_ }⟩⟩
  · intro i k y hy
    exact (hownC i k y hy).trans
      (Finset.single_le_sum (fun j _ => hC j k) (Finset.mem_univ i))
  · intro p i k _hk y hy hactive
    apply (htransitionQ p i k y hy hactive).trans
    exact (Finset.single_le_sum (fun j _ => hQ p j k) (Finset.mem_univ i)).trans
      (Finset.single_le_sum
        (fun z _ => Finset.sum_nonneg (fun j _ => hQ z j k)) (Finset.mem_univ p))

#print axioms parameterRound2_exists_rawPreparation_of_compact_chart_extensions
end
end GlobalEmbedding.Continuation
