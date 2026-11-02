import Repair.EndpointCompactRawIdentity
import Smoothing.TensorProductJets

/-! Original transition profiles on genuine precompact chart extensions.
Unlike a raw-cutoff transition estimate, this controls every actual chart
overlap in the original norm domains, whether a cutoff is active or not. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ,E) ∞ X]

theorem repair_compact_original_transition_bounds
    (A : BufferedAtlas X E)
    (parent : Fin A.count → OpenPartialHomeomorph X E)
    (hparent : ∀ i, parent i ∈ maximalAtlas 𝓘(ℝ,E) ∞ X)
    (hforward : ∀ i, (A.chart i : X → E) = parent i)
    (hinverse : ∀ i, ((A.chart i).symm : E → X) = (parent i).symm)
    (hsource : ∀ i, (A.chart i).source ⊆ (parent i).source)
    (K : Fin A.count → Set E) (hK : ∀ i, IsCompact (K i))
    (htargetK : ∀ i, (A.chart i).target ⊆ K i)
    (hKparent : ∀ i, K i ⊆ (parent i).target) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ p i k y, y ∈ (A.chart p).target → (A.chart p).symm y ∈ (A.chart i).source →
        ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k := by
  classical
  have htransition : ∀ p i k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ (A.chart i).source →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ C := by
    intro p i k
    let image := (parent i).symm '' K i
    have hImage : IsCompact image :=
      (hK i).image_of_continuousOn ((parent i).continuousOn_symm.mono (hKparent i))
    have hImageSource : image ⊆ (parent i).source := by
      rintro _ ⟨x,hx,rfl⟩
      exact (parent i).map_target (hKparent i hx)
    let O := (parent p).target ∩ (parent p).symm ⁻¹' (parent i).source
    let L := K p ∩ (parent p).symm ⁻¹' image
    have hO : IsOpen O := (parent p).isOpen_inter_preimage_symm (parent i).open_source
    have hClosed : IsClosed L :=
      ((parent p).continuousOn_symm.mono (hKparent p)).preimage_isClosed_of_isClosed
        (hK p).isClosed hImage.isClosed
    have hL : IsCompact L := (hK p).of_isClosed_subset hClosed inter_subset_left
    have hLO : L ⊆ O := fun y hy => ⟨hKparent p hy.1,hImageSource hy.2⟩
    have hf : ContDiffOn ℝ ∞ (parent i ∘ (parent p).symm) O :=
      ((contMDiffOn_of_mem_maximalAtlas (hparent i)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas (hparent p)).mono inter_subset_left)
        (fun _ hy => hy.2)).contDiffOn
    obtain ⟨C,hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (parent i ∘ (parent p).symm) O L L hO hL Subset.rfl hLO hf k
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro y hy hactive
    have hpoint : (parent p).symm y ∈ (A.chart i).source := by rwa [hinverse p] at hactive
    have hImagePoint : (parent p).symm y ∈ image := by
      refine ⟨A.chart i ((parent p).symm y),htargetK i ((A.chart i).map_source hpoint),?_⟩
      rw [hforward i,(parent i).left_inv (hsource i hpoint)]
    have hyL : y ∈ L := ⟨htargetK p hy,hImagePoint⟩
    rw [hforward i,hinverse p]
    exact (hC ⟨⟨y,hyL⟩,rfl⟩).trans (le_max_left _ _)
  choose C hC hBound using htransition
  let T : ℕ → ℝ := fun k => ∑ p, ∑ i, C p i k
  refine ⟨T,fun k => Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => hC p i k)),?_⟩
  intro p i k y hy hi
  apply (hBound p i k y hy hi).trans
  exact (Finset.single_le_sum (fun j _ => hC p j k) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun j _ => hC z j k)) (Finset.mem_univ p))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_compact_original_transition_bounds
