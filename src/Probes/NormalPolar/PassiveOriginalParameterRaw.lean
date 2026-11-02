import NormalPolar.PassiveOriginalParameterAtlas
import Smoothing.ParameterRound2CompactPreparation

/-! Genuine raw parameter cutoffs on the same finite atlas.  Unit plateaus
are constructed inside its actual inner cover.  Whole-target derivative
budgets use its genuine compact inverse-chart extensions; no finished
smoothing or repair packet is an input. -/
noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem passiveOriginal_parameter_raw_of_inverse_collars
    (B : BufferedAtlas P E)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (B.chart i))
    (hSupport : ∀ i, B.inner i ⊆ B.support i)
    (parent : Fin B.count → OpenPartialHomeomorph P E)
    (hparent : ∀ i, parent i ∈ maximalAtlas 𝓘(ℝ,E) ∞ P)
    (hinverse : ∀ i, ((B.chart i).symm : E → P) = (parent i).symm)
    (K : Fin B.count → Set E) (hK : ∀ i, IsCompact (K i))
    (hTK : ∀ i, (B.chart i).target ⊆ K i)
    (hKT : ∀ i, K i ⊆ (parent i).target) :
    ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
      Nonempty (TensorRawCutoffPreparation B BP TP B.supportDegree) := by
  obtain ⟨raw,hsmooth,hinner⟩ := BumpCovering.exists_isSubordinate_of_prop
    (ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞) (by
      intro s t hs ht hd
      obtain ⟨f,hf⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ,E) hs ht hd
      exact ⟨f,f.contMDiff,hf⟩)
    isClosed_univ B.inner B.inner_open (by
      intro x _
      obtain ⟨i,hi⟩ := B.cover x
      exact mem_iUnion.mpr ⟨i,hi⟩)
  have hown : ∀ i k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (B.chart i).target,
      ‖iteratedFDeriv ℝ k (raw i ∘ (B.chart i).symm) y‖ ≤ C := by
    intro i k
    have hf : ContDiffOn ℝ ∞ (raw i ∘ (parent i).symm) (parent i).target :=
      ((hsmooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hparent i))).contDiffOn
    obtain ⟨C,hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (raw i ∘ (parent i).symm) (parent i).target (B.chart i).target (K i)
      (parent i).open_target (hK i) (hTK i) (hKT i) hf k
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro y hy
    rw [hinverse i]
    exact (hC ⟨⟨y,hy⟩,rfl⟩).trans (le_max_left _ _)
  have htrans : ∀ p i k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (B.chart p).target,
      ‖iteratedFDeriv ℝ k (B.chart i ∘ (B.chart p).symm) y‖ ≤ C := by
    intro p i k
    have hf : ContDiffOn ℝ ∞ (B.chart i ∘ (parent p).symm) (parent p).target :=
      ((hforward i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hparent p))).contDiffOn
    obtain ⟨C,hC⟩ := parameterRound2_coordinate_jets_bounded_of_compact
      (B.chart i ∘ (parent p).symm) (parent p).target (B.chart p).target (K p)
      (parent p).open_target (hK p) (hTK p) (hKT p) hf k
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro y hy
    rw [hinverse p]
    exact (hC ⟨⟨y,hy⟩,rfl⟩).trans (le_max_left _ _)
  choose C hC hownC using hown
  choose T hT htransT using htrans
  refine ⟨fun k => ∑ i, C i k,fun k => ∑ p, ∑ i, T p i k,
    fun k => Finset.sum_nonneg (fun i _ => hC i k),
    fun k => Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => hT p i k)),?_⟩
  refine ⟨{
    raw := fun i => raw i
    smooth := hsmooth
    plateau_cover := ?_
    inner_support := hinner
    enlarged_support := fun i => (hinner i).trans (hSupport i)
    degree := le_rfl
    own_jets := ?_
    transition_jets := ?_ }⟩
  · intro x
    obtain ⟨i,hi⟩ := raw.eventuallyEq_one' x (mem_univ x)
    exact ⟨i,hi.eq_of_nhds⟩
  · intro i k y hy
    exact (hownC i k y hy).trans
      (Finset.single_le_sum (fun j _ => hC j k) (Finset.mem_univ i))
  · intro p i k _ y hy _
    exact (htransT p i k y hy).trans
      ((Finset.single_le_sum (fun j _ => hT p j k) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun j _ => hT q j k))
          (Finset.mem_univ p)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_parameter_raw_of_inverse_collars
