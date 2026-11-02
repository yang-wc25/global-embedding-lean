import Probes.ActualOriginalHostTargetRestriction

/-! Restrict only an actual host chart's parameter domain. All forward,
inverse and slice inverse functions remain literal; the physical source is
exactly the previous source intersected with the new parameter neighborhood. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem round3_prepared_host_restrict_parameter
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (V : Set Ep) (hV : IsOpen V) :
    ∃ (b' : OpenPartialHomeomorph X X) (e' : Ep → OpenPartialHomeomorph M D),
      ActualOriginalHostSliceData c b' psi e' ∧ b'.source ⊆ b.source ∧
      b'.target = b.target ∩ (V ×ˢ (univ : Set D)) ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) ∧
      (actualHostAdaptedChart c b').source =
        (actualHostAdaptedChart c b).source ∩ (V ×ˢ (univ : Set M)) := by
  let a := actualHostAdaptedChart c b
  obtain ⟨b',e',hTarget,hSource,hb,hbi,hData,hASource,hSlices⟩ :=
    actual_original_host_restrict_target c hc b psi e hdata (b.target ∩ (V ×ˢ (univ : Set D)))
      (b.open_target.inter (hV.prod isOpen_univ)) inter_subset_left
  refine ⟨b',e',hData,hSource,hTarget,hb,hbi,hSlices,?_⟩
  rw [hASource]
  ext y
  constructor
  · intro hy
    refine ⟨hy.1,?_,mem_univ _⟩
    have hp := (hdata.2.2.2.1 y hy.1).1
    exact hp ▸ hy.2.2.1
  · intro hy
    refine ⟨hy.1,?_,?_,mem_univ _⟩
    · rw [← hdata.1]
      exact a.map_source hy.1
    · rw [(hdata.2.2.2.1 y hy.1).1]
      exact hy.2.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_host_restrict_parameter
