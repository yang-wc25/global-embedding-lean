import Probes.ActualOriginalHostRefinement
import Probes.ActualSecondaryOriginalConstruction

/-! The true host-to-adapted transition for a constructed phase chart.
These facts remove the separate transition and inverse-smoothness assumptions
from the prepared-secondary consumer. They concern the actual partial maps,
including their genuine source and target, not an arbitrary replacement. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem round3_prepared_host_transition_domains
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (hsource : b.source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target) :
    let q := actualOriginalHostJointChart (Ep := Ep) c
    let a := actualHostAdaptedChart c b
    (q.symm.trans a).source = b.source ∧
    (q.symm.trans a).target = b.target ∧
    EqOn (q.symm.trans a) b b.source ∧
    EqOn (q.symm.trans a).symm b.symm b.target := by
  intro q a
  have hsrc : (q.symm.trans a).source = b.source := by
    ext z
    change (z ∈ q.target ∧ q.symm z ∈ q.source ∧ q (q.symm z) ∈ b.source) ↔ z ∈ b.source
    constructor
    · rintro ⟨hz,_,hb⟩
      rwa [q.right_inv hz] at hb
    · intro hz
      exact ⟨hsource hz,q.map_target (hsource hz),by simpa only [q.right_inv (hsource hz)] using hz⟩
  have htgt : (q.symm.trans a).target = b.target := by
    ext z
    change ((z ∈ b.target ∧ b.symm z ∈ q.target) ∧ q.symm (b.symm z) ∈ q.source) ↔ z ∈ b.target
    constructor
    · exact fun hz => hz.1.1
    · intro hz
      exact ⟨⟨hz,hsource (b.map_target hz)⟩,q.map_target (hsource (b.map_target hz))⟩
  refine ⟨hsrc,htgt,?_,?_⟩
  · intro z hz
    change b (q (q.symm z)) = b z
    rw [q.right_inv (hsource hz)]
  · intro z hz
    change q (q.symm (b.symm z)) = b.symm z
    exact q.right_inv (hsource (b.map_target hz))

theorem round3_prepared_host_transition_jets
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (hsource : b.source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target) :
    let q := actualOriginalHostJointChart (Ep := Ep) c
    let a := actualHostAdaptedChart c b
    (∀ k z, z ∈ b.source →
      iteratedFDeriv ℝ k (q.symm.trans a) z = iteratedFDeriv ℝ k b z) ∧
    (∀ k z, z ∈ b.target →
      iteratedFDeriv ℝ k (q.symm.trans a).symm z = iteratedFDeriv ℝ k b.symm z) := by
  intro q a
  obtain ⟨_,_,hf,hi⟩ := round3_prepared_host_transition_domains c b hsource
  constructor
  · intro k z hz
    exact ((hf.eventuallyEq_of_mem (b.open_source.mem_nhds hz)).iteratedFDeriv ℝ k).eq_of_nhds
  · intro k z hz
    exact ((hi.eventuallyEq_of_mem (b.open_target.mem_nhds hz)).iteratedFDeriv ℝ k).eq_of_nhds

theorem round3_prepared_host_transition_smooth
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b psi e)
    (hsource : b.source ⊆ (actualOriginalHostJointChart (Ep := Ep) c).target)
    (rho : Ep × M → ℝ)
    (hrho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho) :
    let q := actualOriginalHostJointChart (Ep := Ep) c
    let a := actualHostAdaptedChart c b
    ContDiffOn ℝ ∞ (rho ∘ q.symm) (q.symm.trans a).source ∧
    ContDiffOn ℝ ∞ (q.symm.trans a).symm (q.symm.trans a).target := by
  intro q a
  have hq : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,X) ∞ q q.source := by
    have hcs : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓙 ∞
        (fun z : Ep × M => c z.2) q.source :=
      (contMDiffOn_of_mem_maximalAtlas hc).comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2)
    exact contMDiffOn_fst.prodMk_space hcs
  have hqi : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ q.symm q.target := by
    have hcs : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞ (fun z : X => c.symm z.2) q.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas hc).comp contDiff_snd.contMDiff.contMDiffOn
        (fun _ hz => hz.2)
    exact contDiff_fst.contMDiff.contMDiffOn.prodMk hcs
  refine ⟨?_,?_⟩
  · exact (hrho.comp_contMDiffOn (hqi.mono (fun _ hz => hz.1))).contDiffOn
  · exact (hq.comp (hdata.2.2.1.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)).contDiffOn

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_host_transition_domains
#print axioms GlobalEmbedding.Continuation.round3_prepared_host_transition_jets
#print axioms GlobalEmbedding.Continuation.round3_prepared_host_transition_smooth
