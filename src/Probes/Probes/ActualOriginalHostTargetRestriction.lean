import Probes.ActualIncrementHostGeometryInputs

/-! Restrict the SAME produced host chart to a real conditioning neighborhood.
The native chart and inverse functions are literally unchanged. Genuine
maximal source slices are reconstructed, and their inverse functions agree
everywhere with the original slices. This allows the derived compact-frame
reserve to enter the actual quantitative geometry without altering any jets.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]

theorem actual_original_host_restrict_target
    (c : OpenPartialHomeomorph M D) (hc : c ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (b : OpenPartialHomeomorph X X) (psi : Ep × M → ℝ)
    (e : Ep → OpenPartialHomeomorph M D) (hdata : ActualOriginalHostSliceData c b psi e)
    (O0 : Set X) (hO0 : IsOpen O0) (hOb : O0 ⊆ b.target) :
    ∃ (b' : OpenPartialHomeomorph X X) (e' : Ep → OpenPartialHomeomorph M D),
      b'.target = O0 ∧ b'.source ⊆ b.source ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      ActualOriginalHostSliceData c b' psi e' ∧
      (actualHostAdaptedChart c b').source =
        (actualHostAdaptedChart c b).source ∩ (actualHostAdaptedChart c b) ⁻¹' O0 ∧
      (∀ p, ((e' p).symm : D → M) = (e p).symm) := by
  have hg := actual_host_slice_geometry_inputs c hc b psi e hdata
  rcases hdata with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hadapt,hback,hforward,hbj,hfj⟩
  let q := actualOriginalHostJointChart (Ep := Ep) c
  let U := b.source ∩ b ⁻¹' O0
  have hU : IsOpen U := b.continuousOn.isOpen_inter_preimage b.open_source hO0
  let b' := b.restrOpen U hU
  have hsource : b'.source ⊆ b.source := inter_subset_left
  have htarget : b'.target = O0 := by
    ext z
    change (z ∈ b.target ∧ b.symm z ∈ b.source ∧ b (b.symm z) ∈ O0) ↔ z ∈ O0
    constructor
    · intro hz
      simpa only [b.right_inv hz.1] using hz.2.2
    · intro hz
      exact ⟨hOb hz,b.map_target (hOb hz),by simpa only [b.right_inv (hOb hz)] using hz⟩
  have hshape (z : X) (hz : z ∈ b.source) :
      (b z).1 = z.1 ∧ (b z).2 0 = psi (z.1,c.symm z.2) := by
    have hqt := hg.1 hz
    have hs : q.symm z ∈ (actualHostAdaptedChart c b).source := by
      refine ⟨q.map_target hqt,?_⟩
      change q (q.symm z) ∈ b.source
      rwa [q.right_inv hqt]
    have hh := hforw (q.symm z) hs
    change (b (q (q.symm z))).1 = z.1 ∧
      (b (q (q.symm z))).2 0 = psi (z.1,c.symm z.2) at hh
    simpa only [q.right_inv hqt] using hh
  obtain ⟨hat',ha',hai',hforw',e',he'⟩ := actual_adapted_chart_original_host c hc psi b'
    (hsource.trans hg.1) (hg.2.1.mono hsource)
    (hg.2.2.1.mono (fun z hz => hOb (by rwa [htarget] at hz)))
    (fun z hz => (hshape z (hsource hz)).1) (fun z hz => (hshape z (hsource hz)).2)
  refine ⟨b',e',htarget,hsource,rfl,rfl,⟨hat',ha',hai',hforw',he'⟩,?_,?_⟩
  · ext z
    change (z ∈ q.source ∧ q z ∈ b.source ∧ q z ∈ b.source ∧ b (q z) ∈ O0) ↔
      ((z ∈ q.source ∧ q z ∈ b.source) ∧ b (q z) ∈ O0)
    tauto
  · intro p
    funext y
    rw [he'.2.2.2.2.1,hei]
    rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_host_restrict_target
