import NormalPolar.JointSecondarySignedSamples
import NormalPolar.JointSecondarySignedHost
import NormalPolar.PassiveSecondarySeedChart

/-! Exact host samples for the canonical parameter pullback of a signed
piece. The true inverse host transition is the identity on its target.
The compact active sample consequently stays in the original parameter Q
and maps to the original spatial sample under the actual observer change. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M Ep P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer
variable (b b' : JointSecondarySignedBuffer d i)
  (hbb : b.compactTarget ⊆ interior b'.compactTarget)
  (B : OpenPartialHomeomorph P Ep)

def nativeHostTransition : OpenPartialHomeomorph X X :=
  ((OpenPartialHomeomorph.refl Ep).prod b'.chart).symm.trans
    (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod b.chart))

include hbb in
theorem nativeHostTransition_target :
    (b.nativeHostTransition b' B).target = B.target ×ˢ b.chart.target := by
  have hs : (round3ParameterChartPullback B
      ((OpenPartialHomeomorph.refl P).prod b.chart)).source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod b'.chart).source := by
    intro z hz
    exact ⟨mem_univ _,b.source_in_outer b' hbb
      ((passiveSecondarySeed_chart_source B b.chart z).mp hz).2⟩
  rw [nativeHostTransition,actual_secondary_host_transition_target _ _ hs]
  ext z
  exact passiveSecondarySeed_chart_target B b.chart z

include hbb in
theorem nativeHostTransition_inverse (z : X) (hz : z ∈ (b.nativeHostTransition b' B).target) :
    (b.nativeHostTransition b' B).symm z = z := by
  rw [b.nativeHostTransition_target b' hbb B] at hz
  change (B (B.symm z.1),b'.chart (b.chart.symm z.2)) = z
  rw [B.right_inv hz.1]
  have hz' : z ∈ (b.hostTransition b').target := by
    rw [b.hostTransition_target b' hbb]
    exact ⟨mem_univ _,hz.2⟩
  exact b.hostTransition_inverse b' hbb z hz'

include hbb in
theorem nativeHostTransition_inverse_smooth :
    ContDiffOn ℝ ∞ (b.nativeHostTransition b' B).symm (b.nativeHostTransition b' B).target :=
  contDiffOn_id.congr (b.nativeHostTransition_inverse b' hbb B)

include hbb in
theorem nativeHostTransition_inverse_jets (ell : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (z : X) (hz : z ∈ (b.nativeHostTransition b' B).target) :
    ell^(k-1)*‖iteratedFDeriv ℝ k (b.nativeHostTransition b' B).symm z‖ ≤ 1 := by
  have hz' : z ∈ (b.hostTransition b').target := by
    rw [b.hostTransition_target b' hbb]
    exact ⟨mem_univ _,((b.nativeHostTransition_target b' hbb B) ▸ hz).2⟩
  have hnew : (b.nativeHostTransition b' B).symm =ᶠ[𝓝 z] (id : X → X) :=
    (show EqOn (b.nativeHostTransition b' B).symm id (b.nativeHostTransition b' B).target from
      b.nativeHostTransition_inverse b' hbb B).eventuallyEq_of_mem
      ((b.nativeHostTransition b' B).open_target.mem_nhds hz)
  have hold : (b.hostTransition b').symm =ᶠ[𝓝 z] (id : X → X) :=
    (show EqOn (b.hostTransition b').symm id (b.hostTransition b').target from
      b.hostTransition_inverse b' hbb).eventuallyEq_of_mem
      ((b.hostTransition b').open_target.mem_nhds hz')
  rw [((hnew.trans hold.symm).iteratedFDeriv ℝ k).eq_of_nhds]
  exact b.hostTransition_inverse_jets b' hbb ell k hk z hz'

include hbb in
theorem nativeHostSample_target (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M) :
    Q ×ˢ b.adaptedActiveSample S ⊆ (b.nativeHostTransition b' B).target := by
  rw [b.nativeHostTransition_target b' hbb B]
  exact fun _ hz => ⟨hQ hz.1,b.adaptedActiveSample_target S hz.2⟩

include hbb in
theorem nativeHostSample_inverse_image (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M) :
    (b.nativeHostTransition b' B).symm '' (Q ×ˢ b.adaptedActiveSample S) =
      Q ×ˢ b.adaptedActiveSample S := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    rw [b.nativeHostTransition_inverse b' hbb B z (b.nativeHostSample_target b' hbb B Q hQ S hz)]
    exact hz
  · intro z hz
    exact ⟨z,hz,b.nativeHostTransition_inverse b' hbb B z
      (b.nativeHostSample_target b' hbb B Q hQ S hz)⟩

include hbb in
theorem nativeHostSample_observer_domain (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (e : OpenPartialHomeomorph M D) (hSe : S ⊆ e.source) :
    Q ×ˢ b.adaptedActiveSample S ⊆ B.target ×ˢ (b'.chart.symm.trans e).source := by
  intro z hz
  have hs := b.adaptedActiveSample_inverse S z.2 hz.2
  have ht : z.2 ∈ b'.chart.target := by
    rw [b'.chart_target]
    exact hbb (interior_subset (by simpa only [b.chart_target] using b.adaptedActiveSample_target S hz.2))
  exact ⟨hQ hz.1,ht,hSe hs.1⟩

theorem nativeHostSample_observer_mapsTo (Q : Set Ep) (S : Set M)
    (e : OpenPartialHomeomorph M D) :
    MapsTo (fun z : X => (z.1,e (b'.chart.symm z.2)))
      (Q ×ˢ b.adaptedActiveSample S) (Q ×ˢ (e '' S)) := by
  intro z hz
  exact ⟨hz.1,⟨b.chart.symm z.2,(b.adaptedActiveSample_inverse S z.2 hz.2).1,rfl⟩⟩

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.nativeHostTransition_inverse_jets
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.nativeHostSample_inverse_image
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.nativeHostSample_observer_domain
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.nativeHostSample_observer_mapsTo
