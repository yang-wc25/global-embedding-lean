import NormalPolar.JointSecondarySignedHostSamples
import NormalPolar.JointSecondarySignedPaddedProfiles

/-! Literal cutoff, partition, support and host jet fields for the same
canonical native secondary choices and compact active samples. Empty slots
remain empty, and the common cutoff/inverse budgets are constructed before
every scale and order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep P Rec : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
  [Fintype Rec] [DecidableEq Rec]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {phase : Rec → M → ℝ} {K O : Rec → Set M}
  (seeds : (r : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (phase r) (K r) (O r))

def jointSecondarySignedNativeCutoff (B : OpenPartialHomeomorph P Ep)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) : Ep × M → ℝ :=
  ((jointSecondarySeedPaddedChoice seeds r s).pullback B).cutoff

theorem jointSecondarySignedNativeCutoff_active (B : OpenPartialHomeomorph P Ep)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (h : s.1 = r) :
    jointSecondarySignedNativeCutoff seeds B r s = fun z => (seeds s.1).refinement.cutoff s.2 z.2 := by
  unfold jointSecondarySignedNativeCutoff
  simp only [jointSecondarySeedPaddedChoice,if_pos h]
  rfl

theorem jointSecondarySignedNativeCutoff_inactive (B : OpenPartialHomeomorph P Ep)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (h : s.1 ≠ r) :
    jointSecondarySignedNativeCutoff seeds B r s = 0 := by
  unfold jointSecondarySignedNativeCutoff
  simp only [jointSecondarySeedPaddedChoice,if_neg h]
  rfl

theorem jointSecondarySignedNativeHost_active (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (h : s.1 = r) :
    jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s =
      ((seeds s.1).inner s.2).nativeHostTransition ((seeds s.1).outer s.2) B := by
  unfold jointSecondarySignedNativeHostTransition
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1]
  simp only [jointSecondarySeedPaddedChoice,if_pos h]
  rfl

theorem jointSecondarySignedNativeRaw_host_source (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (jointSecondarySeedPaddedChoice (P := P) seeds r s).host).source := by
  intro z hz
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1] at hz
  change z ∈ (round3ParameterChartPullback B (jointSecondarySeedPaddedChoice (P := P) seeds r s).chart).source at hz
  rw [round3ParameterChartPullback_source] at hz
  exact ⟨mem_univ _,(jointSecondarySeedPadded_host_source (P := P) seeds r s hz.2.1).2⟩

theorem jointSecondarySignedNativeCutoff_partition (B : OpenPartialHomeomorph P Ep)
    (r : Rec) (z : Ep × M)
    (hz : z ∈ round3ParameterNativeDomain B ((univ : Set P) ×ˢ K r)) :
    ∑ s, jointSecondarySignedNativeCutoff seeds B r s z = 1 := by
  change (∑ s, (jointSecondarySeedPaddedChoice (P := P) seeds r s).cutoff (B.symm z.1,z.2)) = 1
  exact jointSecondarySeedPaddedChoice_partition seeds r (B.symm z.1,z.2) hz.2.2

theorem jointSecondarySignedNativeCutoff_support (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    incrementsGlobalRelativeSupport (round3ParameterNativeDomain B (univ : Set (P × M)))
      (jointSecondarySignedNativeCutoff seeds B r s) ∩
      round3ParameterNativeDomain B ((univ : Set P) ×ˢ K r) ⊆
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).support := by
  rw [jointSecondarySignedNativeRaw_support]
  by_cases h : s.1 = r
  · rw [jointSecondarySignedNativeCutoff_active seeds B r s h,if_pos h]
    rintro _ ⟨⟨z,hz,rfl⟩,ha⟩
    exact ⟨ha.1,mem_univ _,
      tsupport_comp_subset_preimage ((seeds s.1).refinement.cutoff s.2)
        continuous_subtype_val.snd hz,ha.2.2⟩
  · rw [jointSecondarySignedNativeCutoff_inactive seeds B r s h,if_neg h]
    have hzero : tsupport (fun _ : ↥(round3ParameterNativeDomain B (univ : Set (P × M))) => (0 : ℝ)) = ∅ :=
      tsupport_zero
    simp only [incrementsGlobalRelativeSupport,Pi.zero_apply,hzero,image_empty,empty_inter]
    exact empty_subset _

theorem jointSecondarySignedNativeCutoff_smooth (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞ (jointSecondarySignedNativeCutoff seeds B r s ∘
      ((OpenPartialHomeomorph.refl Ep).prod (jointSecondarySeedPaddedChoice (P := P) seeds r s).host).symm)
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).source := by
  by_cases h : s.1 = r
  · rw [jointSecondarySignedNativeCutoff_active seeds B r s h,
      jointSecondarySignedNativeHost_active seeds B Q hQ S scale hs n j ell he he1 r s h,
      jointSecondarySeedPaddedChoice_host]
    apply (((seeds s.1).inner s.2).host_cutoff_smooth ((seeds s.1).outer s.2)).mono
    intro z hz
    exact ⟨hz.1,mem_univ _,((passiveSecondarySeed_chart_source B ((seeds s.1).inner s.2).chart
      (z.1,((seeds s.1).outer s.2).chart.symm z.2)).mp hz.2).2⟩
  · rw [jointSecondarySignedNativeCutoff_inactive seeds B r s h]
    exact contDiffOn_const

theorem jointSecondarySignedNativeHost_inverse_smooth (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).symm
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).target := by
  by_cases h : s.1 = r
  · rw [jointSecondarySignedNativeHost_active seeds B Q hQ S scale hs n j ell he he1 r s h]
    exact ((seeds s.1).inner s.2).nativeHostTransition_inverse_smooth
      ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B
  · unfold jointSecondarySignedNativeHostTransition
    rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1]
    simp only [jointSecondarySeedPaddedChoice,if_neg h,OpenPartialHomeomorph.trans_target,
      round3ParameterSecondaryEmptyChoice_native_target,empty_inter]
    exact contDiffOn_empty

theorem jointSecondarySignedNativeHost_inverse_jets (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (k : ℕ) (hk : 1 ≤ k)
    (z : X) (hz : z ∈ (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).sample) :
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).symm z‖ ≤ 1 := by
  change z ∈ jointSecondarySignedNativeSample seeds Q S r s at hz
  by_cases h : s.1 = r
  · simp only [jointSecondarySignedNativeSample,if_pos h] at hz
    rw [jointSecondarySignedNativeHost_active seeds B Q hQ S scale hs n j ell he he1 r s h]
    exact ((seeds s.1).inner s.2).nativeHostTransition_inverse_jets
      ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B ell k hk z
      (((seeds s.1).inner s.2).nativeHostSample_target
        ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B Q hQ S hz)
  · simp only [jointSecondarySignedNativeSample,if_neg h,mem_empty_iff_false] at hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeCutoff_support
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeCutoff_smooth
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeHost_inverse_jets
