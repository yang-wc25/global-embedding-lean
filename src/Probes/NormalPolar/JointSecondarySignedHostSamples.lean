import NormalPolar.JointSecondarySignedNativeSamples
import NormalPolar.JointSecondarySignedNativeHost

/-! The exact source and inverse-image sample of the common padded native
secondary family. These identities feed genuine extra-host observation
producers. Active entries use the original Q and compact spatial sample;
inactive entries have the actual empty source and empty sample. -/

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

def jointSecondarySignedNativeHostTransition (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) : OpenPartialHomeomorph X X :=
  ((OpenPartialHomeomorph.refl Ep).prod
    (jointSecondarySeedPaddedChoice (P := P) seeds r s).host).symm.trans
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).chart

theorem jointSecondarySignedNativeHost_source (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).source ⊆
      B.target ×ˢ (jointSecondarySeedPaddedChoice (P := P) seeds r s).host.target := by
  intro z hz
  unfold jointSecondarySignedNativeHostTransition at hz
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1] at hz
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,if_pos h] at hz ⊢
    exact ⟨((passiveSecondarySeed_chart_source B ((seeds s.1).inner s.2).chart
      (z.1,((seeds s.1).outer s.2).chart.symm z.2)).mp hz.2).1,hz.1.2⟩
  · simp only [jointSecondarySeedPaddedChoice,if_neg h,OpenPartialHomeomorph.trans_source,
      round3ParameterSecondaryEmptyChoice_native_source,preimage_empty,inter_empty,mem_empty_iff_false] at hz

theorem jointSecondarySignedNativeHost_sample (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).symm ''
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).sample =
      jointSecondarySignedNativeSample seeds Q S r s := by
  unfold jointSecondarySignedNativeHostTransition
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1]
  change _ '' jointSecondarySignedNativeSample seeds Q S r s = _
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,jointSecondarySignedNativeSample,if_pos h]
    exact ((seeds s.1).inner s.2).nativeHostSample_inverse_image
      ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B Q hQ S
  · simp only [jointSecondarySignedNativeSample,if_neg h,image_empty]

theorem jointSecondarySignedNativeHost_spatial_target (S : Set M)
    (s : Σ r, Fin (seeds r).refinement.count) :
    ((seeds s.1).inner s.2).adaptedActiveSample S ⊆ ((seeds s.1).outer s.2).chart.target := by
  intro y hy
  rw [((seeds s.1).outer s.2).chart_target]
  exact (seeds s.1).nested s.2 (interior_subset (by
    simpa only [((seeds s.1).inner s.2).chart_target] using
      ((seeds s.1).inner s.2).adaptedActiveSample_target S hy))

theorem jointSecondarySignedNativeHost_sample_subset (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).symm ''
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).sample ⊆
      B.target ×ˢ ((seeds s.1).inner s.2).adaptedActiveSample S := by
  rw [jointSecondarySignedNativeHost_sample]
  by_cases h : s.1 = r
  · simp only [jointSecondarySignedNativeSample,if_pos h]
    exact fun _ hz => ⟨hQ hz.1,hz.2⟩
  · simp only [jointSecondarySignedNativeSample,if_neg h]
    exact empty_subset _

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeHost_source
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeHost_sample
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeHost_sample_subset
