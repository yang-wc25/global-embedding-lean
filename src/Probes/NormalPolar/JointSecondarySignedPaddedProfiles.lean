import NormalPolar.JointSecondarySignedPadding

/-! Actual host, support and raw jet fields for the common finite signed source.
Inactive entries are genuine empty domains, and all active entries retain
the constructed partition and nested charts. -/

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


def jointSecondarySeedPaddedTransition (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) : OpenPartialHomeomorph X X :=
  ((OpenPartialHomeomorph.refl Ep).prod
    (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).host).symm.trans
      (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).chart

theorem jointSecondarySeedPadded_host_maximal (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedChoice (P := P) seeds r s).host ∈ maximalAtlas IM ∞ M := by
  rw [jointSecondarySeedPaddedChoice_host]
  exact ((seeds s.1).outer s.2).maximal

theorem jointSecondarySeedPadded_host_source (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedChoice (P := P) seeds r s).chart.source ⊆
      ((OpenPartialHomeomorph.refl P).prod
        (jointSecondarySeedPaddedChoice (P := P) seeds r s).host).source := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,if_pos h]
    exact (seeds s.1).choice_host_source s.2
  · simp only [jointSecondarySeedPaddedChoice,if_neg h,
      round3ParameterSecondaryEmptyChoice_source]
    exact empty_subset _

theorem jointSecondarySeedPadded_cutoff_smooth (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞
      ((jointSecondarySeedPaddedChoice (P := Ep) seeds r s).cutoff ∘
        ((OpenPartialHomeomorph.refl Ep).prod
          (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).host).symm)
      (jointSecondarySeedPaddedTransition seeds r s).source := by
  by_cases h : s.1 = r
  · simpa only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_pos h] using
      (seeds s.1).choice_cutoff_smooth s.2
  · simp only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_neg h]
    exact contDiffOn_const

theorem jointSecondarySeedPadded_inverse_smooth (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞ (jointSecondarySeedPaddedTransition seeds r s).symm
      (jointSecondarySeedPaddedTransition seeds r s).target := by
  by_cases h : s.1 = r
  · simpa only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_pos h] using
      (seeds s.1).choice_inverse_smooth s.2
  · have ht : (jointSecondarySeedPaddedTransition seeds r s).target = ∅ := by
      simp only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_neg h,
        OpenPartialHomeomorph.trans_target,round3ParameterSecondaryEmptyChoice_target,empty_inter]
    rw [ht]
    exact contDiffOn_empty

theorem jointSecondarySeedPadded_support (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).support ⊆ univ ×ˢ K r := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,if_pos h]
    change ((seeds s.1).raw scale hs n j ell he he1 s.2).support ⊆ _
    rw [(seeds s.1).raw_support]
    intro z hz
    exact ⟨mem_univ _,by simpa only [h] using hz.2.2⟩
  · simp only [jointSecondarySeedPaddedRaw,if_neg h]
    exact empty_subset _

theorem jointSecondarySeedPadded_cutoff_support (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    incrementsGlobalRelativeSupport univ (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).cutoff ∩
      (univ ×ˢ K r) ⊆ (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).support := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,jointSecondarySeedPaddedChoice,if_pos h]
    change incrementsGlobalRelativeSupport univ ((seeds s.1).choice (P := Ep) s.2).cutoff ∩
      (univ ×ˢ K r) ⊆ ((seeds s.1).raw scale hs n j ell he he1 s.2).support
    have hr : K r = K s.1 := congrArg K h.symm
    rw [hr]
    exact (seeds s.1).choice_cutoff_raw_support scale hs n j ell he he1 s.2
  · simp only [jointSecondarySeedPaddedRaw,jointSecondarySeedPaddedChoice,if_neg h]
    change incrementsGlobalRelativeSupport univ (0 : Ep × M → ℝ) ∩ _ ⊆ _
    have hzero : tsupport (fun _ : ↥(univ : Set (Ep × M)) => (0 : ℝ)) = ∅ := by
      exact tsupport_zero
    simp only [incrementsGlobalRelativeSupport,Pi.zero_apply,hzero,image_empty,empty_inter]
    exact empty_subset _

theorem jointSecondarySeedPadded_cutoff_jets (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (k : ℕ) (hk : k ≤ n)
    (z : X) (hz : z ∈ (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).sample) :
    ell^k*‖iteratedFDeriv ℝ k
      ((jointSecondarySeedPaddedChoice (P := Ep) seeds r s).cutoff ∘
        ((OpenPartialHomeomorph.refl Ep).prod
          (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).host).symm)
      ((jointSecondarySeedPaddedTransition seeds r s).symm z)‖ ≤ jointSecondarySeedCutoffBudget seeds n := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,if_pos h] at hz
    simp only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_pos h]
    exact ((seeds s.1).choice_cutoff_raw_jets scale hs n j ell he he1 s.2 k hk z hz).trans
      (jointSecondarySeedCutoffBudget_piece seeds s.1 n)
  · rw [jointSecondarySeedPaddedRaw_sample] at hz
    simp only [if_neg h,mem_empty_iff_false] at hz

theorem jointSecondarySeedPadded_inverse_jets (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (k : ℕ) (hk : 1 ≤ k)
    (z : X) (hz : z ∈ (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).sample) :
    ell^(k-1)*‖iteratedFDeriv ℝ k (jointSecondarySeedPaddedTransition seeds r s).symm z‖ ≤ 1 := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,if_pos h] at hz
    simpa only [jointSecondarySeedPaddedTransition,jointSecondarySeedPaddedChoice,if_pos h] using
      (seeds s.1).choice_inverse_raw_jets scale hs n j ell he he1 s.2 k hk z hz
  · rw [jointSecondarySeedPaddedRaw_sample] at hz
    simp only [if_neg h,mem_empty_iff_false] at hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPadded_host_source
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPadded_cutoff_support
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPadded_cutoff_jets
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPadded_inverse_jets
