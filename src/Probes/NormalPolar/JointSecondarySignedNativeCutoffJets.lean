import NormalPolar.JointSecondarySignedNativeProfiles

/-! The cutoff budget for the actual canonical native signed choices is the
same finite cutoff budget chosen before the scale.  The two host inverses
are literally the identity on their respective targets. -/

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

theorem jointSecondarySignedNativeCutoff_jets (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (k : ℕ) (hk : k ≤ n)
    (z : X) (hz : z ∈ (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).sample) :
    ell^k*‖iteratedFDeriv ℝ k
      (jointSecondarySignedNativeCutoff seeds B r s ∘
        ((OpenPartialHomeomorph.refl Ep).prod
          (jointSecondarySeedPaddedChoice (P := P) seeds r s).host).symm)
      ((jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs n j ell he he1 r s).symm z)‖ ≤
      jointSecondarySeedCutoffBudget seeds n := by
  change z ∈ jointSecondarySignedNativeSample seeds Q S r s at hz
  by_cases h : s.1 = r
  · simp only [jointSecondarySignedNativeSample,if_pos h] at hz
    rw [jointSecondarySignedNativeCutoff_active seeds B r s h,
      jointSecondarySignedNativeHost_active seeds B Q hQ S scale hs n j ell he he1 r s h,
      jointSecondarySeedPaddedChoice_host]
    rw [((seeds s.1).inner s.2).nativeHostTransition_inverse
      ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B z
      (((seeds s.1).inner s.2).nativeHostSample_target
        ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) B Q hQ S hz)]
    have hz' := ((seeds s.1).inner s.2).adaptedActiveSample_target S hz.2
    have hjet := (seeds s.1).cutoff_jets ell he he1 n k hk s.2 z hz'
    have ht : z ∈ (((seeds s.1).inner s.2).hostTransition ((seeds s.1).outer s.2)).target := by
      rw [((seeds s.1).inner s.2).hostTransition_target
        ((seeds s.1).outer s.2) ((seeds s.1).nested s.2)]
      exact ⟨mem_univ _,hz'⟩
    rw [((seeds s.1).inner s.2).hostTransition_inverse
      ((seeds s.1).outer s.2) ((seeds s.1).nested s.2) z ht] at hjet
    exact hjet.trans (jointSecondarySeedCutoffBudget_piece seeds s.1 n)
  · simp only [jointSecondarySignedNativeSample,if_neg h,mem_empty_iff_false] at hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeCutoff_jets
