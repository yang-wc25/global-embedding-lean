import NormalPolar.JointSecondarySignedNativeSamples
import NormalPolar.JointSecondarySignedNativeObserver

/-! One uniform actual observation profile for the complete finite signed
family. The common finite index is used only for secondary pieces. Native
parameter charts, scaling factors, reconstruction orders and ell are all
quantified after the positive observation sequence has been constructed. -/

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

theorem jointSecondarySignedNativeRaw_transition_smooth
    (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart)
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart).source := by
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell hell he1 r s).2.1]
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,if_pos h]
    exact ((seeds s.1).inner s.2).nativeObserverTransition_smooth B e he
  · simp only [jointSecondarySeedPaddedChoice,if_neg h,OpenPartialHomeomorph.trans_source,
      round3ParameterSecondaryEmptyChoice_native_source,
      preimage_empty,inter_empty]
    exact contDiffOn_empty

theorem jointSecondarySignedNativeRaw_transition_inverse_smooth
    (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart).symm
      (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart).target := by
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell hell he1 r s).2.1]
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,if_pos h]
    exact ((seeds s.1).inner s.2).nativeObserverTransition_inverse_smooth B e he
  · simp only [jointSecondarySeedPaddedChoice,if_neg h,OpenPartialHomeomorph.trans_target,
      round3ParameterSecondaryEmptyChoice_native_target,empty_inter]
    exact contDiffOn_empty

theorem jointSecondarySignedNativeRaw_active_local
    (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (e : OpenPartialHomeomorph M D) (hSe : S ⊆ e.source)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (z : X)
    (hz : z ∈ Q ×ˢ (e '' S))
    (ha : (z.1,e.symm z.2) ∈
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).support) :
    z ∈ (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart).source := by
  rw [jointSecondarySignedNativeRaw_support] at ha
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell hell he1 r s).2.1]
  by_cases h : s.1 = r
  · simp only [if_pos h] at ha
    simp only [jointSecondarySeedPaddedChoice,if_pos h]
    obtain ⟨x,hx,hxz⟩ := hz.2
    have hze : z.2 ∈ e.target := hxz ▸ e.map_source (hSe hx)
    exact ((seeds s.1).inner s.2).nativeObserverTransition_active B e z (hQ hz.1) hze ha.2.2.1
  · simp only [if_neg h,mem_empty_iff_false] at ha

theorem jointSecondarySignedNativeRaw_observer_jets_uniform
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧
      ∀ (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target)
      (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
      (n j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (he1 : ell ≤ 1)
      (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (z : X),
      z ∈ Q ×ˢ (e '' S) →
      (z.1,e.symm z.2) ∈
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).support →
      ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k
        ((jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell hell he1 r s).chart ∘
          (fun y : X => (y.1,e.symm y.2))) z‖ ≤ T k := by
  let Sub := Σ r, Fin (seeds r).refinement.count
  choose C hC hb using (fun s : Sub =>
    ((seeds s.1).inner s.2).exists_native_observer_jets (P := P) (Ep := Ep) e he S hS hSe)
  let T : ℕ → ℝ := fun k => 1+∑ s : Sub, C s k
  have hT : ∀ k, 0 < T k := fun k =>
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun s _ => (hC s k).le))
  have hpiece : ∀ s k, C s k ≤ T k := fun s k =>
    (Finset.single_le_sum (fun s _ => (hC s k).le) (Finset.mem_univ s)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨T,hT,?_⟩
  intro B Q hQ scale hs n j ell hell he1 r s z hz ha k hk
  rw [jointSecondarySignedNativeRaw_support] at ha
  rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell hell he1 r s).2.1]
  by_cases h : s.1 = r
  · simp only [if_pos h] at ha
    simp only [jointSecondarySeedPaddedChoice,if_pos h]
    exact (hb s B ell hell he1 k hk z (hQ hz.1) hz.2 ha.2.2.1).trans (hpiece s k)
  · simp only [if_neg h,mem_empty_iff_false] at ha

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw_transition_smooth
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw_transition_inverse_smooth
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw_observer_jets_uniform
