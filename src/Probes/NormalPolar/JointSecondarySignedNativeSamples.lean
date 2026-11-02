import NormalPolar.JointSecondarySignedSamples
import NormalPolar.PassiveSecondarySeedPadding

/-! Compact active samples in the canonical original parameter chart. The
actual physical choices and the entire support are unchanged. Only the set
where quantitative jets are requested is the original Q times the actual
adapted image of S intersected with the subordinate cutoff support. -/

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

def jointSecondarySignedNativeSample (Q : Set Ep) (S : Set M)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) : Set X :=
  if s.1 = r then Q ×ˢ ((seeds s.1).inner s.2).adaptedActiveSample S else ∅

theorem jointSecondarySignedNativeSample_compact (Q : Set Ep) (S : Set M)
    (hQ : IsCompact Q) (hS : IsCompact S)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    IsCompact (jointSecondarySignedNativeSample seeds Q S r s) := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySignedNativeSample,if_pos h]
    exact ((seeds s.1).inner s.2).jointAdaptedActiveSample_compact Q S hQ hS
  · simp only [jointSecondarySignedNativeSample,if_neg h]
    exact isCompact_empty

theorem jointSecondarySignedNativeSample_subset (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    jointSecondarySignedNativeSample seeds Q S r s ⊆
      (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).sample := by
  rw [passiveSecondarySeed_padded_sample]
  by_cases h : s.1 = r
  · simp only [jointSecondarySignedNativeSample,if_pos h]
    exact fun _ hz => ⟨hQ hz.1,((seeds s.1).inner s.2).adaptedActiveSample_target S hz.2⟩
  · simp only [jointSecondarySignedNativeSample,if_neg h]
    exact Subset.rfl

def jointSecondarySignedNativeRaw (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
      (fun _ => contMDiff_const_rescale F hF scale) n j ell
      (jointSecondarySeedGeometryBudget seeds (max n j))
      (round3ParameterNativeDomain B (univ : Set (P × M))) :=
  (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).restrictSample
    (jointSecondarySignedNativeSample seeds Q S r s)
    (jointSecondarySignedNativeSample_subset seeds B Q hQ S scale hs n j ell he he1 r s)

theorem jointSecondarySignedNativeRaw_choice (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).c =
        ((jointSecondarySeedPaddedChoice seeds r s).pullback B).c ∧
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).chart =
        ((jointSecondarySeedPaddedChoice seeds r s).pullback B).chart ∧
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).phase =
        (fun z => phase r z.2) :=
  passiveSecondarySeed_padded_choice seeds B scale hs n j ell he he1 r s

theorem jointSecondarySignedNativeRaw_support (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).support =
      if s.1 = r then round3ParameterNativeDomain B
        ((univ : Set P) ×ˢ (tsupport ((seeds s.1).refinement.cutoff s.2) ∩ K r)) else ∅ :=
  passiveSecondarySeed_padded_support seeds B scale hs n j ell he he1 r s

theorem jointSecondarySignedNativeRaw_active_sample (B : OpenPartialHomeomorph P Ep)
    (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (e : OpenPartialHomeomorph M D) (hSe : S ⊆ e.source)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) (z : X)
    (hz : z ∈ Q ×ˢ (e '' S))
    (ha : (z.1,e.symm z.2) ∈
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).support) :
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).chart
      (z.1,e.symm z.2) ∈
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs n j ell he he1 r s).sample := by
  rw [jointSecondarySignedNativeRaw_support] at ha
  by_cases h : s.1 = r
  · simp only [if_pos h] at ha
    have hcut : e.symm z.2 ∈ tsupport ((seeds s.1).refinement.cutoff s.2) := ha.2.2.1
    rw [(jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs n j ell he he1 r s).2.1]
    simp only [jointSecondarySeedPaddedChoice,if_pos h]
    change round3ParameterChartPullback B
      ((OpenPartialHomeomorph.refl P).prod ((seeds s.1).inner s.2).chart) (z.1,e.symm z.2) ∈ _
    rw [passiveSecondarySeed_chart_apply B ((seeds s.1).inner s.2).chart
      (z.1,e.symm z.2) (hQ hz.1)]
    change (z.1,((seeds s.1).inner s.2).chart (e.symm z.2)) ∈
      jointSecondarySignedNativeSample seeds Q S r s
    simp only [jointSecondarySignedNativeSample,if_pos h,mem_prod]
    exact ⟨hz.1,((seeds s.1).inner s.2).adaptedActiveSample_active e S hSe z.2 hz.2 hcut⟩
  · simpa only [if_neg h,mem_empty_iff_false] using ha

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeSample_compact
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw_choice
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedNativeRaw_active_sample
