import NormalPolar.PassiveSecondarySeedFamily
import NormalPolar.JointSecondarySignedPadding

/-! The one physical signed finite family has its literal canonical native
geometry in every original parameter chart. Active slots keep the complete
inner target intersected with B.target. Inactive slots use the actual
parameter-conjugated empty chart, not a substituted dummy function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M P Ep Rec : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Rec] [DecidableEq Rec]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {phase : Rec → M → ℝ} {K O : Rec → Set M}
  (seeds : (r : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (phase r) (K r) (O r))
  (B : OpenPartialHomeomorph P Ep)

def passiveSecondarySeed_padded_raw
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
      (fun _ => contMDiff_const_rescale F hF scale) n j ell
      (jointSecondarySeedGeometryBudget seeds (max n j))
      (round3ParameterNativeDomain B (univ : Set (P × M))) :=
  if s.1 = r then
    (passiveSecondarySeed_family_raw F hF (phase s.1) (K s.1) (O s.1)
      (seeds s.1) B scale hs n j ell he he1 s.2).enlargeBudget
      (jointSecondarySeedGeometryBudget_piece seeds s.1 (max n j))
  else round3ParameterSecondaryEmptyNativeRawGeometry (fun _ : Ep => scale • F)
    (fun _ => contMDiff_const_rescale F hF scale) n j ell
    (jointSecondarySeedGeometryBudget seeds (max n j))
    (round3ParameterNativeDomain B (univ : Set (P × M))) B
    ((seeds s.1).outer s.2).chart ((seeds s.1).outer s.2).maximal (fun z => phase r z.2)

variable (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
  (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
  (r : Rec) (s : Σ r, Fin (seeds r).refinement.count)

theorem passiveSecondarySeed_padded_choice :
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).c =
        ((jointSecondarySeedPaddedChoice seeds r s).pullback B).c ∧
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).chart =
        ((jointSecondarySeedPaddedChoice seeds r s).pullback B).chart ∧
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).phase =
        (fun z => phase r z.2) := by
  by_cases h : s.1 = r
  · simp only [passiveSecondarySeed_padded_raw,jointSecondarySeedPaddedChoice,if_pos h]
    refine ⟨passiveSecondarySeed_family_c F hF _ _ _ _ B _ _ _ _ _ _ _ _,rfl,?_⟩
    exact (passiveSecondarySeed_family_phase F hF _ _ _ _ B _ _ _ _ _ _ _ _).trans (by rw [h])
  · simp only [passiveSecondarySeed_padded_raw,jointSecondarySeedPaddedChoice,if_neg h]
    exact ⟨rfl,rfl,rfl⟩

theorem passiveSecondarySeed_padded_sample :
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).sample =
      if s.1 = r then B.target ×ˢ ((seeds s.1).inner s.2).chart.target else ∅ := by
  by_cases h : s.1 = r
  · simp only [passiveSecondarySeed_padded_raw,if_pos h]
    exact passiveSecondarySeed_family_sample F hF _ _ _ _ B _ _ _ _ _ _ _ _
  · simp only [passiveSecondarySeed_padded_raw,if_neg h]
    rfl

theorem passiveSecondarySeed_padded_sample_target :
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).sample =
      (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).chart.target := by
  by_cases h : s.1 = r
  · simp only [passiveSecondarySeed_padded_raw,if_pos h]
    exact passiveSecondarySeed_family_sample_target F hF _ _ _ _ B _ _ _ _ _ _ _ _
  · simp only [passiveSecondarySeed_padded_raw,if_neg h]
    exact (round3ParameterSecondaryEmptyChoice_native_target B _).symm

theorem passiveSecondarySeed_padded_support :
    (passiveSecondarySeed_padded_raw seeds B scale hs n j ell he he1 r s).support =
      if s.1 = r then round3ParameterNativeDomain B
        ((univ : Set P) ×ˢ (tsupport ((seeds s.1).refinement.cutoff s.2) ∩ K r)) else ∅ := by
  by_cases h : s.1 = r
  · simp only [passiveSecondarySeed_padded_raw,if_pos h]
    exact (passiveSecondarySeed_family_support F hF _ _ _ _ B _ _ _ _ _ _ _ _).trans
      (congrArg (fun S : Set M => round3ParameterNativeDomain B
        ((univ : Set P) ×ˢ (tsupport ((seeds s.1).refinement.cutoff s.2) ∩ S)))
        (congrArg K h))
  · simp only [passiveSecondarySeed_padded_raw,if_neg h]
    rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_padded_raw
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_padded_choice
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_padded_sample_target
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_padded_support
