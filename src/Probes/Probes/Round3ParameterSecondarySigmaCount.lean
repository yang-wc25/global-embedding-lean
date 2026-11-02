import Probes.Round3ParameterSecondarySigmaPadding

/-! The actual common finite index preserves full ordered secondary sums and exact local counts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {P Ep M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

theorem round3Parameter_secondary_sigma_support_card
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M)) (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (r : Record) (y : Ep × M) :
    (Finset.univ.filter (fun a : Sigma Sub => y ∈
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).support)).card =
    (Finset.univ.filter (fun a : Sub r => y ∈ (geom r a).support)).card := by
  rw [show (Finset.univ.filter (fun a : Sigma Sub => y ∈
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).support)).card =
      ∑ a : Sigma Sub, if y ∈
        (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).support then (1 : ℕ) else 0 from
    Finset.natCast_card_filter _ _]
  rw [Fintype.sum_sigma]
  have he (s : Record) :
      (∑ a : Sub s, if y ∈
        (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r ⟨s,a⟩).support
        then (1 : ℕ) else 0) =
      if s = r then (Finset.univ.filter (fun a : Sub r => y ∈ (geom r a).support)).card else 0 := by
    by_cases h : s = r
    · subst s
      simp only [round3ParameterSecondarySigmaNativeGeometry_active, ite_true]
      exact Finset.sum_boole _ _
    · simp [round3ParameterSecondarySigmaNativeGeometry, h, round3ParameterSecondaryEmptyNativeRawGeometry]
  simp_rw [he]
  simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_sigma_support_card
