import Probes.ActualIncrementSecondaryPaddingConsumer

/-! Real bindings and effective support survive the common finite-index construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

theorem actual_secondary_sigma_padding_bindings
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (choice : (r : Record) → Sub r → ActualOriginalSecondaryChoice Ep M m)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (pair : Record → Set (Ep × M))
    (hc : ∀ r a, (geom r a).c = (choice r a).c)
    (hchart : ∀ r a, (geom r a).chart = (choice r a).chart)
    (hphase : ∀ r a, (geom r a).phase = phase r)
    (hsupport : ∀ r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' pair r ⊆ Subtype.val ⁻¹' (geom r a).support)
    (hpair : ∀ r a, (geom r a).support ⊆ pair r) :
    ∀ r a,
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).c =
        (actualSecondarySigmaChoice Sub host choice r a).c ∧
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).chart =
        (actualSecondarySigmaChoice Sub host choice r a).chart ∧
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).phase = phase r ∧
      (tsupport (fun y : W => (actualSecondarySigmaChoice Sub host choice r a).cutoff y.val) ∩
        Subtype.val ⁻¹' pair r ⊆ Subtype.val ⁻¹'
          (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).support) ∧
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).support ⊆ pair r := by
  intro r ⟨s,a⟩
  by_cases h : s = r
  · subst s
    simp only [actualSecondarySigmaGeometry_active,actualSecondarySigmaChoice_active]
    exact ⟨hc r a,hchart r a,hphase r a,hsupport r a,hpair r a⟩
  · simp [actualSecondarySigmaGeometry,actualSecondarySigmaChoice,h,
      actualSecondaryEmptyRawGeometry,actualSecondaryEmptyChoice]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_sigma_padding_bindings
