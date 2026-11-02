import Probes.Round3ParameterSecondarySigmaPadding

/-! Real bindings and effective support survive the common finite-index construction. -/
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

theorem round3Parameter_secondary_sigma_native_bindings
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M)) (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (pair : Record → Set (Ep × M))
    (hc : ∀ r a, (geom r a).c = (((choice r a).pullback B).toNative).c)
    (hchart : ∀ r a, (geom r a).chart = (((choice r a).pullback B).toNative).chart)
    (hphase : ∀ r a, (geom r a).phase = phase r)
    (hsupport : ∀ r a, tsupport (fun y : W => (((choice r a).pullback B).toNative).cutoff y.val) ∩
      Subtype.val ⁻¹' pair r ⊆ Subtype.val ⁻¹' (geom r a).support)
    (hpair : ∀ r a, (geom r a).support ⊆ pair r) :
    ∀ r a,
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).c =
        (round3ParameterSecondarySigmaNativeChoice B Sub host choice r a).c ∧
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).chart =
        (round3ParameterSecondarySigmaNativeChoice B Sub host choice r a).chart ∧
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).phase = phase r ∧
      (tsupport (fun y : W => (round3ParameterSecondarySigmaNativeChoice B Sub host choice r a).cutoff y.val) ∩
        Subtype.val ⁻¹' pair r ⊆ Subtype.val ⁻¹'
          (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).support) ∧
      (round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r a).support ⊆ pair r := by
  intro r ⟨s,a⟩
  by_cases h : s = r
  · subst s
    simp only [round3ParameterSecondarySigmaNativeGeometry_active,round3ParameterSecondarySigmaNativeChoice_active]
    exact ⟨hc r a,hchart r a,hphase r a,hsupport r a,hpair r a⟩
  · simp [round3ParameterSecondarySigmaNativeGeometry,round3ParameterSecondarySigmaNativeChoice,h,
      round3ParameterSecondaryEmptyNativeRawGeometry,round3ParameterSecondaryEmptyChoice,
      round3ParameterSecondarySigmaChoice,Round3ParameterSecondaryChoice.pullback,
      Round3ParameterSecondaryChoice.toNative]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_sigma_native_bindings
