import Probes.Round3ParameterSecondaryEmptyPadding

/-! One physical sigma choice is selected before all parameter observers.
Its empty slots retain their genuine parameter-conjugated chart functions;
only their empty source/target gives zero contributions.

Different signed phases may have different finite refinements. A common
sigma index preserves each real active chart exactly and uses actual empty
charts for all other slots. Its scalar partition and literal finite waves
have exactly the same sums as the original dependent families. -/
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

def round3ParameterSecondarySigmaChoice
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (r : Record) (a : Sigma Sub) : Round3ParameterSecondaryChoice P M m :=
  if h : a.1 = r then choice r (h ▸ a.2) else round3ParameterSecondaryEmptyChoice (host r)

@[simp] theorem round3ParameterSecondarySigmaChoice_active
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (r : Record) (a : Sub r) :
    round3ParameterSecondarySigmaChoice Sub host choice r ⟨r,a⟩ = choice r a := by
  simp [round3ParameterSecondarySigmaChoice]

def round3ParameterSecondarySigmaNativeChoice
    (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (r : Record) (a : Sigma Sub) : ActualOriginalSecondaryChoice Ep M m :=
  ((round3ParameterSecondarySigmaChoice Sub host choice r a).pullback B).toNative

@[simp] theorem round3ParameterSecondarySigmaNativeChoice_active
    (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (r : Record) (a : Sub r) :
    round3ParameterSecondarySigmaNativeChoice B Sub host choice r ⟨r,a⟩ =
      ((choice r a).pullback B).toNative := by
  unfold round3ParameterSecondarySigmaNativeChoice
  rw [round3ParameterSecondarySigmaChoice_active]

def round3ParameterSecondarySigmaNativeGeometry
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M)) (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (r : Record) (a : Sigma Sub) : ActualSecondaryRawGeometry F hF n j ell Mg W :=
  if h : a.1 = r then geom r (h ▸ a.2)
    else round3ParameterSecondaryEmptyNativeRawGeometry F hF n j ell Mg W B (host r) (hHost r) (phase r)

@[simp] theorem round3ParameterSecondarySigmaNativeGeometry_active
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M)) (B : OpenPartialHomeomorph P Ep)
    (Sub : Record → Type*) (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (r : Record) (a : Sub r) :
    round3ParameterSecondarySigmaNativeGeometry F hF n j ell Mg W B Sub host hHost phase geom r ⟨r,a⟩ = geom r a := by
  simp [round3ParameterSecondarySigmaNativeGeometry]

theorem round3Parameter_secondary_sigma_cutoff_sum
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m)
    (r : Record) (y : P × M) :
    (∑ a : Sigma Sub, (round3ParameterSecondarySigmaChoice Sub host choice r a).cutoff y) =
      ∑ a : Sub r, (choice r a).cutoff y := by
  rw [Fintype.sum_sigma]
  have he (s : Record) :
      (∑ a : Sub s, (round3ParameterSecondarySigmaChoice Sub host choice r ⟨s,a⟩).cutoff y) =
      if s = r then ∑ a : Sub r, (choice r a).cutoff y else 0 := by
    by_cases h : s = r
    · subst s
      simp only [round3ParameterSecondarySigmaChoice_active, ite_true]
    · simp [round3ParameterSecondarySigmaChoice, h, round3ParameterSecondaryEmptyChoice]
  simp_rw [he]
  simp

variable {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]

theorem round3Parameter_secondary_sigma_piece_row_sum
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (record : Record → (Label × Label) × Fin 4)
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (choice : (r : Record) → Sub r → Round3ParameterSecondaryChoice P M m) (r : Record) :
    (∑ a : Sigma Sub, round3ParameterSecondaryPiece F hF g input length tau delta (record r)
      (round3ParameterSecondarySigmaChoice Sub host choice r a)) =
      ∑ a : Sub r, round3ParameterSecondaryPiece F hF g input length tau delta (record r) (choice r a) := by
  rw [Fintype.sum_sigma]
  have he (s : Record) :
      (∑ a : Sub s, round3ParameterSecondaryPiece F hF g input length tau delta (record r)
        (round3ParameterSecondarySigmaChoice Sub host choice r ⟨s,a⟩)) =
      if s = r then ∑ a : Sub r,
        round3ParameterSecondaryPiece F hF g input length tau delta (record r) (choice r a) else 0 := by
    by_cases h : s = r
    · subst s
      simp only [round3ParameterSecondarySigmaChoice_active, ite_true]
    · simp [round3ParameterSecondarySigmaChoice, h, round3Parameter_secondary_empty_piece]
  simp_rw [he]
  simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondarySigmaNativeGeometry
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_sigma_cutoff_sum
#print axioms GlobalEmbedding.Continuation.round3Parameter_secondary_sigma_piece_row_sum
