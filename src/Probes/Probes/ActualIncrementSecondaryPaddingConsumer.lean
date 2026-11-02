import Probes.ActualIncrementSecondarySigmaPadding

/-! The actual common finite index preserves full ordered secondary sums and exact local counts. -/
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

theorem actual_secondary_sigma_support_card
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (Sub : Record → Type*) [∀ r, Fintype (Sub r)]
    (host : Record → OpenPartialHomeomorph M D)
    (hHost : ∀ r, host r ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (phase : Record → Ep × M → ℝ)
    (geom : (r : Record) → Sub r → ActualSecondaryRawGeometry F hF n j ell Mg W)
    (r : Record) (y : Ep × M) :
    (Finset.univ.filter (fun a : Sigma Sub => y ∈
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).support)).card =
    (Finset.univ.filter (fun a : Sub r => y ∈ (geom r a).support)).card := by
  rw [show (Finset.univ.filter (fun a : Sigma Sub => y ∈
      (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).support)).card =
      ∑ a : Sigma Sub, if y ∈
        (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r a).support then (1 : ℕ) else 0 from
    Finset.natCast_card_filter _ _]
  rw [Fintype.sum_sigma]
  have he (s : Record) :
      (∑ a : Sub s, if y ∈
        (actualSecondarySigmaGeometry F hF n j ell Mg W Sub host hHost phase geom r ⟨s,a⟩).support
        then (1 : ℕ) else 0) =
      if s = r then (Finset.univ.filter (fun a : Sub r => y ∈ (geom r a).support)).card else 0 := by
    by_cases h : s = r
    · subst s
      simp only [actualSecondarySigmaGeometry_active, ite_true]
      exact Finset.sum_boole _ _
    · simp [actualSecondarySigmaGeometry, h, actualSecondaryEmptyRawGeometry]
  simp_rw [he]
  simp

variable {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]

private local instance signedRecordFinite : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem actual_secondary_sigma_full_ordered_sum
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (Sub : ActualSecondarySignedRecord Label → Type*) [∀ r, Fintype (Sub r)]
    (host : ActualSecondarySignedRecord Label → OpenPartialHomeomorph M D)
    (choice : (r : ActualSecondarySignedRecord Label) → Sub r → ActualOriginalSecondaryChoice Ep M m) :
    actualOriginalSecondarySum F hF g input length tau delta
      (actualSecondarySigmaChoice Sub host choice) =
    actualSecondaryNonzeroSum (fun nu mu branch y =>
      if h : nu ≠ mu ∨ branch = 0 ∨ branch = 3 then
        ∑ a : Sub ⟨((nu,mu),branch),h⟩,
          actualOriginalSecondaryPiece F hF g input length tau delta ((nu,mu),branch)
            (choice ⟨((nu,mu),branch),h⟩ a) y
      else 0) := by
  funext y
  unfold actualOriginalSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro nu _
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro branch hbranch
  have hb : nu ≠ mu ∨ branch = 0 ∨ branch = 3 := (Finset.mem_filter.mp hbranch).2
  simp only [dif_pos hb]
  have hh := congrFun (actual_secondary_sigma_piece_row_sum (Record := ActualSecondarySignedRecord Label) F hF g input length tau delta
    (fun r : ActualSecondarySignedRecord Label => r.val) Sub host choice ⟨((nu,mu),branch),hb⟩) y
  simpa only [Finset.sum_apply] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_secondary_sigma_support_card
#print axioms GlobalEmbedding.Continuation.actual_secondary_sigma_full_ordered_sum
