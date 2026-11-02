import Probes.Round3PreparedPrimaryPiece

/-! Exact zero padding of actual primary host pieces into one finite index.
The ordinary partition sum and active support count are unchanged. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

def round3PreparedPrimarySigmaPiece
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (Sub : Fin Data.primaryCount → Type*)
    (piece : ∀ nu, Sub nu → Round3PreparedPrimaryPiece Data baseIndex.2 nu W)
    (nu : Fin Data.primaryCount) (a : Sigma Sub) :
    Round3PreparedPrimaryPiece Data baseIndex.2 nu W :=
  if h : a.1 = nu then piece nu (h ▸ a.2) else round3PreparedPrimaryEmpty Data hd baseIndex nu W

@[simp] theorem round3PreparedPrimarySigmaPiece_active
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (Sub : Fin Data.primaryCount → Type*)
    (piece : ∀ nu, Sub nu → Round3PreparedPrimaryPiece Data baseIndex.2 nu W)
    (nu : Fin Data.primaryCount) (a : Sub nu) :
    round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu ⟨nu,a⟩ = piece nu a := by
  simp [round3PreparedPrimarySigmaPiece]

theorem round3_prepared_primary_sigma_cutoff_sum
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (Sub : Fin Data.primaryCount → Type*) [∀ nu, Fintype (Sub nu)]
    (piece : ∀ nu, Sub nu → Round3PreparedPrimaryPiece Data baseIndex.2 nu W)
    (nu : Fin Data.primaryCount) (y : Ep × M) :
    (∑ a : Sigma Sub, (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu a).cutoff y) =
      ∑ a : Sub nu, (piece nu a).cutoff y := by
  rw [Fintype.sum_sigma]
  have he (mu : Fin Data.primaryCount) :
      (∑ a : Sub mu, (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu ⟨mu,a⟩).cutoff y) =
      if mu = nu then ∑ a : Sub nu, (piece nu a).cutoff y else 0 := by
    by_cases h : mu = nu
    · subst mu
      simp only [round3PreparedPrimarySigmaPiece_active,ite_true]
    · simp only [round3PreparedPrimarySigmaPiece,h,dite_false,round3PreparedPrimaryEmpty_cutoff,
        Pi.zero_apply,Finset.sum_const_zero,ite_false]
  simp_rw [he]
  simp

theorem round3_prepared_primary_sigma_support_card
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount) (W : Set (Ep × M))
    (Sub : Fin Data.primaryCount → Type*) [∀ nu, Fintype (Sub nu)]
    (piece : ∀ nu, Sub nu → Round3PreparedPrimaryPiece Data baseIndex.2 nu W)
    (nu : Fin Data.primaryCount) (y : Ep × M) :
    (Finset.univ.filter (fun a : Sigma Sub => y ∈ tsupport
      (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu a).cutoff)).card =
    (Finset.univ.filter (fun a : Sub nu => y ∈ tsupport (piece nu a).cutoff)).card := by
  rw [show (Finset.univ.filter (fun a : Sigma Sub => y ∈ tsupport
      (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu a).cutoff)).card =
      ∑ a : Sigma Sub, if y ∈ tsupport
        (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu a).cutoff then (1 : ℕ) else 0 from
      Finset.natCast_card_filter _ _]
  rw [Fintype.sum_sigma]
  have he (mu : Fin Data.primaryCount) :
      (∑ a : Sub mu, if y ∈ tsupport
          (round3PreparedPrimarySigmaPiece Data hd baseIndex W Sub piece nu ⟨mu,a⟩).cutoff
        then (1 : ℕ) else 0) =
      if mu = nu then (Finset.univ.filter (fun a : Sub nu => y ∈ tsupport (piece nu a).cutoff)).card else 0 := by
    by_cases h : mu = nu
    · subst mu
      simp only [round3PreparedPrimarySigmaPiece_active,ite_true]
      exact Finset.sum_boole _ _
    · simp only [round3PreparedPrimarySigmaPiece,h,dite_false,round3PreparedPrimaryEmpty_cutoff,
        tsupport_zero,mem_empty_iff_false,ite_false,Finset.sum_const_zero]
  simp_rw [he]
  simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_sigma_cutoff_sum
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_sigma_support_card
