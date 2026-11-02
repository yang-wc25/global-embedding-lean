import Repair.IncrementGivenPhaseJets

/-! Original cumulative and weighted norms of the same total and spatial
 phase covectors. Finiteness follows from actual transition derivatives;
 neither the fixed-packet norm nor a completed increment is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

private theorem givenPhasePrefix_bound (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    {k j : ℕ} (hkj : k ≤ j) : A k ≤ bufferedTransitionPrefix A j := by
  have h := Finset.single_le_sum (fun l (_ : l ∈ Finset.range (j+1)) => hA l)
    (show k ∈ Finset.range (j+1) by simp; omega)
  exact h.trans (by unfold bufferedTransitionPrefix; linarith)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem increment_given_actual_phase_weighted_norms
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (owner : Fin Data.primaryCount → Fin Data.atlas.count)
    (xi : Fin Data.primaryCount → D →L[ℝ] ℝ) (weight : Fin Data.primaryCount → ℝ)
    (cap covectorBound : ℝ) (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound)
    (hWeight : ∀ nu, |weight nu| ≤ cap) (hXi : ∀ nu, ‖xi nu‖ ≤ covectorBound)
    (hphase : ∀ nu, Data.phase nu = fun z => weight nu*xi nu (Data.atlas.chart (owner nu) z.2))
    (hSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (Data.atlas.chart (owner nu)).source)
    (Parameter Spatial : ℕ → ℝ) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (nu : Fin Data.primaryCount) (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    (paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu)).toReal ≤
        (j+1)*bufferedTransitionPrefix (incrementGivenPhaseTotalProfile (m+1) d cap covectorBound Spatial) j) ∧
    (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data nu)
      (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalPhaseCovectorCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu)).toReal ≤
        (j+1)*bufferedTransitionPrefix (incrementGivenPhaseSpatialProfile (m+1) d cap covectorBound Spatial) j) := by
  let O := incrementsOriginalPrimaryDifferentiation Data nu
  let U := actualOriginalPhaseOpen Data nu
  let S := incrementsOriginalPrimaryEvaluation Data nu
  let T := incrementGivenPhaseTotalProfile (m+1) d cap covectorBound Spatial
  let V := incrementGivenPhaseSpatialProfile (m+1) d cap covectorBound Spatial
  have hT : ∀ k, 0 ≤ T k := incrementGivenPhaseTotalProfile_nonneg (m+1) d cap covectorBound Spatial hCap hCovector hSpatial
  have hV : ∀ k, 0 ≤ V k := incrementGivenPhaseSpatialProfile_nonneg (m+1) d cap covectorBound Spatial hCap hCovector hSpatial
  have hO := actual_original_primaryDifferentiation_open Data hd.primary_open nu
  have hU := actualOriginalPhaseOpen_open Data hd nu
  have hSU := actualOriginalPhaseOpen_sample Data hd nu
  have hTotal := actualOriginalTotalPhaseCoordinates_contDiffOn Data hd hs nu
  have hSpatialSmooth (i) : ContDiffOn ℝ ∞ (incrementsOriginalPhaseCovectorCoordinates Data nu i) (U i) := by
    have hf := (actualOriginalJointPhase_contDiffOn Data hd hs nu i).fderiv_of_isOpen
      (hU i) (m := ∞) (by simp)
    apply ((incrementGivenSpatialExtraction (m+1) d).contDiff.comp_contDiffOn hf).congr
    intro z hz
    exact (increment_given_phase_spatial_coordinates Data hd nu (owner nu) (xi nu) (weight nu)
      (hphase nu) i z hz.1.1 (hSource nu _ hz.1.2))
  have hJets (i) (k : ℕ) (y) (hy : y ∈ S i) :=
    increment_given_actual_phase_gradient_jets Data hd hs nu (owner nu) (xi nu) (weight nu)
      cap covectorBound hCap hCovector (hWeight nu) (hXi nu) (hphase nu) (hSource nu)
      Parameter Spatial transition i y hy k
  have hTotalNorm := parameterRound2_paperAtlasWeighted_le_of_weighted_jets j ell (bufferedTransitionPrefix T j)
    hell hell1 (by unfold bufferedTransitionPrefix; exact add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => hT k)))
    (actualOriginalTotalPhaseCoordinates Data nu) U S hU hSU hTotal (by
      intro i k hk y hy
      apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell.le hell1)).trans
      exact (hJets i k y hy).1.trans (givenPhasePrefix_bound T hT hk))
  have hSpatialNorm := parameterRound2_paperAtlasWeighted_le_of_weighted_jets j ell (bufferedTransitionPrefix V j)
    hell hell1 (by unfold bufferedTransitionPrefix; exact add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => hV k)))
    (incrementsOriginalPhaseCovectorCoordinates Data nu) U S hU hSU hSpatialSmooth (by
      intro i k hk y hy
      apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell.le hell1)).trans
      exact (hJets i k y hy).2.trans (givenPhasePrefix_bound V hV hk))
  have hTotalEq := actual_paperAtlasWeighted_open_restrict 0 j ell
    (actualOriginalTotalPhaseCoordinates Data nu) O U S hO hU (fun _ => inter_subset_left) hSU
  have hSpatialEq := actual_paperAtlasWeighted_open_restrict 0 j ell
    (incrementsOriginalPhaseCovectorCoordinates Data nu) O U S hO hU (fun _ => inter_subset_left) hSU
  rw [hTotalEq,hSpatialEq]
  exact ⟨hTotalNorm,hSpatialNorm⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_actual_phase_weighted_norms
