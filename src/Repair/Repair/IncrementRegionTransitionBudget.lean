import Repair.IncrementGivenPhaseJets
import Repair.ReferenceOriginalInteractionGeometry

/-! Actual original transition budgets on the constructed interaction
 domain, including zero order from the unchanged original coordinate bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def incrementRegionTransitionProfile (coordinateBound sourceBound : ℝ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then max coordinateBound sourceBound else Spatial j

theorem incrementRegionTransitionProfile_nonneg (coordinateBound sourceBound : ℝ) (Spatial : ℕ → ℝ)
    (hCoordinate : 0 ≤ coordinateBound) (hSource : 0 ≤ sourceBound) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementRegionTransitionProfile coordinateBound sourceBound Spatial j := by
  unfold incrementRegionTransitionProfile
  split_ifs
  · exact hCoordinate.trans (le_max_left _ _)
  · exact hSpatial _

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem increment_actual_spatial_transition_first
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i k : Fin Data.atlas.count) (x : D)
    (hx : x ∈ (Data.atlas.chart i).target)
    (hOther : (Data.atlas.chart i).symm x ∈ (Data.atlas.chart k).source)
    (hSample : x ∈ Data.sourceNormDomain i) :
    ‖fderiv ℝ (Data.atlas.chart k ∘ (Data.atlas.chart i).symm) x‖ ≤ Spatial 1 := by
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i) (Data.atlas.chart k)
  have hz : (0,x) ∈ S.source := ⟨mem_univ _,hx,hOther⟩
  have hs := (repair_reference_host_transition_smooth («Ep» := Ep) (Data.atlas.chart i) (Data.atlas.chart k)
    (hd.atlas_smooth.chart_mem i) (hd.atlas_smooth.chart_mem k)).1
  have hFirst := actual_joint_spatial_jacobian_norm_le S S.source S.open_source hs (0,x) hz
  have hBound := transition.spatial i k 1 le_rfl (0,x) hSample hz
  rw [norm_iteratedFDeriv_one] at hBound
  exact hFirst.trans hBound

theorem increment_actual_interaction_owner_transition_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ) (R buffer coordinateBound sourceBound : ℝ)
    (geometry : RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta R buffer coordinateBound)
    (owner : Fin Data.primaryCount → Fin Data.atlas.count)
    (hSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (Data.atlas.chart (owner nu)).source)
    (hOwnSamples : ∀ nu z, z ∈ Data.primaryDomain nu →
      Data.atlas.chart (owner nu) z.2 ∈ Data.sourceNormDomain (owner nu))
    (hSourceBound : ∀ ih y, y ∈ Data.sourceNormDomain ih → ‖y‖ ≤ sourceBound)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (nu : Fin Data.primaryCount) (hnu : nu=r.val.1.1 ∨ nu=r.val.1.2) :
    geometry.domain ⊆ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (Data.atlas.chart (owner nu))).source ∧
      ∀ j z, z ∈ geometry.domain →
        ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep)
          (Data.atlas.chart i.1) (Data.atlas.chart (owner nu))) z‖ ≤
          incrementRegionTransitionProfile coordinateBound sourceBound Spatial j := by
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (Data.atlas.chart (owner nu))
  have hActive (z) (hz : z ∈ geometry.domain) :
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu := by
    have ha := geometry.active hz
    rcases hnu with rfl | rfl
    · exact (round3_prepared_native_primary_active Data i _ ha.1).1
    · exact (round3_prepared_native_primary_active Data i _ ha.2).1
  have hS : geometry.domain ⊆ S.source := by
    intro z hz
    exact ⟨mem_univ _,(geometry.target hz).2,hSource nu _ (hActive z hz)⟩
  refine ⟨hS,?_⟩
  intro j z hz
  by_cases hj : j=0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    change max ‖z.1‖ ‖Data.atlas.chart (owner nu) ((Data.atlas.chart i.1).symm z.2)‖ ≤ max coordinateBound sourceBound
    exact max_le_max ((norm_fst_le z).trans (geometry.coordinates z hz))
      (hSourceBound _ _ (hOwnSamples nu _ (hActive z hz)))
  · simp only [incrementRegionTransitionProfile,if_neg hj]
    change ‖iteratedFDeriv ℝ j S z‖ ≤ Spatial j
    exact transition.spatial i.1 (owner nu) j (by omega) z
      ((actual_original_native_evaluation_iff Data hd i z).mp (geometry.samples z hz)).1 (hS hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_spatial_transition_first
#print axioms GlobalEmbedding.Continuation.increment_actual_interaction_owner_transition_jets
