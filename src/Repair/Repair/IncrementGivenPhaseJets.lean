import Repair.IncrementGivenPhaseCoordinates

/-! The true template phase in every original observing chart has a
 numerical full-joint gradient profile. Only original positive transition
 derivatives are read; no phase value or completed Given profile is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def incrementGivenPhasePositiveProfile (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  cap*covectorBound*Spatial j*linearModelFactor (parameterTensorModelEquiv n d).symm j

def incrementGivenPhaseTotalProfile (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖incrementGivenTotalExtraction (n+d)‖*incrementGivenPhasePositiveProfile n d cap covectorBound Spatial (j+1)

def incrementGivenPhaseSpatialProfile (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  ‖incrementGivenSpatialExtraction n d‖*incrementGivenPhasePositiveProfile n d cap covectorBound Spatial (j+1)

theorem incrementGivenPhasePositiveProfile_nonneg (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementGivenPhasePositiveProfile n d cap covectorBound Spatial j :=
  mul_nonneg (mul_nonneg (mul_nonneg hCap hCovector) (hSpatial j)) (linearModelFactor_nonneg _ _)

theorem incrementGivenPhaseTotalProfile_nonneg (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementGivenPhaseTotalProfile n d cap covectorBound Spatial j :=
  mul_nonneg (norm_nonneg (incrementGivenTotalExtraction (n+d))) (incrementGivenPhasePositiveProfile_nonneg n d cap covectorBound Spatial hCap hCovector hSpatial _)

theorem incrementGivenPhaseSpatialProfile_nonneg (n d : ℕ) (cap covectorBound : ℝ) (Spatial : ℕ → ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hSpatial : ∀ j, 0 ≤ Spatial j) (j : ℕ) :
    0 ≤ incrementGivenPhaseSpatialProfile n d cap covectorBound Spatial j :=
  mul_nonneg (norm_nonneg (incrementGivenSpatialExtraction n d)) (incrementGivenPhasePositiveProfile_nonneg n d cap covectorBound Spatial hCap hCovector hSpatial _)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "I" => 𝓘(ℝ,D)

theorem increment_given_actual_phase_positive_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (nu : Fin Data.primaryCount) (owner : Fin Data.atlas.count)
    (xi : D →L[ℝ] ℝ) (weight cap covectorBound : ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hWeight : |weight| ≤ cap) (hXi : ‖xi‖ ≤ covectorBound)
    (hphase : Data.phase nu = fun z => weight*xi (Data.atlas.chart owner z.2))
    (hSource : ∀ z ∈ Data.primaryDomain nu, z.2 ∈ (Data.atlas.chart owner).source)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Y)
    (hy : y ∈ incrementsOriginalPrimaryEvaluation Data nu i)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (actualOriginalJointPhase Data nu i) y‖ ≤
      incrementGivenPhasePositiveProfile (m+1) d cap covectorBound Spatial j := by
  let a := parameterTensorModelEquiv (m+1) d
  let z := a.symm y
  let S := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (Data.atlas.chart owner)
  let L := xi.comp (ContinuousLinearMap.snd ℝ Ep D)
  let f : X → ℝ := fun z => weight*L (S z)
  have hS : z ∈ S.source := ⟨mem_univ _,hy.1.1.1,hSource _ hy.2⟩
  have hs := (repair_reference_host_transition_smooth («Ep» := Ep) (Data.atlas.chart i.1)
    (Data.atlas.chart owner) (hd.atlas_smooth.chart_mem i.1) (hd.atlas_smooth.chart_mem owner)).1
  have hL : ‖L‖ ≤ covectorBound := (xi.opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg xi) (ContinuousLinearMap.norm_snd_le ℝ Ep D)).trans hXi)
  have hNative := increment_given_positive_linear_jets L S z (hs.contDiffAt (S.open_source.mem_nhds hS))
    weight cap covectorBound (Spatial j) hWeight hCap hL hCovector j
    (transition.spatial i.1 owner j hj z hy.1.2.1 hS)
  have he : actualOriginalJointPhase Data nu i = f ∘ a.symm := by
    funext u
    simp only [actualOriginalJointPhase,hphase,Function.comp_apply]
    rfl
  rw [he]
  exact (norm_iteratedFDeriv_comp_equiv_le a.symm f j y).trans
    (mul_le_mul_of_nonneg_right hNative (linearModelFactor_nonneg _ _))

variable [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]

theorem increment_given_actual_phase_gradient_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (owner : Fin Data.atlas.count)
    (xi : D →L[ℝ] ℝ) (weight cap covectorBound : ℝ)
    (hCap : 0 ≤ cap) (hCovector : 0 ≤ covectorBound) (hWeight : |weight| ≤ cap) (hXi : ‖xi‖ ≤ covectorBound)
    (hphase : Data.phase nu = fun z => weight*xi (Data.atlas.chart owner z.2))
    (hSource : ∀ z ∈ Data.primaryDomain nu, z.2 ∈ (Data.atlas.chart owner).source)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Y)
    (hy : y ∈ incrementsOriginalPrimaryEvaluation Data nu i) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (actualOriginalTotalPhaseCoordinates Data nu i) y‖ ≤
      incrementGivenPhaseTotalProfile (m+1) d cap covectorBound Spatial j ∧
    ‖iteratedFDeriv ℝ j (incrementsOriginalPhaseCovectorCoordinates Data nu i) y‖ ≤
      incrementGivenPhaseSpatialProfile (m+1) d cap covectorBound Spatial j := by
  let O := actualOriginalPhaseOpen Data nu i
  let f := actualOriginalJointPhase Data nu i
  have hO : IsOpen O := actualOriginalPhaseOpen_open Data hd nu i
  have hyO : y ∈ O := actualOriginalPhaseOpen_sample Data hd nu i hy
  have hf : ContDiffAt ℝ ∞ f y :=
    (actualOriginalJointPhase_contDiffOn Data hd hs nu i).contDiffAt (hO.mem_nhds hyO)
  have hBound := increment_given_actual_phase_positive_jets Data hd nu owner xi weight cap covectorBound
    hCap hCovector hWeight hXi hphase hSource Parameter Spatial transition i y hy (j+1) (by omega)
  constructor
  · exact increment_given_derivative_extraction_jets (incrementGivenTotalExtraction (m+1+d)) f y hf j _ hBound
  · have he : incrementsOriginalPhaseCovectorCoordinates Data nu i =ᶠ[𝓝 y]
        incrementGivenSpatialExtraction (m+1) d ∘ fderiv ℝ f := by
      filter_upwards [hO.mem_nhds hyO] with z hz
      exact increment_given_phase_spatial_coordinates Data hd nu owner xi weight hphase i z
        hz.1.1 (hSource _ hz.1.2)
    rw [(he.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact increment_given_derivative_extraction_jets (incrementGivenSpatialExtraction (m+1) d) f y hf j _ hBound

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_given_actual_phase_positive_jets
#print axioms GlobalEmbedding.Continuation.increment_given_actual_phase_gradient_jets
