import Repair.EntranceOriginalChartProfiles
import Smoothing.Round3OuterParameterFixedReferenceProfiles
import Smoothing.Round3OuterStablePrimaryFamily

/-!
# Numerical original-observer budget of the same selected reference packet

Only original transition jets, fixed coordinate domains and source-sample
membership are new fields.  All native reference jets are those already
proved for the selected whole reference profiles.  The actual original
and fixed-carrier families consume the resulting identical numerical
Forward/Inverse profiles.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

structure RepairPrimaryObserverBudget
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet) where
  parameter : ℕ → ℝ
  spatial : ℕ → ℝ
  parameter_nonneg : ∀ j, 0 ≤ parameter j
  spatial_nonneg : ∀ j, 0 ≤ spatial j
  transition : RepairOriginalTransitionBudgets Ref parameter spatial
  parameterValue : ℝ
  sourceValue : ℝ
  parameterValue_nonneg : 0 ≤ parameterValue
  sourceValue_nonneg : 0 ≤ sourceValue
  parameter_value : ∀ ip p, p ∈ Ref.parameterNormDomain ip → ‖p‖ ≤ parameterValue
  source_value : ∀ i x, x ∈ Ref.sourceNormDomain i → ‖x‖ ≤ sourceValue
  native_source : ∀ nu i a z, z ∈ (profiles.piece nu i a).native.source →
    z.1 ∈ Ref.parameterNormDomain i.2 ∧ z.2 ∈ Ref.sourceNormDomain (profiles.piece nu i a).host

namespace RepairPrimaryObserverBudget
variable {Ref : IncrementsOriginalNativeData (m+1) d N M P}
    {hd : IncrementsOriginalDomainConditions Ref} {hs : IncrementsOriginalSmoothInputs Ref}
    {theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ}
    {packet : Round3ParameterWholePrimaryPieceSupply Ref theta}
    {profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet}
    (budget : RepairPrimaryObserverBudget Ref hd hs theta packet profiles)

def forwardProfile : ℕ → ℝ := repairEntranceOriginalForwardProfile budget.parameterValue
  profiles.Tforward budget.parameter budget.spatial

def inverseProfile : ℕ → ℝ := repairEntranceOriginalInverseProfile budget.parameterValue budget.sourceValue
  profiles.Tinv budget.parameter budget.spatial

theorem forward_nonneg (j : ℕ) : 0 ≤ budget.forwardProfile j := by
  dsimp only [forwardProfile,repairEntranceOriginalForwardProfile]
  split_ifs
  · exact budget.parameterValue_nonneg.trans (le_max_left _ _)
  · exact repairEntranceCompositionProfile_nonneg _ _
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameter_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ profiles.Tforward_nonneg budget.parameter_nonneg))
      budget.spatial_nonneg j

theorem inverse_nonneg (j : ℕ) : 0 ≤ budget.inverseProfile j := by
  dsimp only [inverseProfile,repairEntranceOriginalInverseProfile]
  split_ifs
  · exact budget.parameterValue_nonneg.trans (le_max_left _ _)
  · exact repairEntranceCompositionProfile_nonneg _ _ budget.spatial_nonneg
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameter_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ profiles.Tinv_nonneg budget.parameter_nonneg)) j

theorem original_profiles
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (ForwardOld InverseOld Meta : ℕ → ℝ)
    (hOld : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterWholePrimaryFamily Ref hd hs hn theta
        (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles)) ForwardOld InverseOld Meta) :
    Round3ParameterOriginalChartProfiles Ref
      (round3ParameterWholePrimaryFamily Ref hd hs hn theta
        (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles))
      budget.forwardProfile budget.inverseProfile Meta :=
  repairEntrance_original_all_observer_profiles Ref hd hs hn theta
    (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles)
    profiles.Tforward profiles.Tinv budget.parameter budget.spatial
    profiles.Tforward_nonneg profiles.Tinv_nonneg budget.parameter_nonneg budget.spatial_nonneg
    budget.transition profiles.forward_jets profiles.inverse_jets budget.native_source
    budget.parameterValue budget.sourceValue budget.parameter_value budget.source_value
    ForwardOld InverseOld Meta hOld

end RepairPrimaryObserverBudget

/-- The fixed carrier multiplies each old eta by the same scalar plateau,
so its support is a subset of the old support and its chart functions are
literally unchanged. Its quantitative Forward/Inverse cost is unchanged. -/
theorem repairEntrance_fixed_carrier_inherits_observer_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {A : Type*} [Fintype A]
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Ref.primaryCount) (Β := A) (fun p x => Ref.F (p,x)))
    (hOpen : ∀ nu, IsOpen (round3FixedCarrierDomain (g.eta nu)))
    (Forward Inverse Meta FOld IOld MFixed : ℕ → ℝ)
    (hOriginal : Round3ParameterOriginalChartProfiles Ref g Forward Inverse Meta)
    (hFixed : Round3ParameterOriginalChartProfiles Ref
      (round3ParameterFixedCarrierFamily Ref g hOpen) FOld IOld MFixed) :
    Round3ParameterOriginalChartProfiles Ref
      (round3ParameterFixedCarrierFamily Ref g hOpen) Forward Inverse MFixed := by
  intro ell hell hell1 nu a i gN t etaN k z hz hPhysical
  have hOrigSupport : ((Ref.parameterChart i.2).symm z.1,(Ref.atlas.chart i.1).symm z.2) ∈
      tsupport (g.eta nu a) := tsupport_mul_subset_right hPhysical
  have hOrig := hOriginal ell hell hell1 nu a i k z hz hOrigSupport
  have hFixedPoint := hFixed ell hell hell1 nu a i k z hz hPhysical
  exact ⟨hFixedPoint.1,hFixedPoint.2.1,hOrig.2.2.1,hOrig.2.2.2.1,hFixedPoint.2.2.2.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.RepairPrimaryObserverBudget.original_profiles
#print axioms GlobalEmbedding.Continuation.repairEntrance_fixed_carrier_inherits_observer_profiles
