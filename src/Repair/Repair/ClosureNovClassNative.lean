import Repair.ClosureNovClassFactory

/-! The actual weighted datum, including all native phase and positive
reserve certificates, selected from the proved original-map producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology ENNReal BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
private local instance : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

namespace ClosureNovFixedClass.AllowedMap
variable {c : ClosureNovFixedClass m d N M P}


def raw {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalNativeData (m+1) d N M P :=
  repairReferenceOriginalFamilyData c.numerical.referenceBudget (c.geometry.seed F0) h.sliceSmooth
    (fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => F0 (p,y)) x) c.geometry.samples
    c.geometry.parentDomain c.geometry.parentCarrier (fun _ => 0) (h.family)
    (c.seedDomains F0) c.geometry.outer

def positive {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalNativeData (m+1) d N M P :=
  repairReferencePositiveData (h.raw) c.numerical.rawReserve

def label {F0 : P × M → V} (h : c.AllowedMap F0) : Fin (h.positive).primaryCount → ℕ :=
  Classical.choose (h.weighted_exists)

theorem label_lt {F0 : P × M → V} (h : c.AllowedMap F0) (nu : Fin (h.positive).primaryCount) : h.label nu < c.numerical.labelBound :=
  (Classical.choose_spec (h.weighted_exists)).1 nu

theorem label_proper {F0 : P × M → V} (h : c.AllowedMap F0) (nu mu : Fin (h.positive).primaryCount) (hne : nu ≠ mu)
    (hh : (tsupport ((h.raw).cutoff nu) ∩ tsupport ((h.raw).cutoff mu)).Nonempty) :
    h.label nu ≠ h.label mu :=
  (Classical.choose_spec (h.weighted_exists)).2.1 nu mu hne hh

def weight {F0 : P × M → V} (h : c.AllowedMap F0) : Fin (h.positive).primaryCount → ℝ := fun nu =>
  repairReferenceSignedHierarchy c.numerical.referenceBudget.cover c.numerical.referenceBudget.operatorBound c.numerical.transition ^ h.label nu

def data {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalNativeData (m+1) d N M P :=
  repairReferenceWeightedData (h.positive) (h.weight)

theorem native_exists {F0 : P × M → V} (h : c.AllowedMap F0) :
    ∃ (hd : IncrementsOriginalDomainConditions (h.data))
      (hs : IncrementsOriginalSmoothInputs (h.data)),
      IncrementsOriginalPhaseConditions (h.data) hd hs ∧
      IncrementsOriginalFreeNormalConditions (h.data) hd hs ∧
      IncrementsOriginalQualitativeDecompositionInputs (h.data) ∧
      IncrementsOriginalDecompositionReserveInputs (h.data) c.numerical.reserve ∧
      IncrementsOriginalLinearSmoothInputs (h.data) ∧
      (∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport ((h.data).cutoff nu))).card ≤ c.numerical.labelBound) ∧
      RepairOriginalTransitionBudgets (h.data) c.numerical.parameterTransition c.numerical.spatialTransition :=
  (Classical.choose_spec (h.weighted_exists)).2.2

def domain {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalDomainConditions (h.data) := Classical.choose (h.native_exists)
def nativeSmooth {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalSmoothInputs (h.data) :=
  Classical.choose (Classical.choose_spec (h.native_exists))

theorem native_properties {F0 : P × M → V} (h : c.AllowedMap F0) :
      IncrementsOriginalPhaseConditions (h.data) (h.domain) (h.nativeSmooth) ∧
      IncrementsOriginalFreeNormalConditions (h.data) (h.domain) (h.nativeSmooth) ∧
      IncrementsOriginalQualitativeDecompositionInputs (h.data) ∧
      IncrementsOriginalDecompositionReserveInputs (h.data) c.numerical.reserve ∧
      IncrementsOriginalLinearSmoothInputs (h.data) ∧
      (∀ z, (Finset.univ.filter (fun nu => z ∈ tsupport ((h.data).cutoff nu))).card ≤ c.numerical.labelBound) ∧
      RepairOriginalTransitionBudgets (h.data) c.numerical.parameterTransition c.numerical.spatialTransition :=
  Classical.choose_spec (Classical.choose_spec (h.native_exists))

theorem immersion {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalSliceImmersionInputs (h.data) :=
  closureNov_reference_slice_immersion_inputs c.geometry F0 h.sliceSmooth c.lower c.lower_pos
    h.ellipticity (h.data) rfl

theorem ellipticity_inputs {F0 : P × M → V} (h : c.AllowedMap F0) : IncrementsOriginalCoordinateEllipticityInputs (h.data) c.lower :=
  ⟨c.lower_pos,fun p _ i y hy v => h.ellipticity p i y hy v⟩

end ClosureNovFixedClass.AllowedMap
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.native_properties
#print axioms GlobalEmbedding.Continuation.ClosureNovFixedClass.AllowedMap.immersion
