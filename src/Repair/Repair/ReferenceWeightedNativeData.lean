import Probes.ActualIncrementOriginalPrimitiveBinding
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs

/-!
# The hierarchy in the original native increment datum

Source: `thm:repair`, uniform phase preparation.  The actual phase is
multiplied by its fixed weight and the actual linear tensor functional is
divided by the square of that same weight.  The map, tensors, cutoff,
normal, open domains and compact parameter set are unchanged.  All claims
below concern the original native data structures.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "𝓙" => 𝓘(ℝ,EuclideanSpace ℝ (Fin n))

def repairReferenceWeightedData (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) : IncrementsOriginalNativeData n d N M P :=
  { Data with
    phase := fun nu z => weight nu • Data.phase nu z
    linearArgument := fun nu p x => (weight nu ^ 2)⁻¹ • Data.linearArgument nu p x }

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem repairReferenceWeightedDomain
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hd : IncrementsOriginalDomainConditions Data) :
    IncrementsOriginalDomainConditions (repairReferenceWeightedData Data weight) :=
  { hd with }

theorem repairReferenceWeightedSmooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hs : IncrementsOriginalSmoothInputs Data) :
    IncrementsOriginalSmoothInputs (repairReferenceWeightedData Data weight) where
  F_joint := hs.F_joint
  H_coordinates := hs.H_coordinates
  phase_joint := fun nu => (weight nu • ContinuousLinearMap.id ℝ ℝ).contDiff.contMDiff.comp_contMDiffOn
    (hs.phase_joint nu)
  cutoff_joint := hs.cutoff_joint
  normal_joint := hs.normal_joint

theorem repair_reference_weighted_covector
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (nu : Fin Data.primaryCount) (z : P × M)
    (hz : z ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) :
    incrementsOriginalPhaseCovector (repairReferenceWeightedData Data weight) nu z.1 z.2 =
      weight nu • incrementsOriginalPhaseCovector Data nu z.1 z.2 := by
  have hpsi := actual_original_phase_mdifferentiableAt Data hd hs nu z.1 z.2 hz
  have hh := const_smul_mfderiv hpsi (weight nu)
  ext v
  exact congrArg (fun L => L v) hh

/-- The same actual normal remains free on the literal weighted kernel.
No new normal is selected when changing the hierarchy. -/
theorem repair_reference_weighted_normal
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hweight : ∀ nu, weight nu ≠ 0)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs) :
    IncrementsOriginalFreeNormalConditions (repairReferenceWeightedData Data weight)
      (repairReferenceWeightedDomain Data weight hd) (repairReferenceWeightedSmooth Data weight hs) where
  unit := hn.unit
  normal := hn.normal
  free := by
    intro nu z hz u v
    have hc := repair_reference_weighted_covector Data weight hd hs nu z hz
    have hker (w : (incrementsOriginalPhaseCovector
        (repairReferenceWeightedData Data weight) nu z.1 z.2).ker) :
        incrementsOriginalPhaseCovector Data nu z.1 z.2 w.val = 0 := by
      have hh := w.property
      change incrementsOriginalPhaseCovector
        (repairReferenceWeightedData Data weight) nu z.1 z.2 w.val = 0 at hh
      have heval := congrArg (fun L : TangentSpace 𝓙 z.2 →L[ℝ] ℝ => L w.val) hc
      have hzero : weight nu * incrementsOriginalPhaseCovector Data nu z.1 z.2 w.val = 0 :=
        heval.symm.trans hh
      exact (mul_eq_zero.mp hzero).resolve_left (hweight nu)
    exact hn.free nu z hz ⟨u.val,hker u⟩ ⟨v.val,hker v⟩

theorem repair_reference_weighted_linear_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (hl : IncrementsOriginalLinearSmoothInputs Data) :
    IncrementsOriginalLinearSmoothInputs (repairReferenceWeightedData Data weight) := by
  constructor
  intro nu i
  have heq : incrementsOriginalLinearArgumentCoordinates
      (repairReferenceWeightedData Data weight) nu i =
      fun y => (weight nu ^ 2)⁻¹ • incrementsOriginalLinearArgumentCoordinates Data nu i y := rfl
  rw [heq]
  exact (hl.linear_coordinates nu i).const_smul _

/-- A common upper bound on the actual weights produces the original
strict square-root reserve, uniformly in the number of phases. -/
theorem repair_reference_weighted_reserve
    (Data : IncrementsOriginalNativeData n d N M P)
    (weight : Fin Data.primaryCount → ℝ) (cap rho : ℝ)
    (hcap : 0 < cap) (hweight : ∀ nu, 0 < weight nu)
    (hweightCap : ∀ nu, weight nu ≤ cap)
    (hr : IncrementsOriginalDecompositionReserveInputs Data rho) :
    IncrementsOriginalDecompositionReserveInputs (repairReferenceWeightedData Data weight)
      (rho/cap^2) := by
  refine ⟨div_pos hr.reserve_pos (sq_pos_of_pos hcap), ?_⟩
  intro nu z hz hp A hA
  have hw2 : 0 < weight nu ^ 2 := sq_pos_of_pos (hweight nu)
  have hc2 : 0 < cap^2 := sq_pos_of_pos hcap
  have harg := hr.lower nu z hz hp A hA
  have harg0 : 0 ≤ Data.linearArgument nu z.1 z.2 A.val := hr.reserve_pos.le.trans harg
  have hsq : weight nu^2 ≤ cap^2 := sq_le_sq₀ (hweight nu).le hcap.le |>.2 (hweightCap nu)
  change rho/cap^2 ≤ (weight nu^2)⁻¹*Data.linearArgument nu z.1 z.2 A.val
  calc
    rho/cap^2 ≤ Data.linearArgument nu z.1 z.2 A.val/cap^2 :=
      div_le_div_of_nonneg_right harg hc2.le
    _ ≤ Data.linearArgument nu z.1 z.2 A.val/(weight nu^2) :=
      div_le_div_of_nonneg_left harg0 hw2 hsq
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_covector
#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_normal
#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_linear_smooth
#print axioms GlobalEmbedding.Continuation.repair_reference_weighted_reserve
