import Smoothing.Round3RepairNormalStage
import Smoothing.ParameterRound2OriginalFiniteReserveGerm
import GlobalEmbedding.Paper.IncrementsOriginalImmersionInputs

/-! Restrict the literal smoothing stage to the actual common stable
parameter neighborhood. The map, tensor, smoothing scale, original samples
and fixed packet are unchanged. Relative support is restricted genuinely;
no stability off the produced neighborhood is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

def round3RestrictParameterData (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) : IncrementsOriginalNativeData n d N M P :=
  { Data with parameterOpen := V }

theorem round3_restrict_parameter_region
    (Data : IncrementsOriginalNativeData n d N M P) (V : Set P)
    (hV : V ⊆ Data.parameterOpen) :
    incrementsOriginalParameterRegion (round3RestrictParameterData Data V) ⊆
      incrementsOriginalParameterRegion Data := fun _ hz => ⟨hV hz.1,hz.2⟩

theorem round3_restrict_parameter_relative_support
    (Data : IncrementsOriginalNativeData n d N M P) (V : Set P)
    (hOld : IsOpen Data.parameterOpen) (hNew : IsOpen V) (hV : V ⊆ Data.parameterOpen)
    (nu : Fin Data.primaryCount) :
    incrementsOriginalRelativeCutoffSupport (round3RestrictParameterData Data V) nu ⊆
      incrementsOriginalRelativeCutoffSupport Data nu := by
  rw [parameterRound2_original_relativeSupport_eq _ hNew,
    parameterRound2_original_relativeSupport_eq _ hOld]
  exact fun _ hz => ⟨round3_restrict_parameter_region Data V hV hz.1,hz.2⟩

theorem round3_restrict_parameter_fixed_packet
    (Data : IncrementsOriginalNativeData n d N M P) (V : Set P) (j : ℕ) (ell : ℝ) :
    parameterRound2_originalFixedPacketProfile (round3RestrictParameterData Data V) j ell =
      parameterRound2_originalFixedPacketProfile Data j ell := rfl

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem round3_restrict_parameter_domain
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalDomainConditions (round3RestrictParameterData Data V) :=
  { hd with
    parameter_open := hV
    parameter_subset := hKV
    cutoff_support_local := fun nu => (round3_restrict_parameter_relative_support
      Data V hd.parameter_open hV hVO nu).trans (hd.cutoff_support_local nu) }

theorem round3_restrict_parameter_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (hs : IncrementsOriginalSmoothInputs Data) (V : Set P) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalSmoothInputs (round3RestrictParameterData Data V) := by
  have hRegion := round3_restrict_parameter_region Data V hVO
  exact ⟨hs.F_joint.mono hRegion,
    fun i => (hs.H_coordinates i).mono (fun _ hz => ⟨hz.1,hRegion hz.2⟩),
    fun nu => (hs.phase_joint nu).mono (fun _ hz => ⟨hz.1,hRegion hz.2⟩),
    fun nu => (hs.cutoff_joint nu).mono (fun _ hz => ⟨hz.1,hRegion hz.2⟩),
    fun nu => (hs.normal_joint nu).mono (fun _ hz => ⟨hz.1,hRegion hz.2⟩)⟩

theorem round3_restrict_parameter_linear
    (Data : IncrementsOriginalNativeData n d N M P)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data) (V : Set P) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalLinearSmoothInputs (round3RestrictParameterData Data V) :=
  ⟨fun nu i => (hLinear.linear_coordinates nu i).mono
    (fun _ hz => ⟨hz.1,round3_restrict_parameter_region Data V hVO hz.2⟩)⟩

theorem round3_restrict_parameter_normal
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalFreeNormalConditions (round3RestrictParameterData Data V)
      (round3_restrict_parameter_domain Data hd V hV hKV hVO)
      (round3_restrict_parameter_smooth Data hs V hVO) := by
  have hRegion := round3_restrict_parameter_region Data V hVO
  exact ⟨fun nu z hz => hn.unit nu z ⟨hz.1,hRegion hz.2⟩,
    fun nu z hz => hn.normal nu z ⟨hz.1,hRegion hz.2⟩,
    fun nu z hz u v => hn.free nu z ⟨hz.1,hRegion hz.2⟩ u v⟩

theorem round3_restrict_parameter_phase
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (V : Set P) (hV : IsOpen V) (hKV : Data.parameterSet ⊆ V) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalPhaseConditions (round3RestrictParameterData Data V)
      (round3_restrict_parameter_domain Data hd V hV hKV hVO)
      (round3_restrict_parameter_smooth Data hs V hVO) := by
  have hRegion := round3_restrict_parameter_region Data V hVO
  have hRel := round3_restrict_parameter_relative_support Data V hd.parameter_open hV hVO
  exact ⟨fun nu z hz => hp.primary_good nu z ⟨hz.1,hRegion hz.2⟩,
    fun nu z hz => hp.doubled_good nu z ⟨hz.1,hRegion hz.2⟩,
    fun nu mu hne sign z hz => hp.interaction_good nu mu hne sign z ⟨hRel nu hz.1,hRel mu hz.2⟩⟩

theorem round3_restrict_parameter_immersion
    (Data : IncrementsOriginalNativeData n d N M P)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) (V : Set P) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalSliceImmersionInputs (round3RestrictParameterData Data V) :=
  ⟨fun p hp x => hImm.immersion p (hVO hp) x⟩

theorem round3_restrict_parameter_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (V : Set P) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalQualitativeDecompositionInputs (round3RestrictParameterData Data V) :=
  { fiber_open := fun p hp x => hDecomp.fiber_open p (hVO hp) x
    H_symmetric := fun p hp x => hDecomp.H_symmetric p (hVO hp) x
    reference_symmetric := fun p hp x => hDecomp.reference_symmetric p (hVO hp) x
    H_mem := fun p hp x => hDecomp.H_mem p (hVO hp) x
    reference_mem := fun p hp x => hDecomp.reference_mem p (hVO hp) x
    decomposition := fun p hp x A hA => hDecomp.decomposition p (hVO hp) x A hA
    argument_positive := fun p hp x nu hchi A hA => hDecomp.argument_positive p (hVO hp) x nu hchi A hA }

theorem round3_restrict_parameter_reserve
    (Data : IncrementsOriginalNativeData n d N M P) (rho : ℝ)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (V : Set P) (hOld : IsOpen Data.parameterOpen) (hV : IsOpen V) (hVO : V ⊆ Data.parameterOpen) :
    IncrementsOriginalDecompositionReserveInputs (round3RestrictParameterData Data V) rho :=
  ⟨hReserve.reserve_pos,fun nu z hz hp A hA => hReserve.lower nu z
    (round3_restrict_parameter_relative_support Data V hOld hV hVO nu hz) hp A hA⟩

namespace Round3RepairOriginalSmoothingStage
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {r : ℕ} {budget : ℝ} {reference givenPacket : ℕ → ℝ}

def restrictParameter
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket)
    (V : Set P) :
    Round3RepairOriginalSmoothingStage (round3RestrictParameterData Data V)
      BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket := { stage with }

end Round3RepairOriginalSmoothingStage
#print axioms Round3RepairOriginalSmoothingStage.restrictParameter
#print axioms round3_restrict_parameter_domain
#print axioms round3_restrict_parameter_phase
#print axioms round3_restrict_parameter_decomposition
end GlobalEmbedding.Continuation
