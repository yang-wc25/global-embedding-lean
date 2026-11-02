import Smoothing.Round3OuterStageParameterRestriction
import Smoothing.Round3RepairStageSmoothTarget

/-! Original domain and smooth-input records for the literal computed
SF/SH target. Reference phase, cutoff and reference normal are restricted
to the actual new parameter neighborhood; SF/H regularity comes from the
same smoother. No normal legality for the old normal at SF is inferred. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)

theorem round3_computed_stage_domain
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (U : Set P) (rho : ℝ) (hU : IsOpen U) (hKU : Data.parameterSet ⊆ U)
    (hUO : U ⊆ Data.parameterOpen) :
    IncrementsOriginalDomainConditions (round3OriginalComputedPositiveData Data F H U rho) :=
  { round3_restrict_parameter_domain Data hd U hU hKU hUO with }

theorem round3_computed_stage_original_smooth_inputs
    (Data : IncrementsOriginalNativeData n d N M P)
    (hs : IncrementsOriginalSmoothInputs Data)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (U : Set P) (rho : ℝ) (hUO : U ⊆ Data.parameterOpen)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage (round3OriginalComputedPositiveData Data F H U rho)
      BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket) :
    IncrementsOriginalSmoothInputs (round3OriginalComputedPositiveData Data F H U rho) := by
  let hsU := round3_restrict_parameter_smooth Data hs U hUO
  exact round3_repair_stage_original_smooth_inputs _ BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage
    hsU.phase_joint hsU.cutoff_joint hsU.normal_joint

theorem round3_computed_stage_original_linear
    (Data : IncrementsOriginalNativeData n d N M P)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (U : Set P) (rho : ℝ) (hUO : U ⊆ Data.parameterOpen) :
    IncrementsOriginalLinearSmoothInputs (round3OriginalComputedPositiveData Data F H U rho) :=
  ⟨(round3_restrict_parameter_linear Data hLinear U hUO).linear_coordinates⟩

#print axioms round3_computed_stage_domain
#print axioms round3_computed_stage_original_smooth_inputs
end GlobalEmbedding.Continuation
