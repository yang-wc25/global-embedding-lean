import NormalPolar.PassiveRescaledData
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import GlobalEmbedding.Paper.IncrementsOriginalDecompositionInputs

/-! The original positive tensor decomposition is independent of ambient
reference contraction. Its given H, original linear functionals, tensor
neighborhoods and numerical reserve retain their exact values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

theorem passiveRescaledData_decomposition (Data : IncrementsOriginalNativeData n d N M P)
    (h : IncrementsOriginalQualitativeDecompositionInputs Data) (c : ℝ) :
    IncrementsOriginalQualitativeDecompositionInputs (passiveRescaledData Data c) := by
  cases h
  constructor <;> assumption

theorem passiveRescaledData_reserve (Data : IncrementsOriginalNativeData n d N M P)
    (rho : ℝ) (h : IncrementsOriginalDecompositionReserveInputs Data rho) (c : ℝ) :
    IncrementsOriginalDecompositionReserveInputs (passiveRescaledData Data c) rho := by
  cases h
  constructor <;> assumption

theorem passiveRescaledData_linear (Data : IncrementsOriginalNativeData n d N M P)
    (h : IncrementsOriginalLinearSmoothInputs Data) (c : ℝ) :
    IncrementsOriginalLinearSmoothInputs (passiveRescaledData Data c) :=
  ⟨h.linear_coordinates⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_decomposition
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_reserve
#print axioms GlobalEmbedding.Continuation.passiveRescaledData_linear
