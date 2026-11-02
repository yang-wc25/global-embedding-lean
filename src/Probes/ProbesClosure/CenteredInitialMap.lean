import NormalPolar.ActualRepairCenteredFamily
import NormalPolar.ActualRepairModelFirstDefectStateMap

/-! Whole spatial slices of the actual first map.  These identities keep the
increment and the centered parameter map opaque, so callers can transport
the full spatial function without unfolding a dependent repair packet. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar

namespace GlobalEmbedding.Continuation

variable {d N : ℕ} {ι M P : Type*} [Fintype ι]
  [TopologicalSpace P]

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Centering the actual first map preserves its literal reference and full
increment on the whole spatial slice. -/
theorem probes_centered_initial_map
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (Fref U initial : P × M → V) (t : ℝ)
    (hInitial : initial = actualRepairModelFirstDefectFirstMap Fref U (t^10))
    (u : Fin d → ℝ) :
    actualRepairCenteredFamily B b p₀ initial u = fun x =>
      Real.sqrt (1-(t^10)^2) • Fref (actualRepairParameterMap B b p₀ u,x) +
        U (actualRepairParameterMap B b p₀ u,x) := by
  rw [hInitial]
  rfl

/-- A passive reference specializes the same identity to the original map;
the supplied increment and centered parameter map remain unchanged. -/
theorem probes_centered_initial_map_of_reference
    (B : TensorBufferedChartFamily ι P Ep) (b : ι) (p₀ : P)
    (Fref U initial : P × M → V) (F₀ : M → V) (t : ℝ)
    (hInitial : initial = actualRepairModelFirstDefectFirstMap Fref U (t^10))
    (hReference : Fref = fun z => F₀ z.2) (u : Fin d → ℝ) :
    actualRepairCenteredFamily B b p₀ initial u = fun x =>
      Real.sqrt (1-(t^10)^2) • F₀ x + U (actualRepairParameterMap B b p₀ u,x) := by
  rw [probes_centered_initial_map B b p₀ Fref U initial t hInitial u, hReference]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.probes_centered_initial_map
#print axioms GlobalEmbedding.Continuation.probes_centered_initial_map_of_reference
