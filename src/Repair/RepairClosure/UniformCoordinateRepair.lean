import RepairClosure.UniformRepairStatements
import OriginalIntegration.OriginalBufferedCoordinateRepair

/-! Full proof of the explicit coordinate-margin statement.  The native
statement defined next to it is not asserted and is not an assumption. -/

noncomputable section
namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalIntegration
universe uM uP

theorem uniform_coordinate_repair_complete : UniformCoordinateRepairStatement.{uM,uP} := by
  intro m d N M topologyM hausdorffM chartsM smoothM boundaryM auxiliaryNorm continuousNorm
    b R hR lower margin hLower hMargin hDim hAmbient rho hrho
  obtain ⟨J,epsilon,t0,_hJ,h442,he,ht,h1,hOpen⟩ :=
    original_buffered_coordinate_repair.{uM,uP} b R hR lower margin
      hLower hMargin hDim hAmbient rho hrho
  refine ⟨J,epsilon,t0,h442,he,ht,h1,?_⟩
  intro P topologyP hausdorffP compactP chartsP smoothP g F0 core hPhase
  exact hOpen M P g F0 ⟨core.smooth,core.map_bounds,core.ellipticity,hPhase⟩

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.uniform_coordinate_repair_complete
