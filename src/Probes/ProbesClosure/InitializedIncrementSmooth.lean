import NormalPolar.ActualRepairModelFirstDefectStateMap
import Smoothing.Round3RepairClosedState

/-! The full original increment has global joint smoothness because the
produced closed state is its literal sum with the smooth contracted reference.
This recovers smoothness of the same U without manufacturing a new raw slice,
changing its original product samples, or differentiating selected witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- Actual same-U joint smoothness follows from the produced closed state. -/
theorem probes_initialized_increment_smooth
    (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference givenPacket)
    {budget epsilon eta tau : ℝ} {k : ℕ}
    (initial : Round3RepairClosedState packet budget epsilon eta k tau)
    (U : P × M → V) (delta : ℝ)
    (hInitial : initial.map = actualRepairModelFirstDefectFirstMap packet.referenceMap U delta) :
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞ U := by
  have hRef : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,V) ∞
      (fun z => Real.sqrt (1-delta^2) • packet.referenceMap z) :=
    ((contDiff_id : ContDiff ℝ ∞ (fun y : V => y)).const_smul
      (Real.sqrt (1-delta^2))).contMDiff.comp packet.referenceMap_smooth
  have hEq : (fun z => initial.map z-Real.sqrt (1-delta^2) • packet.referenceMap z) = U := by
    funext z
    rw [hInitial]
    simp only [actualRepairModelFirstDefectFirstMap,add_sub_cancel_left]
  simpa only [hEq] using initial.smooth.sub hRef

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_initialized_increment_smooth
