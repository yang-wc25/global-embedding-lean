import Probes.Round3RepairRawEndpoint

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairLimitImmersionChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairLimitImmersionIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)










namespace Round3RepairFullEndpoint
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  {run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial}
  (out : Round3RepairFullEndpoint packet run)

include out in
/-- Exact metric equality of the same physical series gives immersion
throughout an arbitrary parameter manifold, from the prescribed metric's
positivity. No limiting geometry or phase-stability input is required. -/
theorem actual_limit_immersion
    (hPositive : ∀ p x, ∀ v : TangentSpace IT x, v ≠ 0 → 0 < packet.metric p x v v) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∀ p x, Function.Injective (mfderiv IT 𝓘(ℝ,Ey) (fun y => Fstar (p,y)) x) := by
  intro Fstar p x v w hEq
  by_contra hNe
  have hSub : v-w ≠ 0 := sub_ne_zero.mpr hNe
  have hPos := hPositive p x (v-w) hSub
  have hDeriv : mfderiv IT 𝓘(ℝ,Ey) (fun y => Fstar (p,y)) x (v-w)=0 := by
    rw [map_sub,hEq,sub_self]
  have hZero : inducedMetric (I := IT) (fun y => Fstar (p,y)) x (v-w) (v-w)=0 := by
    simp only [inducedMetric_apply,hDeriv,map_zero]
  have hMetric := congrFun (out.limit.2.2.1 p) x
  change inducedMetric (I := IT) (fun y => Fstar (p,y)) x = packet.metric p x at hMetric
  rw [hMetric] at hZero
  exact (ne_of_gt hPos) hZero

include out in
/-- The original immersion interface for the SAME Fstar on all P. -/
theorem actual_limit_original_immersion
    (hPositive : ∀ p x, ∀ v : TangentSpace IT x, v ≠ 0 → 0 < packet.metric p x v v) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    IncrementsOriginalSliceImmersionInputs {Data with F := Fstar, parameterOpen := univ} := by
  intro Fstar
  exact ⟨fun p _ x => out.actual_limit_immersion packet hPositive p x⟩

end Round3RepairFullEndpoint
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairFullEndpoint.actual_limit_immersion
#print axioms GlobalEmbedding.Continuation.Round3RepairFullEndpoint.actual_limit_original_immersion
