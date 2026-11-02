import Probes.Round3RepairPrimitiveIncrement

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
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
local instance round3RepairStatePrimitiveChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairStatePrimitiveIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)






/-- The primitive input is tied to the actual SF and SH computed from this
state and the literal (6.5) exponents, including the chosen next stage s. -/
abbrev Round3RepairStatePrimitiveInput [CompactSpace M]
    (cost : Round3RepairPrimitiveCosts) {budget epsilon eta : ℝ} {k : ℕ} {t : ℝ}
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) (ht : 0 < t) (ht1 : t ≤ 1) :=
  let current := state.toSmoothingState s hk hks ht ht1
  Round3RepairPrimitiveIncrementData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost (40*(k+1)) (t^(11/10 : ℝ)) (t^(1/10 : ℝ)) (t^k)
    (current.smoothedMap packet) (current.computedTarget packet)

/-- No increment or output estimate is an input: this consumes the primitive
mean/raw witnesses and returns the actual joint conclusion for their U. -/
theorem round3_repair_state_primitive_conclusion [CompactSpace M]
    (cost : Round3RepairPrimitiveCosts) {budget epsilon eta : ℝ} {k : ℕ} {t : ℝ}
    (state : Round3RepairClosedState packet budget epsilon eta k t)
    (s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) (ht : 0 < t) (ht1 : t ≤ 1)
    (primitive : Round3RepairStatePrimitiveInput (Tr := Tr) (Λ := Λ) (Β := Β)
      (SubSecondary := SubSecondary) packet cost state s hk hks ht ht1)
    (hTheta : t < cost.Theta^10) :
    let current := state.toSmoothingState s hk hks ht ht1
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) (primitive.increment packet) (current.computedTarget packet)
      (40*(k+1)) (t^k) (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) cost.Cmap cost.Cmetric := by
  have hScale := actual_repair_fixed_scales_admissible ht ht1 k s hk hks
  have hEntry := (actual_repair_uniform_stage_threshold cost.theta_pos cost.theta_le_one).2.2 t ht hTheta
  have hout := primitive.conclusion packet hEntry.1 hEntry.2.1 hScale.2.2.2.1.le hScale.2.2.2.2.1
  rw [hScale.2.2.1] at hout
  exact hout

namespace Round3RepairClosedState
/-- Transport changes only the index proof, never the actual map. -/
def atEqualScale {budget epsilon eta : ℝ} {k : ℕ} {t t' : ℝ}
    (state : Round3RepairClosedState packet budget epsilon eta k t) (h : t=t') :
    Round3RepairClosedState packet budget epsilon eta k t' := h ▸ state

@[simp] theorem atEqualScale_map {budget epsilon eta : ℝ} {k : ℕ} {t t' : ℝ}
    (state : Round3RepairClosedState packet budget epsilon eta k t) (h : t=t') :
    (state.atEqualScale packet h).map = state.map := by cases h; rfl
end Round3RepairClosedState
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_state_primitive_conclusion
