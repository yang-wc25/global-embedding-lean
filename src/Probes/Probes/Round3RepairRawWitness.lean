import Probes.Round3RepairUniformCostFactory
import Probes.Round3RepairPrimitiveIncrement

/-! A genuine next state from the literal same SF, SH and global U.
Both stay and advance are covered.  The old and new states use exactly one
fixed Ω/Q domain; all higher-order recurrences survive in the result. -/
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
local instance round3RepairRawWitnessChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairRawWitnessIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- Only actual primary functions and primitive raw mean witnesses remain
after the literal smoother and uniform theorem have supplied their data. -/
structure Round3RepairRawMeanWitness (cost : Round3RepairPrimitiveCosts)
    {q : ℕ} {budget : ℝ} {state : Round3RepairCurrentSmoothingState packet q budget}
    (data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
      (SubSecondary := SubSecondary) packet cost state) where
  g : Round3ParameterPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β)
    (fun p x => state.smoothedMap packet (p,x))
  chart_preserves : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)
  primary : Λ → Set (P × M)
  mean_raw : Round3ParameterMeanRawReserveSupply (Tr := Tr) Data.atlas packet.parameterFamily.chart
    packet.closedSamples univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell)
    data.H cost.rho q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T
    (fun p x => state.smoothedMap packet (p,x)) data.slice_smooth g primary state.ell

namespace Round3RepairRawMeanWitness
variable {cost : Round3RepairPrimitiveCosts} {q : ℕ} {budget : ℝ}
  {state : Round3RepairCurrentSmoothingState packet q budget}
  {data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost state}
def toMean (witness : Round3RepairRawMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost data) :
    Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost q state.ell (state.smoothedMap packet) (state.computedTarget packet) :=
  data.toMean packet witness.g witness.chart_preserves witness.primary witness.mean_raw
end Round3RepairRawMeanWitness

/-- Primitive mean and one coherent secondary family for all orders. The
map/tensor/germ/smoothing/threshold conclusions are not fields. -/
structure Round3RepairRawIncrementWitness (cost : Round3RepairPrimitiveCosts)
    {q : ℕ} {budget : ℝ} {state : Round3RepairCurrentSmoothingState packet q budget}
    (data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
      (SubSecondary := SubSecondary) packet cost state) (e delta : ℝ) where
  mean : Round3RepairRawMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary) packet cost data
  choice : ActualSecondarySignedRecord Λ → SubSecondary → Round3ParameterSecondaryChoice P M m
  choice_preserves : ∀ r a, Round3ParameterChartPreserves (choice r a).chart
  raw : ∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) Data.atlas packet.parameterFamily.chart
    (fun p x => state.smoothedMap packet (p,x)) data.slice_smooth ((mean.toMean packet).restrictedPrimary packet)
    ((mean.toMean packet).iterate packet e).val ((mean.toMean packet).iterate packet e).val
    (j+2*q+8) (j+q+4) j q cost.Rsub cost.Lprimary cost.Rsecondary cost.reserve
    (cost.Bsec j) (cost.Msec j) (cost.Ccut j) (cost.Tsec j) (cost.Tinv j) (cost.Tobs j)
    univ mean.primary packet.closedSamples state.ell delta (e*state.ell) 0 choice)

namespace Round3RepairRawIncrementWitness
variable {cost : Round3RepairPrimitiveCosts} {q : ℕ} {budget : ℝ}
  {state : Round3RepairCurrentSmoothingState packet q budget}
  {data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost state} {e delta : ℝ}

def toPrimitive (witness : Round3RepairRawIncrementWitness (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost data e delta) :
    Round3RepairPrimitiveIncrementData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost q state.ell e delta (state.smoothedMap packet) (state.computedTarget packet) where
  mean := witness.mean.toMean packet
  choice := witness.choice
  choice_preserves := witness.choice_preserves
  raw := witness.raw
end Round3RepairRawIncrementWitness

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairRawIncrementWitness.toPrimitive
