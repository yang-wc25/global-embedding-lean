import Probes.Round3RepairRawWitness
import Smoothing.Round3ParameterCanonicalReserveForget

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
local instance round3RepairCanonicalMeanChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairCanonicalMeanIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- Genuine canonical primary raw data on the fixed original Ω/Q domain.
The native observation domain is retained before constructing the solver
or requesting any secondary estimates. -/
structure Round3RepairCanonicalMeanWitness (cost : Round3RepairPrimitiveCosts)
    {q : ℕ} {budget : ℝ} {state : Round3RepairCurrentSmoothingState packet q budget}
    (data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
      (SubSecondary := SubSecondary) packet cost state) where
  g : Round3ParameterPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β)
    (fun p x => state.smoothedMap packet (p,x))
  chart_preserves : ∀ nu a, Round3ParameterChartPreserves (g.chart nu a)
  primary : Λ → Set (P × M)
  canonical : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) Data.atlas packet.parameterFamily.chart
    packet.closedSamples univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell)
    data.H cost.rho q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T
    (fun p x => state.smoothedMap packet (p,x)) data.slice_smooth g primary state.ell

namespace Round3RepairCanonicalMeanWitness
variable {cost : Round3RepairPrimitiveCosts} {q : ℕ} {budget : ℝ}
  {state : Round3RepairCurrentSmoothingState packet q budget}
  {data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost state}

/-- The same g and primary domains define the mean operator. Forgetting the
observer identity loses no estimate, and makes no new choice of a field. -/
def toRawMean (witness : Round3RepairCanonicalMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost data) :
    Round3RepairRawMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary) packet cost data where
  g := witness.g
  chart_preserves := witness.chart_preserves
  primary := witness.primary
  mean_raw := round3Parameter_canonical_reserve_forget Data.atlas packet.parameterFamily.chart packet.closedSamples
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell)
    data.H cost.rho q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T
    (fun p x => state.smoothedMap packet (p,x)) data.slice_smooth witness.g witness.primary state.ell witness.canonical
end Round3RepairCanonicalMeanWitness

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairCanonicalMeanWitness.toRawMean
