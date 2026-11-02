import Smoothing.Round3RepairPrimitiveMeanData

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
local instance round3RepairPrimitiveIncrementChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairPrimitiveIncrementIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)





variable {cost : Round3RepairPrimitiveCosts} {q : ℕ} {ell e delta : ℝ}
  {SF : P × M → EuclideanSpace ℝ (Fin N)} {target : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x)}
namespace Round3RepairPrimitiveMeanData
variable (mean : Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
  (SubSecondary := SubSecondary) packet cost q ell SF target)

def seminorm (ell : ℝ) := parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
  packet.closedSamples_compact (fun _ _ hy => hy.1) ell

theorem meanSmooth : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
    ∀ K : {K : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ //
      seminorm packet ell 0 (K-mean.H) < cost.rho},
    round3ParameterPrimaryMeanError (fun p x => SF (p,x)) mean.slice_smooth mean.g K.val.val (q+2) (epsilon*ell) ∈
      parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ :=
  Classical.choose (mean.input mean.g mean.chart_preserves mean.primary mean.mean_raw)

def operator (mean : Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary) packet cost q ell SF target) := round3ParameterMeanReserveOperator (Λ := Λ) (Β := Β) (m := m) (d := d) (N := N) Data.atlas packet.parameterFamily.chart packet.closedSamples univ
  (seminorm packet ell) mean.H cost.rho ell (fun p x => SF (p,x)) mean.slice_smooth mean.g q (mean.meanSmooth packet)

def iterate (mean : Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary) packet cost q ell SF target) (e : ℝ) := (meanReserveStep (seminorm packet ell 0) mean.H cost.rho (mean.operator packet e))^[q] mean.H

def restrictedPrimary (mean : Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary) packet cost q ell SF target) : Round3ParameterPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β) (fun p x => SF (p,x)) := round3Parameter_restrictPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β) (fun p x => SF (p,x)) mean.g univ isOpen_univ
end Round3RepairPrimitiveMeanData

/-- One actual mean iteration and one fixed secondary choice, all derivative
orders using that same choice.  The raw witnesses occur before U is defined. -/
structure Round3RepairPrimitiveIncrementData (cost : Round3RepairPrimitiveCosts)
    (q : ℕ) (ell e delta : ℝ) (SF : P × M → Ey)
    (target : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x)) where
  mean : Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost q ell SF target
  choice : ActualSecondarySignedRecord Λ → SubSecondary → Round3ParameterSecondaryChoice P M m
  choice_preserves : ∀ r a, Round3ParameterChartPreserves (choice r a).chart
  raw : ∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) Data.atlas packet.parameterFamily.chart
    (fun p x => SF (p,x)) mean.slice_smooth (mean.restrictedPrimary packet)
    (mean.iterate packet e).val (mean.iterate packet e).val
    (j+2*q+8) (j+q+4) j q cost.Rsub cost.Lprimary cost.Rsecondary cost.reserve
    (cost.Bsec j) (cost.Msec j) (cost.Ccut j) (cost.Tsec j) (cost.Tinv j) (cost.Tobs j)
    univ mean.primary packet.closedSamples ell delta (e*ell) 0 choice)

namespace Round3RepairPrimitiveIncrementData
variable (step : Round3RepairPrimitiveIncrementData (Tr := Tr) (Λ := Λ) (Β := Β)
  (SubSecondary := SubSecondary) packet cost q ell e delta SF target)

def increment : P × M → Ey :=
  round3ParameterIncrementMap (fun p x => SF (p,x)) step.mean.slice_smooth
    (step.mean.restrictedPrimary packet) (step.mean.iterate packet e).val (q+2) (e*ell) delta step.choice

/-- Literal Top, Kq, and sine/cosine U, with the genuine global original
norm bounds and metric error supplied by the primitive analytic theorem. -/
theorem conclusion (he : 0 < e) (heTheta : e < cost.Theta)
    (hdelta : 0 ≤ delta) (hdeltaLe : delta ≤ e*ell) :
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      SF (step.increment packet) target q delta (e*ell) ell cost.Cmap cost.Cmetric := by
  have h := (Classical.choose_spec (step.mean.input step.mean.g step.mean.chart_preserves
    step.mean.primary step.mean.mean_raw)) e he heTheta delta hdelta hdeltaLe
    univ isOpen_univ (Subset.refl _) (fun _ _ _ => mem_univ _)
    step.choice step.choice_preserves step.raw
  have hout : Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      SF (step.increment packet) step.mean.H.val q delta (e*ell) ell cost.Cmap cost.Cmetric := h.2
  simpa only [step.mean.target_eq] using hout

end Round3RepairPrimitiveIncrementData
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairPrimitiveIncrementData.conclusion
