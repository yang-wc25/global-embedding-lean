import Probes.Round3RepairClosedNumericalEntry
import Probes.Round3ParameterUniformFixedInput
import Probes.ActualRepairUniformThreshold

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
local instance round3RepairPrimitiveMeanChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairPrimitiveMeanIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- Numerical data fixed before a current map, its smoothing scale, and the
actual mean/secondary witnesses.  There is one profile for every order. -/
structure Round3RepairPrimitiveCosts where
  rho : ℝ
  reserve : ℝ
  Theta : ℝ
  theta_pos : 0 < Theta
  theta_le_one : Theta ≤ 1
  Rsub : ℕ
  Lprimary : ℕ
  Rsecondary : ℕ
  Bnd : ℕ → ℝ → ℝ
  Mg : ℕ → ℝ
  Dinput : ℕ → ℝ
  T : ℕ → ℝ
  Bsec : ℕ → ℝ
  Msec : ℕ → ℝ
  Ccut : ℕ → ℝ
  Tsec : ℕ → ℕ → ℝ
  Tinv : ℕ → ℕ → ℝ
  Tobs : ℕ → ℕ → ℝ
  Cmap : ℕ → ℝ
  Cmetric : ℕ → ℝ
  map_nonneg : ∀ j, 0 ≤ Cmap j
  metric_nonneg : ∀ j, 0 ≤ Cmetric j

/-- Actual primitive mean data for the literal supplied SF and SH target.
The two fields carrying analysis are the uniform theorem and its primitive
raw mean reserve witnesses, never a final U, displacement bound or error. -/
structure Round3RepairPrimitiveMeanData (cost : Round3RepairPrimitiveCosts)
    (q : ℕ) (ell : ℝ) (SF : P × M → Ey)
    (target : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x)) where
  slice_smooth : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => SF (p,x))
  H : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ
  target_eq : H.val = target
  input : Round3ParameterUniformFixedInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    Data.atlas packet.parameterFamily.chart packet.closedSamples univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) ell)
    H cost.rho ell q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T cost.Theta
    cost.Rsecondary cost.Bsec cost.Msec cost.Ccut cost.Tsec cost.Tinv cost.Tobs cost.Cmap cost.Cmetric
    (fun p x => SF (p,x)) slice_smooth
  g : Round3ParameterPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β) (fun p x => SF (p,x))
  chart_preserves : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)
  primary : Λ → Set (P × M)
  mean_raw : Round3ParameterMeanRawReserveSupply (Tr := Tr) Data.atlas packet.parameterFamily.chart
    packet.closedSamples univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) ell)
    H cost.rho q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T
    (fun p x => SF (p,x)) slice_smooth g primary ell

end GlobalEmbedding.Continuation
