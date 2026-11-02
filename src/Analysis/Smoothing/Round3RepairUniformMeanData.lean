import Smoothing.Round3RepairPrimitiveMeanData
import Smoothing.Round3RepairClosedTargetData

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
local instance round3RepairUniformDataChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairUniformDataIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- Fixed primitive geometric/jet profiles, before any current map. These
contain no displacement or metric-error output constants. -/
structure Round3RepairPrimitiveProfiles where
  rho : ℝ
  rho_pos : 0 < rho
  reserve : ℝ
  reserve_pos : 0 < reserve
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
  Bnd_nonneg : ∀ j R, 0 ≤ Bnd j R
  Mg_nonneg : ∀ j, 0 ≤ Mg j
  Dinput_nonneg : ∀ j, 0 ≤ Dinput j
  T_nonneg : ∀ j, 0 ≤ T j
  Bsec_nonneg : ∀ j, 0 ≤ Bsec j
  Msec_nonneg : ∀ j, 0 ≤ Msec j
  Ccut_nonneg : ∀ j, 0 ≤ Ccut j
  Tsec_nonneg : ∀ j a, 0 ≤ Tsec j a
  Tinv_nonneg : ∀ j a, 0 ≤ Tinv j a
  Tobs_nonneg : ∀ j a, 0 ≤ Tobs j a

/-- Adjoin only the numerical outputs of the proved uniform increment
 theorem to the fixed primitive profiles. -/
def Round3RepairPrimitiveProfiles.withUniform
    (profile : Round3RepairPrimitiveProfiles) (Theta : ℝ) (hTheta : 0 < Theta) (hTheta1 : Theta ≤ 1)
    (Cmap Cmetric : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j) (hCmetric : ∀ j, 0 ≤ Cmetric j) :
    Round3RepairPrimitiveCosts where
  rho := profile.rho
  reserve := profile.reserve
  Theta := Theta
  theta_pos := hTheta
  theta_le_one := hTheta1
  Rsub := profile.Rsub
  Lprimary := profile.Lprimary
  Rsecondary := profile.Rsecondary
  Bnd := profile.Bnd
  Mg := profile.Mg
  Dinput := profile.Dinput
  T := profile.T
  Bsec := profile.Bsec
  Msec := profile.Msec
  Ccut := profile.Ccut
  Tsec := profile.Tsec
  Tinv := profile.Tinv
  Tobs := profile.Tobs
  Cmap := Cmap
  Cmetric := Cmetric
  map_nonneg := hCmap
  metric_nonneg := hCmetric

/-- All non-raw analytic entrance fields are generated from the actual
same-domain smoother and the original uniform theorem. -/
structure Round3RepairClosedUniformMeanData (cost : Round3RepairPrimitiveCosts)
    {q : ℕ} {budget : ℝ} (state : Round3RepairCurrentSmoothingState packet q budget) where
  slice_smooth : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap packet (p,x))
  H : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ
  target_eq : H.val=state.computedTarget packet
  input : Round3ParameterUniformFixedInput (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    Data.atlas packet.parameterFamily.chart packet.closedSamples univ
    (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell)
    H cost.rho state.ell q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T cost.Theta
    cost.Rsecondary cost.Bsec cost.Msec cost.Ccut cost.Tsec cost.Tinv cost.Tobs cost.Cmap cost.Cmetric
    (fun p x => state.smoothedMap packet (p,x)) slice_smooth

namespace Round3RepairClosedUniformMeanData
variable {cost : Round3RepairPrimitiveCosts} {q : ℕ} {budget : ℝ}
  {state : Round3RepairCurrentSmoothingState packet q budget}

/-- A producer supplies actual raw mean evidence only. The smoother and the
uniform theorem have already supplied H, its regularity and the fixed input. -/
def toMean (data : Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β)
    (SubSecondary := SubSecondary) packet cost state)
    (g : Round3ParameterPrimaryFamily (I := IT) (m := m) (Λ := Λ) (Β := Β)
      (fun p x => state.smoothedMap packet (p,x)))
    (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)) (primary : Λ → Set (P × M))
    (raw : Round3ParameterMeanRawReserveSupply (Tr := Tr) Data.atlas packet.parameterFamily.chart
      packet.closedSamples univ
      (parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
        packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell)
      data.H cost.rho q cost.Rsub cost.Lprimary cost.reserve cost.Bnd cost.Mg cost.Dinput cost.T
      (fun p x => state.smoothedMap packet (p,x)) data.slice_smooth g primary state.ell) :
    Round3RepairPrimitiveMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost q state.ell (state.smoothedMap packet) (state.computedTarget packet) where
  slice_smooth := data.slice_smooth
  H := data.H
  target_eq := data.target_eq
  input := data.input
  g := g
  chart_preserves := hg
  primary := primary
  mean_raw := raw
end Round3RepairClosedUniformMeanData

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairClosedUniformMeanData.toMean
