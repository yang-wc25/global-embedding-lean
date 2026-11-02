import Probes.Round3RepairReservedCosts
import Probes.Round3RepairRawWitness
import Smoothing.Round3ParameterMeanUniformRaw

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairMeanEntranceChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairMeanEntranceIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The same canonical Kq enters its original C0 reserve before any
secondary raw evidence is requested. Its proof uses only the actual mean
raw factory and the actual SH budget retained with the named threshold. -/
theorem round3_repair_generated_mean_iterate_reserve
    (profile : Round3RepairPrimitiveProfiles) {q : ℕ} (hq : 1 ≤ q) {budget : ℝ}
    (reserved : Round3RepairReservedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget)
    (state : Round3RepairCurrentSmoothingState packet q budget)
    (witness : Round3RepairRawMeanWitness (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet reserved.generated.cost (reserved.generated.data state))
    (e : ℝ) (he : 0 < e) (heTheta : e < reserved.generated.cost.Theta) :
    let mean := witness.toMean packet
    let p := Round3RepairPrimitiveMeanData.seminorm packet state.ell
    p 0 (mean.iterate packet e-mean.H) ≤ reserved.generated.cost.rho/2 ∧
    p 0 (mean.iterate packet e-mean.H) < reserved.generated.cost.rho := by
  intro mean p
  let generated := reserved.generated
  let cost := generated.cost
  let B0 := fun j => generated.targetCost j*budget+(j+1)*packet.closedReferenceProfile j
  rcases generated.profiles with ⟨hRho,hReserve,hRsub,hLprimary,hRsecondary,hBnd,hMg,hDinput,hT,hRest⟩
  have hrho : 0 < cost.rho := by simpa only [cost,hRho] using profile.rho_pos
  have hc : 0 < cost.reserve := by simpa only [cost,hReserve] using profile.reserve_pos
  have hBndNonneg : ∀ j R, 0 ≤ cost.Bnd j R := by simpa only [cost,hBnd] using profile.Bnd_nonneg
  have hMgNonneg : ∀ j, 0 ≤ cost.Mg j := by simpa only [cost,hMg] using profile.Mg_nonneg
  have hDinputNonneg : ∀ j, 0 ≤ cost.Dinput j := by simpa only [cost,hDinput] using profile.Dinput_nonneg
  have hTNonneg : ∀ j, 0 ≤ cost.T j := by simpa only [cost,hT] using profile.T_nonneg
  let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    q cost.Rsub cost.Lprimary hq cost.reserve hc cost.Bnd cost.Mg hBndNonneg hMgNonneg cost.T hTNonneg
  have hCsize : Csize = round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
        profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg := by
    dsimp only [Csize]
    congr 1 <;> assumption
  have hThreshold : cost.Theta=parameterRound2_uniformMeanThreshold B0 Csize cost.rho q (q+4) := by
    simpa only [cost,B0,hCsize,hRho] using generated.named_threshold
  obtain ⟨hTheta,hTheta1,Cmean,hCmean,hMean⟩ :=
    round3Parameter_actual_raw_mean_uniform_before_data.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 cost.rho hrho q cost.Rsub cost.Lprimary hq cost.reserve hc
      cost.Bnd cost.Mg cost.Dinput hBndNonneg hMgNonneg hDinputNonneg cost.T hTNonneg
  obtain ⟨hsm,hPhysical⟩ := hMean P Λ Β Data.parameterCount Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth packet.closedSamples univ packet.closedSamples_compact (fun _ _ hy => hy.1)
    state.ell state.ell_pos (state.ell_le_t.trans state.t_le_one) mean.H
    (reserved.target_budget state) (fun p x => state.smoothedMap packet (p,x)) mean.slice_smooth
    mean.g mean.chart_preserves mean.primary mean.mean_raw
  have heNamed : e < parameterRound2_uniformMeanThreshold B0 Csize cost.rho q (q+4) := by
    rw [← hThreshold]
    exact heTheta
  have hBound := (hPhysical e he heNamed).1 q (le_refl q)
  have hBound' : p 0 (mean.iterate packet e-mean.H) ≤ cost.rho/2 := hBound
  exact ⟨hBound',hBound'.trans_lt (by linarith)⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_generated_mean_iterate_reserve
