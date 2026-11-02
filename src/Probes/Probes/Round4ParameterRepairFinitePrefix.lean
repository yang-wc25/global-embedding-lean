import Probes.Round4ParameterMeanFiniteCost
import Probes.Round4ParameterFiniteCostConsumer
import Smoothing.Round4SpatialPairFiniteConstants

/-!
# A finite prefix for the actual selected repair numbers

This composes the raw smoothing geometry, fixed reference metric budget,
general-parameter mean iteration and actual oscillatory increment costs.
At observation j all selected numerical outputs are unchanged when the
displayed input profiles agree through J = j+(q+1)*(q+4)+2. The scalar
reserve and overlap parameters are held fixed. This is a dependence result
for the actual primitive-profile factory; it does not identify primitive
profiles with a paper-level reference-jet profile.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]

def round4ParameterRepairReferenceProfile
    (n d N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp q : ℕ) (reference : ℕ → ℝ) (budget : ℝ) (j : ℕ) : ℝ :=
  round4SpatialPairConstant n d N radius hradius BS TS BP TP Ds Dp j q*budget+(j+1)*reference j

theorem round4Parameter_repair_numbers_prefix_congr
    (radius : ℝ) (hradius : 0 < radius) (Ds Dp : ℕ)
    (BS TS BP TP BS' TS' BP' TP' reference reference' : ℕ → ℝ) (budget rho : ℝ)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd Bnd' : ℕ → ℝ → ℝ) (Mg Dinput T Mg' Dinput' T' : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hT : ∀ k, 0 ≤ T k)
    (hBnd' : ∀ s R, 0 ≤ Bnd' s R) (hMg' : ∀ s, 0 ≤ Mg' s) (hT' : ∀ k, 0 ≤ T' k)
    (Bsec Msec Ccut Bsec' Msec' Ccut' : ℕ → ℝ)
    (Tsec Tinv Tobs Tsec' Tinv' Tobs' : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k)
    (hBsec' : ∀ j, 0 ≤ Bsec' j) (hMsec' : ∀ j, 0 ≤ Msec' j) (hCcut' : ∀ j, 0 ≤ Ccut' j)
    (hTsec' : ∀ j k, 0 ≤ Tsec' j k) (hTinv' : ∀ j k, 0 ≤ Tinv' j k)
    (hTobs' : ∀ j k, 0 ≤ Tobs' j k) (j : ℕ)
    (hBS : ∀ k, k ≤ j+(q+1)*(q+4)+2 → BS k = BS' k)
    (hTS : ∀ k, k ≤ j+(q+1)*(q+4)+2 → TS k = TS' k)
    (hBP : ∀ k, k ≤ j+(q+1)*(q+4)+2 → BP k = BP' k)
    (hTP : ∀ k, k ≤ j+(q+1)*(q+4)+2 → TP k = TP' k)
    (hRef : ∀ k, k ≤ j+(q+1)*(q+4)+2 → reference k = reference' k)
    (hBeq : ∀ k, k ≤ j+(q+1)*(q+4)+2 → ∀ R, Bnd k R = Bnd' k R)
    (hMeq : ∀ k, k ≤ j+(q+1)*(q+4)+2 → Mg k = Mg' k)
    (hDeq : ∀ k, k ≤ j+(q+1)*(q+4)+2 → Dinput k = Dinput' k)
    (hTeq : ∀ k, k ≤ j+(q+1)*(q+4)+2 → T k = T' k)
    (hBs : Bsec j = Bsec' j) (hMs : Msec j = Msec' j) (hCc : Ccut j = Ccut' j)
    (hTs : ∀ k, k ≤ j+(q+1)*(q+4)+2 → Tsec j k = Tsec' j k)
    (hTi : ∀ k, k ≤ j+(q+1)*(q+4)+2 → Tinv j k = Tinv' j k)
    (hTo : ∀ k, k ≤ j+(q+1)*(q+4)+2 → Tobs j k = Tobs' j k) :
    let B0 := round4ParameterRepairReferenceProfile (m+1) d N radius hradius BS TS BP TP Ds Dp q reference budget
    let B0' := round4ParameterRepairReferenceProfile (m+1) d N radius hradius BS' TS' BP' TP' Ds Dp q reference' budget
    let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let Csize' := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd' Mg' hBnd' hMg' T' hT'
    let Cmean := round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg T hT
    let Cmean' := round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0' q Rsub Lprimary hq reserve hc Bnd' Mg' Dinput' hBnd' hMg' T' hT'
    parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4) =
      parameterRound2_uniformMeanThreshold B0' Csize' rho q (q+4) ∧
    round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs j =
    round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec' Msec' Ccut' Tsec' Tinv' Tobs'
      hBsec' hMsec' hCcut' hTsec' hTinv' hTobs' j ∧
    round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs Cmean j =
    round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec' Msec' Ccut' Tsec' Tinv' Tobs'
      hBsec' hMsec' hCcut' hTsec' hTinv' hTobs' Cmean' j := by
  intro B0 B0' Csize Csize' Cmean Cmean'
  have hB0 (k) (hk : k ≤ j+(q+1)*(q+4)) : B0 k = B0' k := by
    have hPair := round4SpatialPairConstant_congr_prefix (m+1) d N radius hradius Ds Dp k q
      (fun a ha => hBS a (by omega)) (fun a ha => hTS a (by omega))
      (fun a ha => hBP a (by omega)) (fun a ha => hTP a (by omega))
    change _*budget+(k+1)*reference k = _*budget+(k+1)*reference' k
    rw [hPair,hRef k (by omega)]
  have hEntrance : q*(q+4) ≤ j+(q+1)*(q+4) := by
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  have hMean : Cmean j = Cmean' j := round4ParameterMeanResidualCost_prefix_congr
    B0 B0' q Rsub Lprimary hq reserve hc Bnd Bnd' Mg Dinput Mg' Dinput'
    hBnd hMg hBnd' hMg' T T' hT hT' j hB0
    (fun k hk => hBeq k (by omega)) (fun k hk => hMeq k (by omega))
    (fun k hk => hDeq k (by omega)) (fun k hk => hTeq k (by omega))
  constructor
  · exact round4ParameterMeanThreshold_prefix_congr B0 B0' rho q Rsub Lprimary hq reserve hc
      Bnd Bnd' Mg Mg' hBnd hMg hBnd' hMg' T T' hT hT'
      (fun k hk => hB0 k (hk.trans hEntrance))
      (fun k hk => hBeq k (by omega)) (fun k hk => hMeq k (by omega))
      (fun k hk => hTeq k (by omega))
  · have hmul : q+4 ≤ (q+1)*(q+4) := by
      have hh := Nat.mul_le_mul_right (q+4) (Nat.succ_le_succ (Nat.zero_le q))
      simpa only [Nat.zero_add,Nat.one_mul] using hh
    exact round4Parameter_stage_costs_prefix_congr
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs Bsec' Msec' Ccut' Tsec' Tinv' Tobs'
      hBsec' hMsec' hCcut' hTsec' hTinv' hTobs' Cmean Cmean' j hBs hMs hCc
      (fun k hk => hTs k (by omega)) (fun k hk => hTi k (by omega))
      (fun k hk => hTo k (by omega)) hMean

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_repair_numbers_prefix_congr
