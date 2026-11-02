import Repair.EntranceCanonicalStageCosts
import Probes.Round4ParameterFiniteGlobalConsumer
import Repair.IncrementCanonicalCostsMeanFinitePhysical
import Probes.Round3ParameterUniformStatements

/-!
# The actual global increment with fully named finite numerical costs

The threshold, displacement and metric constants are fixed before P, any
atlas, the input tensor, maps and scales. Every numerical coefficient is
now named and has an exact finite-prefix congruence theorem. The raw mean
construction supplies the very same Kq and the final-domain construction
supplies one U at every order; its true original joint norms and (6.8)
metric residual remain conclusions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ uSubSecondary
variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem repairEntranceCanonical_uniform_actual_global_increment_named_costs
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let Theta := parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4)
    let Cmean := incrementCanonical_round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (Tr := Tr)
      B0 q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg T hT
    let Cmap := repairEntranceCanonicalStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs
    let Cmetric := repairEntranceCanonicalStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs Cmean
    0 < Theta ∧ Theta ≤ 1 ∧
    Round4ParameterUniformNamedGlobalStatement.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 rho Theta q Rsub Lprimary Rsecondary reserve Bnd Mg Dinput T Bsec Msec Ccut Tsec Tinv Tobs
      Cmap Cmetric := by
  intro Csize Theta Cmean Cmap Cmetric
  obtain ⟨hTheta,hTheta1,hCmean,hMean⟩ := incrementCanonical_round4Parameter_actual_raw_mean_named_residual.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    B0 rho hrho q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg hDinput T hT
  obtain ⟨hCmap,hCmetric,hOutput⟩ := repairEntranceCanonical_all_orders_with_finite_costs.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    rho hrho q Rsub Lprimary Rsecondary hq reserve hc Cmean hCmean Theta hTheta1
    Bsec Msec Ccut Tsec Tinv Tobs hBsec hMsec hCcut hTsec hTinv hTobs
  refine ⟨hTheta,hTheta1,hCmap,hCmetric,?_⟩
  intro P _ _ _ Λ Β SubSecondary _ _ _ _ c A B hA hB S W hW cover hS hSO ell hell hell1 H p hH
    F hF g hg primary hdata
  obtain ⟨hsm,hmean⟩ := hMean P Λ Β c A B hA S W hS hSO ell hell hell1 H hH F hF g hg primary hdata
  exact ⟨hsm,hOutput P Λ Β SubSecondary c A B hA hB S W hW cover hS hSO p ell hell hell1 H
    F hF g hg primary hsm hmean⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_uniform_actual_global_increment_named_costs

