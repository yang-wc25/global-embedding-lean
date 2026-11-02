import Probes.Round3ParameterUniformComposition


/-! # Uniform actual global increment on arbitrary parameter manifolds

The named numerical threshold, displacement profile and metric profile are
chosen before P, every atlas, H, F, scale and actual primitive family. Raw
mean data produce one global Kq. One final physical G and one secondary
choice then produce a single U used at every observation order. Its true
original full-joint norms, (6.8) residual and joint∞ are conclusions. -/

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

theorem round3Parameter_uniform_actual_global_increment
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    let Csize := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let Theta := parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4)
    0 < Theta ∧ Theta ≤ 1 ∧
    Round3ParameterUniformGlobalStatement.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 rho Theta q Rsub Lprimary Rsecondary reserve Bnd Mg Dinput T Bsec Msec Ccut Tsec Tinv Tobs := by
  intro Csize Theta
  obtain ⟨hTheta,hTheta1,Cmean,hCmean,hMean⟩ := round3Parameter_actual_raw_mean_uniform_before_data
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    B0 rho hrho q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg hDinput T hT
  refine ⟨hTheta,hTheta1,?_⟩
  exact round3Parameter_uniform_consumer_from_raw_mean B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc
    Bnd Mg Dinput T Cmean hCmean Theta hTheta1 Bsec Msec Ccut Tsec Tinv Tobs
    hBsec hMsec hCcut hTsec hTinv hTobs hMean

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_uniform_actual_global_increment
