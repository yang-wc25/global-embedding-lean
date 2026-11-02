import Probes.Round3ParameterUniformStatements


/-! # Uniform actual global increment on arbitrary parameter manifolds

The named numerical threshold, displacement profile and metric profile are
chosen before P, every atlas, H, F, scale and actual primitive family. Raw
mean data produce one global Kq. One final physical G and one secondary
choice then produce a single U used at every observation order. Its true
original full-joint norms, (6.8) residual and joint∞ are conclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

theorem round3Parameter_uniform_consumer_from_raw_mean
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput T : ℕ → ℝ)
    (Cmean : ℕ → ℝ) (hCM : ∀ j, 0 ≤ Cmean j) (Theta : ℝ) (hTheta1 : Theta ≤ 1)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k)
    (hMean : Round3ParameterUniformMeanCore.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 Cmean rho Theta q Rsub Lprimary reserve Bnd Mg Dinput T) :
    Round3ParameterUniformGlobalStatement.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      B0 rho Theta q Rsub Lprimary Rsecondary reserve Bnd Mg Dinput T Bsec Msec Ccut Tsec Tinv Tobs := by
  obtain ⟨Cmap,Cmetric,hCmap,hCmetric,hOutput⟩ := round3Parameter_all_orders_uniform_before_data
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    rho hrho q Rsub Lprimary Rsecondary hq reserve hc Cmean hCM Theta hTheta1
    Bsec Msec Ccut Tsec Tinv Tobs hBsec hMsec hCcut hTsec hTinv hTobs
  refine ⟨Cmap,Cmetric,hCmap,hCmetric,?_⟩
  intro P _ _ _ Λ Β SubSecondary _ _ _ _ c A B hA hB S W hW cover hS hSO ell hell hell1 H p hH
    F hF g hg primary hdata
  obtain ⟨hsm,hmean⟩ := hMean P Λ Β c A B hA S W hS hSO ell hell hell1 H hH F hF g hg primary hdata
  exact ⟨hsm,hOutput P Λ Β SubSecondary c A B hA hB S W hW cover hS hSO p ell hell hell1 H
    F hF g hg primary hsm hmean⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_uniform_consumer_from_raw_mean
