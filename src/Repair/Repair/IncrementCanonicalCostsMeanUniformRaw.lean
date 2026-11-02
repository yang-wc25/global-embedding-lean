import Repair.IncrementCanonicalCostsMeanFinitePhysical
import Smoothing.Round3ParameterMeanUniformThreshold

/-! Actual primitive mean profiles produce a uniform numerical entrance.
Both Theta and Cmean precede P, every original chart, H and its sampling
sets. The only H budget is the original weighted tensor seminorm, which is
supplied by the same actual SF/SH stage in the final caller. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementCanonical_round3Parameter_actual_raw_mean_uniform_before_data
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    let Csize := incrementCanonical_round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let Theta := parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4)
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧ ∀
      (P : Type uP) [TopologicalSpace P] (Λ : Type uΛ) (Β : Type uΒ) [Fintype Λ] [Fintype Β]
      (c : ℕ) (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B S W),
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    (∀ s, p s H ≤ B0 s) → ∀
      (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)) (primary : Λ → Set (P × M)),
    Round3ParameterMeanRawReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
      Round3ParameterActualMeanPhysicalResidual A B S W p H rho ell q Cmean Theta F hF g hsm := by
  intro Csize Theta
  let Cmean := incrementCanonical_round4ParameterMeanResidualCost.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (Tr := Tr)
    B0 q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg T hT
  obtain ⟨hTheta,hTheta1,hCmean,hMean⟩ :=
    incrementCanonical_round4Parameter_actual_raw_mean_named_residual (m := m) (d := d)
      (N := N) (M := M) (Tr := Tr) B0 rho hrho q Rsub Lprimary hq reserve hc
      Bnd Mg Dinput hBnd hMg hDinput T hT
  exact ⟨hTheta,hTheta1,Cmean,hCmean,hMean⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementCanonical_round3Parameter_actual_raw_mean_uniform_before_data
