import Probes.Round4ParameterFiniteCosts
import Probes.Round3ParameterJointConclusion
import Smoothing.Round3ParameterFinalDomainMean


/-!
# Actual all-order general-parameter increment with finite selected costs

The same Kq, final physical domain, primary family and secondary choice
produce the same U at every order. The numerical displacement and metric
constants are now explicit names with proved finite transition dependence.
No additional geometric premise and no output estimate is introduced.
-/

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

def round4ParameterStageMapCost
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) (j : ℕ) : ℝ :=
  round4ParameterRawMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)

def round4ParameterStageMetricCost
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) (Cmean : ℕ → ℝ) (j : ℕ) : ℝ :=
  round4ParameterRawMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j) + Cmean j

theorem round4Parameter_all_orders_with_finite_costs
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Cmean : ℕ → ℝ) (hCM : ∀ j, 0 ≤ Cmean j) (Theta : ℝ) (hTheta1 : Theta ≤ 1)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    let Cmap := round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs
    let Cmetric := round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs Cmean
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧ ∀
      (P : Type uP) [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (Λ : Type uΛ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary)
      [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary] (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M)) (hW : IsOpen W)
      (cover : ∀ z ∈ W, ∃ b, z.1 ∈ (B b).source)
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B S W)
      (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)) (primary : Λ → Set (P × M))
      (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
        ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
        round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
          parameterRound2_originalTensorGermSpace A B S W),
      Round3ParameterActualMeanPhysicalResidual A B S W p H rho ell q Cmean Theta F hF g hsm →
      ∀ epsilon, 0 < epsilon → epsilon < Theta → ∀ delta, 0 ≤ delta → delta ≤ epsilon*ell →
      let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
      let Kq := (meanReserveStep (p 0) H rho (Top epsilon))^[q] H
      ∀ (G : Set (P × M)) (hG : IsOpen G), G ⊆ W →
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) →
      let gG := round3Parameter_restrictPrimaryFamily F g G hG
      ∀ (choice : ActualSecondarySignedRecord Λ → SubSecondary → Round3ParameterSecondaryChoice P M m),
      (∀ r a, Round3ParameterChartPreserves (choice r a).chart) →
      (∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) A B F hF gG Kq.val Kq.val
        (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary reserve (Bsec j) (Msec j) (Ccut j)
        (Tsec j) (Tinv j) (Tobs j) G primary S ell delta (epsilon*ell) 0 choice)) →
      p 0 (Kq-H) ≤ rho/2 ∧
      Round3ParameterJointIncrementConclusion A B S G (fun z => F z.1 z.2)
        (round3ParameterIncrementMap F hF gG Kq.val (q+2) (epsilon*ell) delta choice)
        H.val q delta (epsilon*ell) ell Cmap Cmetric := by
  intro Cmap Cmetric
  let CU := Cmap
  let CR (j : ℕ) := round4ParameterRawMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  have hCU (j : ℕ) : 0 ≤ CU j := round4ParameterRawMapCost_nonneg
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  have hCR (j : ℕ) : 0 ≤ CR j := round4ParameterRawMetricCost_nonneg
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  have hUB (j : ℕ) := round4ParameterRawMapCost_bound.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  have hRB (j : ℕ) := round4ParameterRawMetricCost_bound.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
      reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
      (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  refine ⟨hCU,fun j => add_nonneg (hCR j) (hCM j),?_⟩
  intro P _ _ _ Λ Β SubSecondary _ _ _ _ c A B hA hB S W hW cover hS hSO p ell hell hell1 H
    F hF g hg primary hsm hmean epsilon he he0 delta hd hdt Top Kq G hG hGW hSG gG choice hchoice hraw
  have hgG : ∀ ν β, Round3ParameterChartPreserves (gG.chart ν β) := by
    intro ν β z hz
    exact hg ν β z hz.1
  let data := fun j => Classical.choice (hraw j)
  let tau := epsilon*ell
  have htau : 0 < tau := mul_pos he hell
  have htaul : tau ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (he0.le.trans hTheta1) hell.le
  let U := round3ParameterIncrementMap F hF gG Kq.val (q+2) tau delta choice
  let Mean := round3ParameterPrimaryMean F hF gG Kq.val (q+2) tau
  have hu (j : ℕ) := hUB j P Λ Β SubSecondary c A B F hF gG hgG Kq.val Kq.val G primary S
    ell delta tau 0 htau htaul hell1 hd hdt choice hchoice (data j)
  have hr (j : ℕ) := hRB j P Λ Β SubSecondary c A B hA F hF gG hgG Kq.val Kq.val G primary S
    ell delta tau 0 htau htaul hell1 hd hdt choice hchoice (data j)
  have hMeanG := round3Parameter_same_mean_residual_on_final_domain A B S W hSO p H rho ell hrho q
    Cmean Theta hTheta1 F hF g hsm hmean epsilon delta he he0 G hG hGW hSG
  have hmeanMem : (fun t x => delta^2 • (Mean t x-H.val t x)) ∈
      parameterRound2_originalTensorGermSpace A B S G := hMeanG.1
  have hmeanBound (j : ℕ) : (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B
      (fun t x => delta^2 • (Mean t x-H.val t x))) (incrementsOriginalDifferentiation A B) S).toReal ≤
      Cmean j*delta^2*(tau/ell)^(q+1) := by
    have hh := (hMeanG.2 j).2
    have heq : tau/ell = epsilon := mul_div_cancel_right₀ epsilon hell.ne'
    exact hh.trans_eq (by rw [heq]; ring)
  have hmetric (j : ℕ) := round3Parameter_original_metric_error_norm_from_germ_remainder_and_mean
    A B S G hS hSO (fun z => F z.1 z.2) U H.val Mean j q delta tau ell (CR j) (Cmean j)
    hd hdt htau htaul hell1 (hCR j) (hCM j) (hr j).1 hmeanMem (hr j).2.2 (hmeanBound j)
  refine ⟨(hmean epsilon he he0).1 q le_rfl,?_⟩
  refine ⟨?_,(hu 0).1,(hmetric 0).1,fun j => (hu j).2.1,fun j => (hu j).2.2,
    fun j => (hmetric j).2⟩
  exact round3Parameter_actual_increment_joint_contMDiffOn (0+2*q+8) (0+q+4) 0 q Rsub Lprimary Rsecondary hq
    (by omega) reserve (Bsec 0) (Msec 0) (Ccut 0) hc (hBsec 0) (hMsec 0) (hCcut 0)
    (Tsec 0) (Tinv 0) (Tobs 0) (hTsec 0) (hTinv 0) A B hB F hF gG hgG Kq.val Kq.val G hG (fun z hz => cover z (hGW hz))
    primary S ell delta tau 0 htau choice hchoice (data 0)

/-- For observation j, the actual chosen map and residual costs only read
Tsec/Tinv through j+q+5 and Tobs through j+2. The scalar budgets at other
observation orders do not enter. -/
theorem round4Parameter_stage_costs_prefix_congr
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k)
    (Bsec' Msec' Ccut' : ℕ → ℝ) (Tsec' Tinv' Tobs' : ℕ → ℕ → ℝ)
    (hBsec' : ∀ j, 0 ≤ Bsec' j) (hMsec' : ∀ j, 0 ≤ Msec' j) (hCcut' : ∀ j, 0 ≤ Ccut' j)
    (hTsec' : ∀ j k, 0 ≤ Tsec' j k) (hTinv' : ∀ j k, 0 ≤ Tinv' j k)
    (hTobs' : ∀ j k, 0 ≤ Tobs' j k)
    (Cmean Cmean' : ℕ → ℝ) (j : ℕ)
    (hB : Bsec j = Bsec' j) (hM : Msec j = Msec' j) (hC : Ccut j = Ccut' j)
    (hT : ∀ k, k ≤ j+q+5 → Tsec j k = Tsec' j k)
    (hI : ∀ k, k ≤ j+q+5 → Tinv j k = Tinv' j k)
    (hO : ∀ k, k ≤ j+2 → Tobs j k = Tobs' j k)
    (hMean : Cmean j = Cmean' j) :
    round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs j =
    round4ParameterStageMapCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec' Msec' Ccut' Tsec' Tinv' Tobs'
      hBsec' hMsec' hCcut' hTsec' hTinv' hTobs' j ∧
    round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec Msec Ccut Tsec Tinv Tobs
      hBsec hMsec hCcut hTsec hTinv hTobs Cmean j =
    round4ParameterStageMetricCost.{uM,uTr,uP,uΛ,uΒ,uSubSecondary} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary Rsecondary hq reserve hc Bsec' Msec' Ccut' Tsec' Tinv' Tobs'
      hBsec' hMsec' hCcut' hTsec' hTinv' hTobs' Cmean' j := by
  have ht := parameterRound2_numericProfilePrefix_congr (j+q+4+1) (Tsec j) (Tsec' j)
    (fun k hk => hT k (by omega))
  have hi := parameterRound2_numericProfilePrefix_congr (j+q+4+1) (Tinv j) (Tinv' j)
    (fun k hk => hI k (by omega))
  have ho := parameterRound2_numericProfilePrefix_congr (j+2) (Tobs j) (Tobs' j) hO
  constructor
  · unfold round4ParameterStageMapCost round4ParameterRawMapCost
    congr 1
    rw [hB,hM,hC,ht,hi,ho]
  · unfold round4ParameterStageMetricCost round4ParameterRawMetricCost
    rw [hMean]
    congr 2
    rw [hB,hM,hC,ht,hi,ho]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_all_orders_with_finite_costs
#print axioms GlobalEmbedding.Continuation.round4Parameter_stage_costs_prefix_congr
