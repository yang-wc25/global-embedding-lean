import Probes.Round3ParameterJointConclusion
import Smoothing.Round3ParameterFinalDomainMean


/-! Necessary local assembly interface for the actual original open-parameter
construction. The original finite parameter atlas need only cover the final
physical G containing the unchanged original samples. The mean germ space
and its original domain W are unchanged. This is an assembly theorem, not a
claim that its actual raw suppliers or original finite-prefix numerics have
been discharged. Its proof is the existing all-order proof with only the
unneeded cover-of-W premise removed. -/

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

theorem auxBridgeNov_all_orders_with_final_domain_cover
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Cmean : ℕ → ℝ) (hCM : ∀ j, 0 ≤ Cmean j) (Theta : ℝ) (hTheta1 : Theta ≤ 1)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k) (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧ ∀
      (P : Type uP) [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (Λ : Type uΛ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary)
      [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary] (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M)) (hW : IsOpen W)
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
      (∀ z ∈ G, ∃ b, z.1 ∈ (B b).source) →
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
  have hU (j : ℕ) := round3Parameter_actual_increment_original_norms_uniform.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
    reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
    (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  choose CU hCU hUB using hU
  have hR (j : ℕ) := round3Parameter_actual_metric_remainder_original_norm_uniform.{uM,uTr,uP,uΛ,uΒ,uSubSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary hq (by omega) (by omega)
    reserve (Bsec j) (Msec j) (Ccut j) hc (hBsec j) (hMsec j) (hCcut j)
    (Tsec j) (Tinv j) (Tobs j) (hTsec j) (hTinv j) (hTobs j)
  choose CR hCR hRB using hR
  refine ⟨CU,fun j => CR j+Cmean j,hCU,fun j => add_nonneg (hCR j) (hCM j),?_⟩
  intro P _ _ _ Λ Β SubSecondary _ _ _ _ c A B hA hB S W hW hS hSO p ell hell hell1 H
    F hF g hg primary hsm hmean epsilon he he0 delta hd hdt Top Kq G hG hGW hSG coverG gG choice hchoice hraw
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
    (Tsec 0) (Tinv 0) (Tobs 0) (hTsec 0) (hTinv 0) A B hB F hF gG hgG Kq.val Kq.val G hG coverG
    primary S ell delta tau 0 htau choice hchoice (data 0)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_all_orders_with_final_domain_cover
