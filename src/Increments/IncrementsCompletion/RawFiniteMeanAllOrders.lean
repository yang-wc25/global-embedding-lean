import Probes.Round3ParameterJointConclusion
import IncrementsCompletion.FiniteMetricAddition

/-!
# Actual all-order increment after the finite native mean construction

This final algebraic consumer is independent of the internal proof carrier
used for the mean iteration.  It takes the one actual resulting native tensor
and the actual raw primary/secondary profiles, and proves the full joint
conclusion for the literal finite increment.  Its constants precede parameter
spaces, atlas counts, and refinement index types; one literal secondary choice
and one literal U serve every observation order.

The mean residual input is the result of the finite actual mean construction,
not a replacement for that construction.  The original-data entrance must
manufacture the raw profiles and this residual before calling the theorem.
No sample compactness, substitute norm, or substitute domain is used here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ uSubSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem incrementsCompletion_actual_all_orders_from_finite_mean
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Cmean : ℕ → ℝ) (hCM : ∀ j, 0 ≤ Cmean j)
    (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (hBsec : ∀ j, 0 ≤ Bsec j) (hMsec : ∀ j, 0 ≤ Msec j) (hCcut : ∀ j, 0 ≤ Ccut j)
    (hTsec : ∀ j k, 0 ≤ Tsec j k) (hTinv : ∀ j k, 0 ≤ Tinv j k)
    (hTobs : ∀ j k, 0 ≤ Tobs j k) :
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧ ∀
      (P : Type uP) [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
      [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
      (Λ : Type uΛ) (Β : Type uΒ) (SubSecondary : Type uSubSecondary)
      [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary] (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (G : Set (P × M)) (hG : IsOpen G)
      (coverG : ∀ z ∈ G, ∃ b, z.1 ∈ (B b).source)
      (ell delta tau : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
      (primary : Λ → Set (P × M))
      (K H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (choice : ActualSecondarySignedRecord Λ → SubSecondary → Round3ParameterSecondaryChoice P M m),
      (∀ r a, Round3ParameterChartPreserves (choice r a).chart) →
      (∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) A B F hF g K K
        (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary reserve (Bsec j) (Msec j) (Ccut j)
        (Tsec j) (Tinv j) (Tobs j) G primary S ell delta tau 0 choice)) →
      let meanResidual := fun t x => delta^2 •
        (round3ParameterPrimaryMean F hF g K (q+2) tau t x-H t x)
      meanResidual ∈ parameterRound2_originalTensorGermSpace A B S G →
      (∀ j, paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B meanResidual)
        (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
        (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B meanResidual)
          (incrementsOriginalDifferentiation A B) S).toReal ≤
          Cmean j*delta^2*(tau/ell)^(q+1)) →
      Round3ParameterJointIncrementConclusion A B S G (fun z => F z.1 z.2)
        (round3ParameterIncrementMap F hF g K (q+2) tau delta choice)
        H q delta tau ell Cmap Cmetric := by
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
  intro P _ _ _ Λ Β SubSecondary _ _ _ _ c A B hA hB S hSO G hG coverG
    ell delta tau htau htaul hell1 hd hdt F hF g hg primary K H choice hchoice hraw
    meanResidual hmeanMem hmeanBound
  let data := fun j => Classical.choice (hraw j)
  let U := round3ParameterIncrementMap F hF g K (q+2) tau delta choice
  let Mean := round3ParameterPrimaryMean F hF g K (q+2) tau
  have hu (j : ℕ) := hUB j P Λ Β SubSecondary c A B F hF g hg K K G primary S
    ell delta tau 0 htau htaul hell1 hd hdt choice hchoice (data j)
  have hr (j : ℕ) := hRB j P Λ Β SubSecondary c A B hA F hF g hg K K G primary S
    ell delta tau 0 htau htaul hell1 hd hdt choice hchoice (data j)
  have hmetric (j : ℕ) := incrementsCompletion_original_metric_error_of_finite_remainder_and_mean
    A B S G hSO (fun z => F z.1 z.2) U H Mean j q delta tau ell (CR j) (Cmean j)
    hd hdt htau htaul hell1 (hCR j) (hCM j) (hr j).1 hmeanMem
    (hr j).2.1 (hmeanBound j).1 (hr j).2.2 (hmeanBound j).2
  refine ⟨?_,(hu 0).1,(hmetric 0).1,fun j => (hu j).2.1,fun j => (hu j).2.2,
    fun j => (hmetric j).2⟩
  exact round3Parameter_actual_increment_joint_contMDiffOn (0+2*q+8) (0+q+4) 0 q
    Rsub Lprimary Rsecondary hq (by omega) reserve (Bsec 0) (Msec 0) (Ccut 0)
    hc (hBsec 0) (hMsec 0) (hCcut 0) (Tsec 0) (Tinv 0) (Tobs 0) (hTsec 0) (hTinv 0)
    A B hB F hF g hg K K G hG coverG primary S ell delta tau 0 htau choice hchoice (data 0)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_actual_all_orders_from_finite_mean
