import Smoothing.ParameterRound2UniformMeanReserve
import Smoothing.ParameterRound2MeanRawGermFixedCostIndex
import Smoothing.ParameterRound2MeanRawGermPairEstimatesIndex
import Smoothing.ParameterRound2MeanGermOperatorNorms

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

universe uM uTr uΛ uΒ

variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_actual_raw_uniform_iterate_profiles_index
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho) (B0 : ℕ → ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T TP hT hTP
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∀ (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∀ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    (∀ s, p s H ≤ B0 s) →
    ∀ epsilon, 0 < epsilon →
      epsilon < parameterRound2_uniformMeanThreshold B0 C rho q (q+4) →
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    let K := fun i => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
      (∀ i ≤ q, ∀ s, p s (K i) ≤ parameterRound2_uniformMeanProfile B0 C (q+4) i s) := by
  intro C p F hF g primary hSupply hsm hH epsilon he he0 Top K
  obtain ⟨hsm',hsize,hdiff⟩ := parameterRound2_actual_raw_mean_germ_fixed_cost_estimates_index
    (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
    A B hA hB S W hS hSO ell hell hell1 H rho q Rsub Lprimary hq reserve hc
    Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam F hF g primary hSupply
  exact parameterRound2_uniform_mean_reserve_profile B0 C rho hrho q (q+4)
    p H hH Top hsize epsilon he he0

#print axioms parameterRound2_actual_raw_uniform_iterate_profiles_index
end GlobalEmbedding.Continuation
