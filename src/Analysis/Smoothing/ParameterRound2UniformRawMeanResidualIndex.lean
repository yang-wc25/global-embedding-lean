import Smoothing.ParameterRound2MeanRawGermFixedCostIndex
import Smoothing.ParameterRound2UniformMeanPhysicalIndex

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
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

/-! The actual raw mean residual with all constants chosen before the atlas,
input tensor, sampling sets and smoothing scale. The only added supplier is
an upper numerical profile B0 for the SAME H in the original seminorm. -/
/-- The SAME raw mean residual at its explicit finite-prefix threshold.
Only Cmean is chosen existentially; epsilon is the named numerical function. -/
theorem parameterRound2_actual_raw_germ_mean_q_residual_named_threshold_index
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
      hc (hBnd s R) (hMg s) T TP hT hTP
    let epsilon0 := parameterRound2_uniformMeanThreshold B0 C rho q (q+4)
    0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧ ∀ {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β] {c : ℕ}
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W),
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    (∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) → ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ParameterRound2ActualGermMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm := by
  intro C epsilon0
  obtain ⟨he0,he01,Cmean,hCmean,hphysical⟩ :=
    parameterRound2_actual_germ_mean_physical_named_threshold_index.{uM,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M)
      B0 C (fun s R => C s R*Dinput s) rho hrho q
  refine ⟨he0,he01,Cmean,hCmean,?_⟩
  intro Λ Β _ _ c A B hA hB S W hS hSO ell hell hell1 H p hH hParam F hF g primary hdata
  obtain ⟨hsm,hsize,hdiff⟩ := parameterRound2_actual_raw_mean_germ_fixed_cost_estimates_index
    (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
    A B hA hB S W hS hSO ell hell hell1 H rho q Rsub Lprimary hq
    reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam F hF g primary hdata
  exact ⟨hsm,hphysical A B S W hS hSO ell hell H hH F hF g hsm hsize hdiff⟩


theorem parameterRound2_actual_raw_germ_mean_q_residual_uniform_before_input_index
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀ {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β] {c : ℕ}
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W),
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    (∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) → ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ParameterRound2ActualGermMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm := by
  let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T TP hT hTP
  obtain ⟨Cmean,hCmean,epsilon0,he0,he01,hphysical⟩ :=
    parameterRound2_actual_germ_mean_physical_uniform_before_input_index.{uM,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M)
      B0 C (fun s R => C s R*Dinput s) rho hrho q
  refine ⟨Cmean,hCmean,epsilon0,he0,he01,?_⟩
  intro Λ Β _ _ c A B hA hB S W hS hSO ell hell hell1 H p hH hParam F hF g primary hdata
  obtain ⟨hsm,hsize,hdiff⟩ := parameterRound2_actual_raw_mean_germ_fixed_cost_estimates_index
    (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
    A B hA hB S W hS hSO ell hell hell1 H rho q Rsub Lprimary hq
    reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam F hF g primary hdata
  exact ⟨hsm,hphysical A B S W hS hSO ell hell H hH F hF g hsm hsize hdiff⟩

#print axioms parameterRound2_actual_raw_germ_mean_q_residual_named_threshold_index
#print axioms parameterRound2_actual_raw_germ_mean_q_residual_uniform_before_input_index
end GlobalEmbedding.Continuation
