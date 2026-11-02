import Smoothing.ParameterRound2MeanRawGermLocalEstimates
import Smoothing.ParameterRound2MeanGermPhysicalConclusion

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-! Complete finite mean inversion from raw primitive profiles, on the
original symmetric reserve, with the original fast weighted norm of the
physical delta-squared residual. No local T or final mean bound is supplied.
The threshold precedes F/g, epsilon, all later j and delta. -/

def ParameterRound2ActualRawGermMeanFiniteStatement
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) : Prop :=
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∃ Cmean : ℕ → ℝ, (∀ j, 0 ≤ Cmean j) ∧
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    ParameterRound2ActualGermMeanPhysicalResidual A B S W p H rho ell q Cmean epsilon0 F hF g hsm

theorem parameterRound2_actual_raw_germ_mean_q_residual
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    ParameterRound2ActualRawGermMeanFiniteStatement (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
      A B hA hB S W hS hSO
      ell hell hell1 H rho hrho q Rsub Lprimary hq
      reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP
      hT hTP hParam := by
  unfold ParameterRound2ActualRawGermMeanFiniteStatement
  intro p
  obtain ⟨C,hC,hlocal⟩ := parameterRound2_actual_raw_mean_germ_local_estimates
    (N := N) (Tr := Tr) (Λ := Λ) (Β := Β)
    A B hA hB S W hS hSO ell hell hell1 H rho q Rsub Lprimary hq
    reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam
  obtain ⟨Cmean,hCmean,epsilon0,he0,he01,hphysical⟩ := parameterRound2_actual_germ_mean_physical_uniform
    (N := N) (Λ := Λ) (Β := Β) A B S W hS hSO ell hell H rho hrho q hq
    C (fun s R => C s R*Dinput s)
  refine ⟨Cmean,hCmean,epsilon0,he0,he01,?_⟩
  intro F hF g primary hdata
  obtain ⟨hsm,hsize,hdiff⟩ := hlocal F hF g primary hdata
  exact ⟨hsm,hphysical F hF g hsm hsize hdiff⟩


#print axioms parameterRound2_actual_raw_germ_mean_q_residual
end GlobalEmbedding.Continuation
