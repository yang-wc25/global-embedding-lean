import Smoothing.ParameterRound2MeanRawGermReserveSupply
import Smoothing.ParameterRound2MeanRawGermPairEstimates
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

theorem parameterRound2_actual_raw_mean_germ_local_estimates
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    ∃ C : ℕ → ℝ → ℝ, (∀ s R, 0 ≤ C s R) ∧ ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    let Top := parameterRound2_actualGermMeanReserveOperator A B S W p H rho ell F hF g q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) ∧
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*(C s R*Dinput s)*p (s+(q+4)) (K.val-L.val)) := by
  intro p
  let C := fun s R => parameterRound2_rawMeanOriginalGermNormCost
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
    (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T TP hT hTP
  have hC (s R) : 0 ≤ C s R := parameterRound2_rawMeanOriginalGermNormCost_nonneg
    (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T TP hT hTP
  refine ⟨C,hC,?_⟩
  intro F hF g primary hdata
  let Nrm := fun (s : ℕ) (Q0 : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x)) =>
    paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates A B Q0)
      (incrementsOriginalDifferentiation A B) S
  have hRaw (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (s : ℕ) (R : ℝ)
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho})
      (hK : p (s+(q+4)) K.val ≤ R) (hL : p (s+(q+4)) L.val ≤ R) :
      let TA := incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell)
      let TB := incrementsGlobalPrimaryMeanError F hF g L.val.val (q+2) (epsilon*ell)
      (TA ∈ parameterRound2_originalTensorGermSpace A B S W ∧
        TB ∈ parameterRound2_originalTensorGermSpace A B S W) ∧
      (Nrm s TA ≠ ⊤ ∧ (Nrm s TA).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s TB ≠ ⊤ ∧ (Nrm s TB).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s (fun t x => TA t x-TB t x) ≠ ⊤ ∧
        (Nrm s (fun t x => TA t x-TB t x)).toReal ≤
          C s R*((epsilon*ell)/ell)*(Dinput s*p (s+(q+4)) (K.val-L.val))) := by
    intro TA TB
    obtain ⟨G,hG,hGW,hSG,Obs,hObs,⟨data⟩⟩ := hdata epsilon he he1 s R K L hK hL
    exact parameterRound2_actual_raw_restricted_mean_norm_bound
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
      hc (hBnd s R) (hMg s) T TP hT hTP A B hA hB S W hSO F hF g K.val L.val G hG hSG primary
      (epsilon*ell) ell (Dinput s*p (s+(q+4)) (K.val-L.val)) (mul_pos he hell)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) hell1
      (mul_nonneg (hDinput s) (apply_nonneg _ _)) Obs hObs data
      (fun i z hz k hk _ => hParam i z hz k hk)
  have hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W := by
    intro epsilon he he1 K
    have hh := hRaw epsilon he he1 0 (p (0+(q+4)) K.val) K K le_rfl le_rfl
    exact hh.1.1
  refine ⟨hsm,?_⟩
  intro Top
  constructor
  · intro epsilon he he1 s R K hK
    exact parameterRound2_actual_germ_mean_operator_size A B S W hS hSO ell hell H rho
      F hF g q hsm epsilon he he1 K s (C s R)
      (hRaw epsilon he he1 s R K K hK hK).2.1.2
  · intro epsilon he he1 s R K L hK hL
    exact parameterRound2_actual_germ_mean_operator_difference A B S W hS hSO ell hell H rho
      F hF g q hsm epsilon he he1 K L s (q+4) (C s R) (Dinput s)
      (hRaw epsilon he he1 s R K L hK hL).2.2.2.2

#print axioms parameterRound2_actual_raw_mean_germ_local_estimates
end GlobalEmbedding.Continuation
