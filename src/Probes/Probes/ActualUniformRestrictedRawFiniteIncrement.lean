import Probes.ActualUniformRestrictedRawStatement
import Probes.ActualRestrictedRawMeanAssembly

/-! The finite-increment estimate with C_j and epsilon0 before the actual
atlas, target and smoothing scale. No desired output norm is supplied. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem actual_original_uniform_restricted_raw_germ_finite_increment
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ActualUniformRestrictedRawGermFiniteStatement (m := m) (d := d) (N := N) (c := c) (M := M)
      (Tr := Tr) (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Brest Mrest Kcut
      hBmean hMmean hDinput hBrest hMrest hKcut T Tinv Tobs TP hT hTinv hTobs hTP := by
  unfold ActualUniformRestrictedRawGermFiniteStatement
  obtain ⟨Cmean,hCmean,epsilon0,he0,he01,hmean⟩ :=
    parameterRound2_actual_raw_germ_mean_q_residual_uniform_before_input
      (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
      B0 rho hrho q Rsub Lprimary hq reserve hc Bmean Mmean Dinput hBmean hMmean hDinput T TP hT hTP
  obtain ⟨CR,CU,hCR,hCU,hAnalytic⟩ := exists_uniform_actual_raw_analytic_budgets
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
    (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    q Rsub Lprimary Rsecondary hq reserve hc Brest Mrest Kcut hBrest hMrest hKcut
    T Tinv Tobs TP hT hTinv hTobs hTP
  let CE := fun j => CR j+Cmean j
  have hCE (j) : 0 ≤ CE j := add_nonneg (hCR j) (hCmean j)
  let C := fun j => CE j+CU j
  have hC (j) : 0 ≤ C j := add_nonneg (hCE j) (hCU j)
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro A B hA hB S W hS hSO ell hell hell1 H p hH hParam F hF g primary hSupply
  obtain ⟨hsm,hphysical⟩ := hmean A B hA hB S W hS hSO ell hell hell1 H hH hParam F hF g primary hSupply
  refine ⟨hsm,?_⟩
  exact actual_restricted_raw_finite_increment_after_mean
    q Rsub Lprimary Rsecondary reserve rho hrho Brest Mrest Kcut T Tinv Tobs TP
    CR CU Cmean hCR hCU hCmean hAnalytic A B hA hB S W hS hSO ell hell hell1 H hParam
    F hF g primary epsilon0 he01 hsm hphysical


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_restricted_raw_germ_finite_increment
