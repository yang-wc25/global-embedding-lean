import Probes.ActualSecondaryRawGermStatement
import Probes.ActualSecondaryGermMetricAddition
import Probes.ActualOriginalIncrementRawNorms
import Smoothing.ParameterRound2MeanRawGermFiniteResidual
import Smoothing.ParameterRound2MeanGermResidualMembership

/-! Complete original metric-error estimate for the SAME finite construction.
The actual finite mean iteration is performed internally. Pure original raw
profiles and fixed actual host/refinement choices produce every primary,
quadratic forcing, secondary and mixed/self metric term. No bound for a
mean, residual, U1, U2 or metric error is an input. The chosen global map and
the mean iterate precede every later derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

theorem actual_original_raw_germ_finite_increment
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hBrest : ∀ s, 0 ≤ Brest s) (hMrest : ∀ s, 0 ≤ Mrest s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    ActualOriginalRawGermFiniteStatement (N := N) (Tr := Tr) (Label := Label)
      (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      A B hA hB S W hS hSO ell hell hell1 H rho hrho q Rsub Lprimary Rsecondary hq
      reserve hc Bmean Mmean Dinput Brest Mrest Kcut hBmean hMmean hDinput hBrest hMrest hKcut
      T Tinv Tobs TP hT hTinv hTobs hTP hParam := by
  unfold ActualOriginalRawGermFiniteStatement
  intro p
  obtain ⟨Cmean,hCmean,epsilon0,he0,he01,hmean⟩ := parameterRound2_actual_raw_germ_mean_q_residual
    (N := N) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
    A B hA hB S W hS hSO ell hell hell1 H rho hrho q Rsub Lprimary hq
    reserve hc Bmean Mmean Dinput hBmean hMmean hDinput T TP hT hTP hParam
  have hrest (j : ℕ) := actual_original_raw_metric_germ_remainder_uniform
    (m := m) (d := d) (N := N) (pcount := c) (M := M) (Tr := Tr) (Label := Label)
    (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary hq
    (by dsimp only [actualSecondarySolveOrder]; omega)
    (by dsimp only [actualSecondarySolveOrder,actualSecondaryInputOrder]; omega)
    reserve (Brest j) (Mrest j) (Kcut j) hc (hBrest j) (hMrest j) (hKcut j)
    T Tinv Tobs TP hT hTinv hTobs hTP
  let CR : ℕ → ℝ := fun j => Classical.choose (hrest j)
  have hCR (j) : 0 ≤ CR j := (Classical.choose_spec (hrest j)).1
  have hrestBound (j) := (Classical.choose_spec (hrest j)).2
  have hwave (j : ℕ) := actual_original_increment_raw_paper_norms_uniform
    (m := m) (d := d) (N := N) (pcount := c) (M := M) (Tr := Tr) (Label := Label)
    (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary hq
    (by dsimp only [actualSecondarySolveOrder]; omega)
    (by dsimp only [actualSecondarySolveOrder,actualSecondaryInputOrder]; omega)
    reserve (Brest j) (Mrest j) (Kcut j) hc (hBrest j) (hMrest j) (hKcut j)
    T Tinv Tobs TP hT hTinv hTobs hTP
  let CU : ℕ → ℝ := fun j => Classical.choose (hwave j)
  have hCU (j) : 0 ≤ CU j := (Classical.choose_spec (hwave j)).1
  have hwaveBound (j) := (Classical.choose_spec (hwave j)).2
  let CE := fun j => (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*CR j+Cmean j
  have hCE (j) : 0 ≤ CE j := add_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) (hCR j)) (hCmean j)
  let C := fun j => CE j+CU j
  have hC (j) : 0 ≤ C j := add_nonneg (hCE j) (hCU j)
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro F hF g primary hSupply
  obtain ⟨hsm,hphysical⟩ := hmean F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he he0lt Top K
  have he1 : epsilon ≤ 1 := he0lt.le.trans he01
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le
  have hphys := hphysical epsilon he he0lt
  refine ⟨hphys.1,?_⟩
  intro delta hdelta hdeltatau choice U j inputbar Delta raw Obs obs E coordinates
  have hh := hrestBound j A B hA hB F hF g (K q).val inputbar W primary S hSO
    ell delta (epsilon*ell) Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs
    (fun i z hz k hk _ => hParam i z hz k hk)
  have hu := hwaveBound j A B hA hB F hF g (K q).val inputbar W primary S hSO
    ell delta (epsilon*ell) Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs
    (fun i z hz k hk _ => hParam i z hz k hk)
  have hK : p 0 (K q-H) < rho := (hphys.1 q le_rfl).trans_lt (by linarith)
  have hm := parameterRound2_actual_germ_physical_mean_mem A B S W p H rho ell F hF g q hsm
    epsilon delta he he1 ⟨K q,hK⟩
  let Mean := incrementsGlobalPrimaryMean F hF g (K q).val (q+2) (epsilon*ell)
  have hmeanBound := (hphys.2 j delta)
  have hmb : (paperAtlasWeighted 0 j (epsilon*ell)
      (incrementsOriginalTensorCoordinates A B (fun t x => delta^2 • (Mean t x-H.val t x)))
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      Cmean j*delta^2*((epsilon*ell)/ell)^(q+1) := by
    exact hmeanBound.2.1.trans_eq (by rw [mul_div_cancel_right₀ epsilon hell.ne']; ring)
  have hout := actual_original_metric_error_norm_from_germ_remainder_and_mean A B S W hS hSO
    (fun y => F y.1 y.2) U H.val Mean j q delta (epsilon*ell) ell
    ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*CR j) (Cmean j)
    hdelta hdeltatau htau htaul hell1
    (mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) (hCR j))
    (hCmean j) hh.1 hm hh.2.2.2 hmb
  have hEcost : CE j ≤ C j := le_add_of_nonneg_right (hCU j)
  have hUcost : CU j ≤ C j := le_add_of_nonneg_left (hCE j)
  refine ⟨hout.1,⟨hout.2.1,?_⟩,hu.1,⟨hu.2.1.1,?_⟩,⟨hu.2.2.1,?_⟩⟩
  · exact hout.2.2.trans (mul_le_mul_of_nonneg_right hEcost (by positivity))
  · exact hu.2.1.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUcost hdelta) htau.le)
  · exact hu.2.2.2.trans (mul_le_mul_of_nonneg_right hUcost hdelta)


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_raw_germ_finite_increment
