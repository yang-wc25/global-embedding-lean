import Probes.ActualRestrictedRawMeanAssemblyStatement
import Smoothing.ParameterRound2MeanGermResidualMembership
import Smoothing.ParameterRound2UniformRawMeanResidual

/-! Complete actual finite increment with uniform constants selected before
all atlases, normalized targets and smoothing scales. The numerical target
slow profile is supplied by the SAME actual smoothing gain. -/

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

theorem actual_restricted_raw_finite_increment_after_mean
    (q Rsub Lprimary Rsecondary : ℕ) (reserve rho : ℝ) (hrho : 0 < rho)
    (Brest Mrest Kcut T Tinv Tobs TP : ℕ → ℝ)
    (CR CU Cmean : ℕ → ℝ) (hCR : ∀ j, 0 ≤ CR j) (hCU : ∀ j, 0 ≤ CU j) (hCmean : ∀ j, 0 ≤ Cmean j)
    (hAnalytic : ActualRawAnalyticBudget (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      q Rsub Lprimary Rsecondary reserve Brest Mrest Kcut T Tinv Tobs TP CR CU)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (primary : Label → Set (Ep × M)) (epsilon0 : ℝ) (he01 : epsilon0 ≤ 1) :
    ActualRestrictedRawFiniteIncrementAfterMean (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr)
      (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
      q Rsub Lprimary Rsecondary reserve rho hrho Brest Mrest Kcut T Tinv Tobs TP
      CR CU Cmean hCR hCU hCmean hAnalytic A B hA hB S W hS hSO ell hell hell1 H hParam
      F hF g primary epsilon0 he01 := by
  unfold ActualRestrictedRawFiniteIncrementAfterMean
  intro p hsm hphysical C
  unfold ActualRestrictedRawFiniteIncrementConclusion
  intro epsilon he he0lt Top K
  have he1 : epsilon ≤ 1 := he0lt.le.trans he01
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le
  have hphys := hphysical epsilon he he0lt
  refine ⟨hphys.1,?_⟩
  intro G hG hGW hSG gG delta hdelta hdeltatau choice U j inputbar Delta raw Obs obs E coordinates
  have hAnal := hAnalytic j A B hA hB F hF gG (K q).val inputbar G primary S hSO
    ell delta (epsilon*ell) Delta htau htaul hell1 hdelta hdeltatau choice raw Obs obs
    (fun i z hz k hk _ => hParam i z hz k hk)
  have hu := hAnal.2.2
  have hK : p 0 (K q-H) < rho := (hphys.1 q le_rfl).trans_lt (by linarith)
  have hrestrict := parameterRound2_actual_germ_physical_mean_restrict A B S W p H rho ell F hF g q hsm
    epsilon delta he he1 ⟨K q,hK⟩ G hG hSO hSG
  let Mean := incrementsGlobalPrimaryMean F hF gG (K q).val (q+2) (epsilon*ell)
  have hm : (fun t x => delta^2 • (Mean t x-H.val t x)) ∈
      parameterRound2_originalTensorGermSpace A B S G :=
    ⟨hrestrict.2.1.1,fun z hz => hrestrict.2.1.2 z (hGW hz)⟩
  have hmeanBound := (hphys.2 j delta)
  have hmb : (paperAtlasWeighted 0 j (epsilon*ell)
      (incrementsOriginalTensorCoordinates A B (fun t x => delta^2 • (Mean t x-H.val t x)))
      (incrementsOriginalDifferentiation A B) S).toReal ≤
      Cmean j*delta^2*((epsilon*ell)/ell)^(q+1) := by
    rw [hrestrict.2.2 0 j (epsilon*ell)]
    exact hmeanBound.2.1.trans_eq (by rw [mul_div_cancel_right₀ epsilon hell.ne']; ring)
  have hout := actual_original_metric_error_norm_from_germ_remainder_and_mean A B S G hS hSO
    (fun y => F y.1 y.2) U H.val Mean j q delta (epsilon*ell) ell
    (CR j) (Cmean j)
    hdelta hdeltatau htau htaul hell1
    (hCR j) (hCmean j) hAnal.1 hm hAnal.2.1.2 hmb
  have hEcost : CR j+Cmean j ≤ C j := le_add_of_nonneg_right (hCU j)
  have hUcost : CU j ≤ C j := le_add_of_nonneg_left (add_nonneg (hCR j) (hCmean j))
  refine ⟨hout.1,⟨hout.2.1,?_⟩,hu.1,⟨hu.2.1.1,?_⟩,⟨hu.2.2.1,?_⟩⟩
  · exact hout.2.2.trans (mul_le_mul_of_nonneg_right hEcost (by positivity))
  · exact hu.2.1.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUcost hdelta) htau.le)
  · exact hu.2.2.2.trans (mul_le_mul_of_nonneg_right hUcost hdelta)


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_restricted_raw_finite_increment_after_mean
