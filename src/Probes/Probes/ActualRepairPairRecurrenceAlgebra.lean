import Probes.ActualRepairWeightedRecurrence
import Smoothing.ParameterRound2InitialWeights

/-! True full-joint weighted pair bookkeeping for (6.8). The inherited map
orders, fixed reference tensor orders, actual displacement and normalized
metric defect are treated in their original shifted norms. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {ι : Type*} [Fintype ι] {a b c : ℕ}

theorem actual_repair_pair_norm_from_components
    (j : ℕ) (tau t delta theta CU CE inherited : ℝ)
    (htau : 0 < tau) (ht : 0 < t) (htaul : tau ≤ t) (ht1 : t ≤ 1)
    (f u : ι → (Fin a → ℝ) → Fin b → ℝ)
    (g e : ι → (Fin a → ℝ) → Fin c → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (f i) U)
    (hu : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (u i) U)
    (hg : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (g i) U)
    (he : ∀ i, ∃ U : Set (Fin a → ℝ), IsOpen U ∧ S i ⊆ U ∧ ContDiffOn ℝ ∞ (e i) U)
    (hFfinite : paperAtlasWeighted 2 j t f O S ≠ ⊤)
    (hRefFinite : paperAtlasCj j g O S ≠ ⊤)
    (hUfinite : paperAtlasWeighted 2 j tau u O S ≠ ⊤)
    (hEfinite : paperAtlasWeighted 0 j tau e O S ≠ ⊤)
    (hFbound : (paperAtlasWeighted 2 j t f O S).toReal ≤ inherited)
    (hUbound : (paperAtlasWeighted 2 j tau u O S).toReal ≤ CU*delta/tau)
    (hEbound : (paperAtlasWeighted 0 j tau e O S).toReal ≤ CE*theta*(1+inherited)) :
    let next := paperAtlasWeighted 2 j tau (fun i x => f i x+u i x) O S+
      paperAtlasWeighted 0 j tau (fun i x => e i x+g i x) O S
    next ≠ ⊤ ∧ next.toReal ≤
      (paperAtlasCj 2 f O S).toReal+(paperAtlasCj 0 g O S).toReal+
      (tau/t)*inherited+tau*j*(paperAtlasCj j g O S).toReal+
      CU*delta/tau+CE*theta*(1+inherited) := by
  intro next
  have hFI := actual_paper_weighted_inherited_scale 2 j htau.le ht htaul f O S hFfinite
  have hGfinite := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 j tau g O S (by simpa using hRefFinite)
  have hGI := parameterRound2_paperAtlasWeighted_le_base_add_top 0 j htau.le (htaul.trans ht1) g O S (by simpa using hRefFinite)
  have hMap := actual_paper_weighted_add_germs 2 j htau f u O S hO hSO hf hu hFI.1 hUfinite
  have hTensor := actual_paper_weighted_add_germs 0 j htau e g O S hO hSO he hg hEfinite hGfinite
  have hfin : next ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hMap.1,hTensor.1⟩
  refine ⟨hfin,?_⟩
  have hFstep := hFI.2.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hFbound (div_nonneg htau.le ht.le)))
  have htensor := hTensor.2
  simp only [Nat.add_zero] at hGI
  dsimp only [next]
  rw [ENNReal.toReal_add hMap.1 hTensor.1]
  linarith [hMap.2,hFstep,htensor,hGI,hUbound,hEbound]

theorem actual_repair_pair_component_absorption
    {t CU CE inherited referenceTop : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hCU : 0 ≤ CU) (hCE : 0 ≤ CE)
    (hInherited : 0 ≤ inherited) (hReference : 0 ≤ referenceTop)
    (j k : ℕ) (hk : 10 ≤ k) :
    (t^(6/5 : ℝ)/t)*inherited+t^(6/5 : ℝ)*j*referenceTop+
      CU*t^k/t^(6/5 : ℝ)+CE*t^(1/5 : ℝ)*(1+inherited) ≤
    (1+j*referenceTop+CU+CE)*t^(1/5 : ℝ)*(1+inherited) := by
  have hratio := (repair_step_scale_ratios ht).1
  have htheta : 0 ≤ t^(1/5 : ℝ) := Real.rpow_nonneg ht.le _
  have htau : t^(6/5 : ℝ) ≤ t^(1/5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hinc : t^k/t^(6/5 : ℝ) ≤ t^(1/5 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_sub ht]
    have hk' : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  have h0 : (t^(6/5 : ℝ)/t)*inherited ≤ t^(1/5 : ℝ)*inherited := by rw [hratio]
  have h1 : t^(6/5 : ℝ)*j*referenceTop ≤ t^(1/5 : ℝ)*j*referenceTop :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htau (Nat.cast_nonneg _)) hReference
  have h2 : CU*t^k/t^(6/5 : ℝ) ≤ CU*t^(1/5 : ℝ) := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hinc hCU
  have hp : 0 ≤ ((j : ℝ)*referenceTop+CU)*t^(1/5 : ℝ)*inherited := by positivity
  nlinarith [h0,h1,h2,hp]


theorem actual_repair_pair_component_absorption_at_scales
    {t tau delta CU CE inherited referenceTop : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hCU : 0 ≤ CU) (hCE : 0 ≤ CE)
    (hInherited : 0 ≤ inherited) (hReference : 0 ≤ referenceTop)
    (j k : ℕ) (hk : 10 ≤ k) (hdelta : delta = t^k) (htau : tau = t^(6/5 : ℝ)) :
    (tau/t)*inherited+tau*j*referenceTop+CU*delta/tau+CE*t^(1/5 : ℝ)*(1+inherited) ≤
      (1+j*referenceTop+CU+CE)*t^(1/5 : ℝ)*(1+inherited) := by
  rw [hdelta,htau]
  exact actual_repair_pair_component_absorption ht ht1 hCU hCE hInherited hReference j k hk


theorem actual_repair_pair_cost_increase (Cd Cu budget referenceTop : ℝ) (j : ℕ)
    (hCu : 0 ≤ Cu) (hbudget : 0 ≤ budget) :
    1+j*referenceTop+Cu+2*Cd*(1+budget) ≤
      1+j*referenceTop+2*(Cd+Cu)*(1+budget) := by
  nlinarith only [hCu,mul_nonneg hCu hbudget]


theorem actual_repair_pair_finish {value baseMap baseTensor a b c d bound : ℝ}
    (hvalue : value ≤ baseMap+baseTensor+a+b+c+d)
    (hcorrection : a+b+c+d ≤ bound) : value ≤ baseMap+baseTensor+bound := by
  linarith only [hvalue,hcorrection]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_pair_norm_from_components
#print axioms GlobalEmbedding.Continuation.actual_repair_pair_component_absorption
