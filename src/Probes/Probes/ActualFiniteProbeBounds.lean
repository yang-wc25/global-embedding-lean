import Probes.ActualFiniteProbeJets
import Probes.ActualProbeHigherBounds

/-!
# Uniform finite-dictionary bounds for the actual parameter/spatial jets

The explicit finite sum below is independent of the small scales. It controls
all spatial orders up to j, the actual native parameter derivative after each
spatial jet, and the family uniformly on a fixed parameter ball. At j=3 the
orders 0,1,2,3 have sizes delta*tau, delta, delta/tau, delta/tau^2.
-/
noncomputable section
open Set GlobalEmbedding.Paper
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p r N : ℕ}

/-- A finite paired column map is bounded by the sum of its actual column
norms, in the native sup norm on the original parameter space. -/
theorem norm_probePairedColumnMap_apply_le
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F) (u : Fin p → ℝ) :
    ‖probePairedColumnMap label c s u‖ ≤ (∑ i, (‖c i‖ + ‖s i‖)) * ‖u‖ := by
  rw [probePairedColumnMap_apply]
  calc
    _ ≤ ∑ i, ‖u (label (i, false)) • c i + u (label (i, true)) • s i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (‖c i‖ + ‖s i‖) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖u (label (i, false)) • c i‖ + ‖u (label (i, true)) • s i‖ :=
          norm_add_le _ _
        _ = ‖u (label (i, false))‖ * ‖c i‖ + ‖u (label (i, true))‖ * ‖s i‖ := by
          rw [norm_smul, norm_smul]
        _ ≤ ‖u‖ * ‖c i‖ + ‖u‖ * ‖s i‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right (norm_le_pi_norm u _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (norm_le_pi_norm u _) (norm_nonneg _))
        _ = _ := by ring
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The actual operator norm of the entire finite parameter map. -/
theorem norm_probePairedColumnMap_le
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F) :
    ‖probePairedColumnMap label c s‖ ≤ ∑ i, (‖c i‖ + ‖s i‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_probePairedColumnMap_apply_le label c s

/-- Weighted column estimates give one native operator estimate. -/
theorem weighted_norm_probePairedColumnMap_le
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F)
    (q : ℝ) (hq : 0 ≤ q) (C S : Fin r → ℝ)
    (hc : ∀ i, q * ‖c i‖ ≤ C i) (hs : ∀ i, q * ‖s i‖ ≤ S i) :
    q * ‖probePairedColumnMap label c s‖ ≤ ∑ i, (C i + S i) := by
  calc
    _ ≤ q * ∑ i, (‖c i‖ + ‖s i‖) :=
      mul_le_mul_of_nonneg_left (norm_probePairedColumnMap_le label c s) hq
    _ = ∑ i, (q * ‖c i‖ + q * ‖s i‖) := by rw [Finset.mul_sum]; simp_rw [mul_add]
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ add_le_add (hc i) (hs i))

/-- An explicit finite constant retaining every original dictionary weight. -/
def probeFiniteJetConstant (j : ℕ) (weight M K : Fin r → ℝ) : ℝ :=
  ∑ i, 2 * incrementsFastMultiplierConstant j (M i) * K i / weight i ^ 2

theorem probeFiniteJetConstant_nonneg (j : ℕ) (weight M K : Fin r → ℝ)
    (hK : ∀ i, 0 ≤ K i) : 0 ≤ probeFiniteJetConstant j weight M K := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (incrementsFastMultiplierConstant_pos j (M i)).le) (hK i)) (sq_nonneg _)

/-- A single finite constant controls the actual parameter derivative of
all spatial orders up to j, on the original open chart. -/
theorem actualFiniteProbeSpatialJet_parameter_weighted_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (label : (Fin r × Bool) ↪ Fin p) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → Fin N → ℝ)
    (hphaseSmooth : ∀ i, ContDiffOn ℝ ∞ (phase i) O)
    (hamplitudeSmooth : ∀ i, ContDiffOn ℝ ∞ (amplitude i) O)
    (u : Fin p → ℝ) (x : E) (hx : x ∈ O)
    (δ τ ell : ℝ) (M K : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1)
    (hK : ∀ i, 0 ≤ K i)
    (hphase : ∀ i k, k < j → ell ^ k *
      ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ weight i * phase i y) x‖ ≤ M i)
    (hamp : ∀ i k, k ≤ j → ell ^ k * ‖iteratedFDeriv ℝ k (amplitude i) x‖ ≤ K i) :
    τ ^ n * ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ n
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x) u‖ ≤
      (δ * τ) * probeFiniteJetConstant j weight M K := by
  rw [(hasFDerivAt_actualFiniteProbeSpatialJet n label δ τ weight phase amplitude u x
    (fun i ↦ ((hphaseSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (fun i ↦ ((hamplitudeSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))).fderiv]
  have hc i := actualProbeCosColumn_weighted_jet_bound j n hn O hO (phase i) (amplitude i)
    (hphaseSmooth i) (hamplitudeSmooth i) x hx δ τ ell (weight i) (M i) (K i)
    hτ hτell hell (hK i) (hphase i) (hamp i)
  have hs i := actualProbeSinColumn_weighted_jet_bound j n hn O hO (phase i) (amplitude i)
    (hphaseSmooth i) (hamplitudeSmooth i) x hx δ τ ell (weight i) (M i) (K i)
    hτ hτell hell (hK i) (hphase i) (hamp i)
  apply (weighted_norm_probePairedColumnMap_le label _ _ (τ ^ n)
    (pow_nonneg hτ.le n) _ _ hc hs).trans_eq
  rw [probeFiniteJetConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _))]
  ring

/-- The family itself has the same bound, multiplied by the actual parameter
norm. The finite sum is unchanged on any fixed parameter ball. -/
theorem actualFiniteProbeSpatialJet_weighted_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (label : (Fin r × Bool) ↪ Fin p) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → Fin N → ℝ)
    (hphaseSmooth : ∀ i, ContDiffOn ℝ ∞ (phase i) O)
    (hamplitudeSmooth : ∀ i, ContDiffOn ℝ ∞ (amplitude i) O)
    (u : Fin p → ℝ) (x : E) (hx : x ∈ O)
    (δ τ ell : ℝ) (M K : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1)
    (hK : ∀ i, 0 ≤ K i)
    (hphase : ∀ i k, k < j → ell ^ k *
      ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ weight i * phase i y) x‖ ≤ M i)
    (hamp : ∀ i k, k ≤ j → ell ^ k * ‖iteratedFDeriv ℝ k (amplitude i) x‖ ≤ K i) :
    τ ^ n * ‖iteratedFDeriv ℝ n
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude u) x‖ ≤
      ‖u‖ * (δ * τ) * probeFiniteJetConstant j weight M K := by
  have h := actualFiniteProbeSpatialJet_parameter_weighted_bound j n hn O hO label weight
    phase amplitude hphaseSmooth hamplitudeSmooth u x hx δ τ ell M K
    hδ hτ hτell hell hK hphase hamp
  rw [(hasFDerivAt_actualFiniteProbeSpatialJet n label δ τ weight phase amplitude u x
    (fun i ↦ ((hphaseSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (fun i ↦ ((hamplitudeSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))).fderiv] at h
  rw [actualFiniteProbeDisplacement_iteratedFDeriv n label δ τ weight phase amplitude u x
    (fun i ↦ ((hphaseSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))
    (fun i ↦ ((hamplitudeSmooth i).contDiffAt (hO.mem_nhds hx)).of_le (by simp))]
  calc
    _ ≤ τ ^ n * (‖probePairedColumnMap label _ _‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((probePairedColumnMap label _ _).le_opNorm u)
        (pow_nonneg hτ.le n)
    _ = ‖u‖ * (τ ^ n * ‖probePairedColumnMap label _ _‖) := by ring
    _ ≤ ‖u‖ * ((δ * τ) * probeFiniteJetConstant j weight M K) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- The same uniform finite constant gives the source's actual C3 scale. -/
theorem actualFiniteProbe_third_jet_bound
    (O : Set E) (hO : IsOpen O)
    (label : (Fin r × Bool) ↪ Fin p) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → Fin N → ℝ)
    (hphaseSmooth : ∀ i, ContDiffOn ℝ ∞ (phase i) O)
    (hamplitudeSmooth : ∀ i, ContDiffOn ℝ ∞ (amplitude i) O)
    (u : Fin p → ℝ) (x : E) (hx : x ∈ O)
    (δ τ ell : ℝ) (M K : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1)
    (hK : ∀ i, 0 ≤ K i)
    (hphase : ∀ i k, k < 3 → ell ^ k *
      ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ weight i * phase i y) x‖ ≤ M i)
    (hamp : ∀ i k, k ≤ 3 → ell ^ k * ‖iteratedFDeriv ℝ k (amplitude i) x‖ ≤ K i) :
    ‖iteratedFDeriv ℝ 3
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude u) x‖ ≤
      ‖u‖ * probeFiniteJetConstant 3 weight M K * (δ / τ ^ 2) := by
  have h := actualFiniteProbeSpatialJet_weighted_bound 3 3 le_rfl O hO label weight
    phase amplitude hphaseSmooth hamplitudeSmooth u x hx δ τ ell M K
    hδ hτ hτell hell hK hphase hamp
  apply (mul_le_mul_iff_right₀ (pow_pos hτ 3)).mp
  apply h.trans_eq
  field_simp

/-- The actual parameter derivative of C3 jets has the same scale with no
parameter-radius factor. -/
theorem actualFiniteProbe_third_jet_parameter_bound
    (O : Set E) (hO : IsOpen O)
    (label : (Fin r × Bool) ↪ Fin p) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → Fin N → ℝ)
    (hphaseSmooth : ∀ i, ContDiffOn ℝ ∞ (phase i) O)
    (hamplitudeSmooth : ∀ i, ContDiffOn ℝ ∞ (amplitude i) O)
    (u : Fin p → ℝ) (x : E) (hx : x ∈ O)
    (δ τ ell : ℝ) (M K : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1)
    (hK : ∀ i, 0 ≤ K i)
    (hphase : ∀ i k, k < 3 → ell ^ k *
      ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ weight i * phase i y) x‖ ≤ M i)
    (hamp : ∀ i k, k ≤ 3 → ell ^ k * ‖iteratedFDeriv ℝ k (amplitude i) x‖ ≤ K i) :
    ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ 3
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x) u‖ ≤
      probeFiniteJetConstant 3 weight M K * (δ / τ ^ 2) := by
  have h := actualFiniteProbeSpatialJet_parameter_weighted_bound 3 3 le_rfl O hO label weight
    phase amplitude hphaseSmooth hamplitudeSmooth u x hx δ τ ell M K
    hδ hτ hτell hell hK hphase hamp
  apply (mul_le_mul_iff_right₀ (pow_pos hτ 3)).mp
  apply h.trans_eq
  field_simp

#print axioms actualFiniteProbeSpatialJet_parameter_weighted_bound
#print axioms actualFiniteProbeSpatialJet_weighted_bound
#print axioms actualFiniteProbe_third_jet_bound
#print axioms actualFiniteProbe_third_jet_parameter_bound
end GlobalEmbedding.Offline
