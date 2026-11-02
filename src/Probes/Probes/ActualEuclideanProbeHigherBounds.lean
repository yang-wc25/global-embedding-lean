import Probes.ActualFiniteProbeBounds
import Probes.ActualRealHomogeneousProbe

/-!
# Actual Euclidean free-column bounds and finite source-map norms

The original target Euclidean norm is retained with both coordinate-conversion
operator norms. These estimates feed the same full finite first-step family,
including its native parameter derivatives after spatial jets.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Offline

section ColumnNorm
variable {Y ι : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

/-- Native norm of a finite actual source-column parameter map. -/
theorem norm_probeColumnMap_le (g : ι → Y) : ‖probeColumnMap g‖ ≤ ∑ i, ‖g i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [probeColumnMap_apply]
  calc
    _ ≤ ∑ i, ‖u i • g i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖g i‖ * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u i) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Weighted native source-column bounds combine without choosing another norm. -/
theorem weighted_norm_probeColumnMap_le (g : ι → Y) (q : ℝ) (hq : 0 ≤ q)
    (C : ι → ℝ) (hg : ∀ i, q * ‖g i‖ ≤ C i) :
    q * ‖probeColumnMap g‖ ≤ ∑ i, C i := by
  calc
    _ ≤ q * ∑ i, ‖g i‖ := mul_le_mul_of_nonneg_left (norm_probeColumnMap_le g) hq
    _ = ∑ i, q * ‖g i‖ := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hg i)
end ColumnNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {N p r : ℕ}

/-- The actual free scaled column at every spatial order, in the source's
Euclidean target norm and with its exact original negative amplitude. -/
theorem actualEuclideanProbeColumn_weighted_jet_bound
    (sine : Bool) (j n : ℕ) (hn : n ≤ j) (O : Set X) (hO : IsOpen O)
    (ψ : X → ℝ) (A : X → EuclideanSpace ℝ (Fin N))
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : X) (hx : x ∈ O) (δ τ ell lam M K : ℝ)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k+1) (fun y ↦ lam * ψ y) x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n
      (if sine then actualProbeSinColumn δ τ lam ψ A else actualProbeCosColumn δ τ lam ψ A) x‖ ≤
      |δ * τ / lam ^ 2| *
        (euclideanTargetCoordinateCost N * incrementsFastMultiplierConstant j M * K) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y ↦ lam * ψ y) O := hψ.const_smul lam
  have hb := actualTrigModulation_weighted_jet_bound sine j n hn O hO (fun y ↦ lam * ψ y) A
    hΦ hA x hx τ ell M K hτ hτell hell hK hphase hamp
  have hmod := actualTrigModulation_contDiffOn sine (fun y ↦ lam * ψ y) τ A O hΦ hA
  have heq : (if sine then actualProbeSinColumn δ τ lam ψ A else actualProbeCosColumn δ τ lam ψ A) =
      fun y ↦ (-(δ * τ / lam ^ 2)) • actualTrigModulation sine (fun z ↦ lam * ψ z) τ A y := by
    funext y
    cases sine <;> simp only [Bool.false_eq_true, ↓reduceIte, actualProbeCosColumn,
      actualProbeSinColumn, actualTrigModulation, probeFastPhase_eq]
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((hmod.contDiffAt (hO.mem_nhds hx)).of_le (by simp)), norm_smul, Real.norm_eq_abs, abs_neg]
  calc
    _ = |δ * τ / lam ^ 2| *
      (τ ^ n * ‖iteratedFDeriv ℝ n (actualTrigModulation sine (fun y ↦ lam * ψ y) τ A) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- Same finite free-wave constant in the genuine Euclidean target norm. -/
def euclideanFiniteProbeJetConstant (N j : ℕ) (weight M K : Fin r → ℝ) : ℝ :=
  euclideanTargetCoordinateCost N * probeFiniteJetConstant j weight M K

theorem euclideanFiniteProbeJetConstant_nonneg (N j : ℕ) (weight M K : Fin r → ℝ)
    (hK : ∀ i, 0 ≤ K i) : 0 ≤ euclideanFiniteProbeJetConstant N j weight M K :=
  mul_nonneg (euclideanTargetCoordinateCost_nonneg N) (probeFiniteJetConstant_nonneg j weight M K hK)

/-- A single finite free-wave constant controls the actual native parameter
jet map, with all original weights and Euclidean norm costs retained. -/
theorem actualEuclideanFreeProbeJetMap_weighted_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set X) (hO : IsOpen O)
    (label : (Fin r × Bool) ↪ Fin p) (weight : Fin r → ℝ)
    (phase : Fin r → X → ℝ) (amplitude : Fin r → X → EuclideanSpace ℝ (Fin N))
    (hphaseSmooth : ∀ i, ContDiffOn ℝ ∞ (phase i) O)
    (hamplitudeSmooth : ∀ i, ContDiffOn ℝ ∞ (amplitude i) O)
    (x : X) (hx : x ∈ O) (δ τ ell : ℝ) (M K : Fin r → ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : ∀ i, 0 ≤ K i)
    (hphase : ∀ i k, k < j → ell ^ k *
      ‖iteratedFDeriv ℝ (k+1) (fun y ↦ weight i * phase i y) x‖ ≤ M i)
    (hamp : ∀ i k, k ≤ j → ell ^ k * ‖iteratedFDeriv ℝ k (amplitude i) x‖ ≤ K i) :
    τ ^ n * ‖probePairedColumnMap label
      (fun i ↦ iteratedFDeriv ℝ n (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
      (fun i ↦ iteratedFDeriv ℝ n (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x)‖ ≤
      (δ * τ) * euclideanFiniteProbeJetConstant N j weight M K := by
  have hc i := actualEuclideanProbeColumn_weighted_jet_bound false j n hn O hO (phase i) (amplitude i)
    (hphaseSmooth i) (hamplitudeSmooth i) x hx δ τ ell (weight i) (M i) (K i)
    hτ hτell hell (hK i) (hphase i) (hamp i)
  have hs i := actualEuclideanProbeColumn_weighted_jet_bound true j n hn O hO (phase i) (amplitude i)
    (hphaseSmooth i) (hamplitudeSmooth i) x hx δ τ ell (weight i) (M i) (K i)
    hτ hτell hell (hK i) (hphase i) (hamp i)
  simp only [Bool.false_eq_true, ↓reduceIte] at hc hs
  apply (weighted_norm_probePairedColumnMap_le label _ _ (τ ^ n) (pow_nonneg hτ.le n) _ _ hc hs).trans_eq
  simp only [euclideanFiniteProbeJetConstant, probeFiniteJetConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _))]
  ring

#print axioms actualEuclideanProbeColumn_weighted_jet_bound
#print axioms actualEuclideanFreeProbeJetMap_weighted_bound
end GlobalEmbedding.Offline
