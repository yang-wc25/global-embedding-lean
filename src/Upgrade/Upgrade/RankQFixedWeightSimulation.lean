import Upgrade.RankQFixedPairExtraction
import GlobalEmbedding.Offline.PairedValueCoincidenceRank

/-!
# Simulate fixed preparation weights after probes returns its weights

The cover and its reference principal frame are prepared once using fixed
auxiliary weights mu (for example 1 and 2). After probes returns lambda,
only parameter-column combinations change. The identities use the SAME
original two-by-two inverse coefficients, extracted from the accepted
`UpgradeRankQDuplicatedPrincipalPacket` hsepB/hsepV proof. Their coefficients
depend only on the two fixed weight lists; they do not depend on the source
point, probe scale, parameters, or fast angles. No coefficient is differentiated.

This repairs the quantifier order needed by finite compact assembly: an open
cover prepared for mu stays fixed when lambda is returned, even if lambda's
two weights are arbitrarily close. Only a fixed error-amplification constant
is added after lambda is known.
-/

noncomputable section
open Module Function GlobalEmbedding.Offline
open scoped BigOperators
namespace GlobalEmbedding.Upgrade

/-- Preparation weights fixed before a finite cover or any probe provider. -/
def rankQPreparationWeights {ι : Type*} (_ : ι) (j : Fin 2) : ℝ :=
  if j = 0 then 1 else 2

theorem rankQPreparationWeights_pos {ι : Type*} (i : ι) (j : Fin 2) :
    0 < rankQPreparationWeights i j := by
  simp only [rankQPreparationWeights]
  split <;> norm_num

theorem rankQPreparationWeights_ne {ι : Type*} (i : ι) :
    rankQPreparationWeights i 0 ≠ rankQPreparationWeights i 1 := by
  norm_num [rankQPreparationWeights]

section Algebra
variable {ι U V : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V]

/-- Public exact versions of the accepted pure tensor/value combinations. -/
theorem rankQFixedPair_pure_identities
    (A : ι → U) (v : ι → V) (lambda : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    let c (i : ι) (j : Fin 2) := (lambda i j ^ 2)⁻¹
    let delta (i : ι) := c i 0 - c i 1
    let J (i : ι) (j : Fin 2) := (A i, -(c i j) • v i)
    ∀ i,
      (-(c i 1) / delta i) • J i 0 + (c i 0 / delta i) • J i 1 = (A i, 0) ∧
      (-1 / delta i) • J i 0 + (1 / delta i) • J i 1 = (0, v i) := by
  let c (i : ι) (j : Fin 2) : ℝ := (lambda i j ^ 2)⁻¹
  let delta (i : ι) := c i 0 - c i 1
  have hd (i : ι) : delta i ≠ 0 := by
    intro hz
    have he : c i 0 = c i 1 := sub_eq_zero.mp hz
    have hs : lambda i 0 ^ 2 = lambda i 1 ^ 2 := inv_inj.mp he
    apply hne i
    exact (sq_eq_sq₀ (hlambda i 0).le (hlambda i 1).le).mp hs
  have hs0 (i : ι) : -(c i 1) / delta i + c i 0 / delta i = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        rw [sub_div, neg_div, sub_eq_add_neg, add_comm]
      _ = 1 := div_self (hd i)
  have hs1 (i : ι) :
      (-(c i 1) / delta i) * -(c i 0) + (c i 0 / delta i) * -(c i 1) = 0 := by
    ring
  have hs2 (i : ι) : (-1 / delta i : ℝ) + 1 / delta i = 0 := by
    rw [neg_div, neg_add_cancel]
  have hs3 (i : ι) :
      (-1 / delta i) * -(c i 0) + (1 / delta i) * -(c i 1) = 1 := by
    calc
      _ = (c i 0 - c i 1) / delta i := by
        ring
      _ = 1 := div_self (hd i)
  have hm0 (w : U) (i : ι) :
      (-(c i 1) / delta i) • w + (c i 0 / delta i) • w = w := by
    rw [← add_smul, hs0 i, one_smul]
  have hm1 (w : V) (i : ι) :
      (-(c i 1) / delta i) • (-(c i 0) • w) +
        (c i 0 / delta i) • (-(c i 1) • w) = 0 := by
    rw [smul_smul, smul_smul, ← add_smul, hs1 i, zero_smul]
  have hm2 (w : U) (i : ι) :
      (-1 / delta i) • w + (1 / delta i) • w = 0 := by
    rw [← add_smul, hs2 i, zero_smul]
  have hm3 (w : V) (i : ι) :
      (-1 / delta i) • (-(c i 0) • w) + (1 / delta i) • (-(c i 1) • w) = w := by
    rw [smul_smul, smul_smul, ← add_smul, hs3 i, one_smul]
  change ∀ i,
    (-(c i 1) / delta i) • (A i, -(c i 0) • v i) +
      (c i 0 / delta i) • (A i, -(c i 1) • v i) = (A i, 0) ∧
    (-1 / delta i) • (A i, -(c i 0) • v i) +
      (1 / delta i) • (A i, -(c i 1) • v i) = (0, v i)
  intro i
  exact ⟨Prod.ext (hm0 (A i) i) (hm1 (v i) i),
    Prod.ext (hm2 (A i) i) (hm3 (v i) i)⟩

/-- Fixed coefficients: pure tensor coefficients plus minus the target
inverse-square weight times the pure value coefficients. -/
def rankQWeightSimulationCoeff (lambda mu : ι → Fin 2 → ℝ)
    (i : ι) (j : Fin 2) (b : Fin 2) : ℝ :=
  let c (k : Fin 2) := (lambda i k ^ 2)⁻¹
  let delta := c 0 - c 1
  let d := (mu i j ^ 2)⁻¹
  if b = 0 then -(c 1) / delta + (-d) * (-1 / delta)
  else c 0 / delta + (-d) * (1 / delta)

/-- The same actual tensor and value at ANY source point can be simulated
with the preparation weights mu, using the weights lambda returned later. -/
theorem simulate_fixed_weights
    (A : ι → U) (v : ι → V) (lambda mu : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1)
    (i : ι) (j : Fin 2) :
    (∑ b : Fin 2, rankQWeightSimulationCoeff lambda mu i j b •
      (A i, -((lambda i b ^ 2)⁻¹) • v i)) =
      (A i, -((mu i j ^ 2)⁻¹) • v i) := by
  let c (k : Fin 2) := (lambda i k ^ 2)⁻¹
  let delta := c 0 - c 1
  let d := (mu i j ^ 2)⁻¹
  let J (b : Fin 2) : U × V := (A i, -(c b) • v i)
  have hp := rankQFixedPair_pure_identities A v lambda hlambda hne i
  have hB : (-(c 1) / delta) • J 0 + (c 0 / delta) • J 1 = (A i, 0) := hp.1
  have hV : (-1 / delta) • J 0 + (1 / delta) • J 1 = (0, v i) := hp.2
  change (∑ b : Fin 2, rankQWeightSimulationCoeff lambda mu i j b • J b) = _
  rw [Fin.sum_univ_two]
  change (-(c 1) / delta + (-d) * (-1 / delta)) • J 0 +
    (c 0 / delta + (-d) * (1 / delta)) • J 1 = _
  calc
    _ = ((-(c 1) / delta) • J 0 + (c 0 / delta) • J 1) +
        (-d) • ((-1 / delta) • J 0 + (1 / delta) • J 1) := by
      simp only [add_smul, smul_add, smul_smul]
      abel
    _ = (A i, 0) + (-d) • ((0 : U), v i) := by rw [hB, hV]
    _ = _ := by simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add]; rfl

end Algebra

/-- A finite uniform coefficient bound, chosen only after the two fixed
weight lists are known. It is independent of all geometric variables. -/
theorem exists_fixed_weight_simulation_bound {ι : Type*} [Fintype ι]
    (lambda mu : ι → Fin 2 → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, 2 * ‖rankQWeightSimulationCoeff lambda mu i j‖ ≤ C := by
  obtain ⟨B, hB⟩ := Finite.exists_le
    (fun ij : ι × Fin 2 ↦ 2 * ‖rankQWeightSimulationCoeff lambda mu ij.1 ij.2‖)
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro i j
  exact (hB (i,j)).trans ((le_abs_self B).trans (by linarith))

section Errors
variable {ι P U V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Apply simulation to an ALREADY TAKEN derivative. The actual two response
errors are retained. The proof reuses the accepted finite-column norm bound. -/
theorem norm_simulate_fixed_weights_error_le
    (J : P →L[ℝ] U × V) (directions : Fin 2 → P)
    (A : ι → U) (v : ι → V) (lambda mu : ι → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1)
    (i : ι) (j : Fin 2) (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ b : Fin 2,
      ‖J (directions b) - (A i, -((lambda i b ^ 2)⁻¹) • v i)‖ ≤ eps) :
    ‖J (∑ b : Fin 2, rankQWeightSimulationCoeff lambda mu i j b • directions b) -
      (A i, -((mu i j ^ 2)⁻¹) • v i)‖ ≤
        2 * eps * ‖rankQWeightSimulationCoeff lambda mu i j‖ := by
  have heq :
      J (∑ b : Fin 2, rankQWeightSimulationCoeff lambda mu i j b • directions b) -
        (A i, -((mu i j ^ 2)⁻¹) • v i) =
      ∑ b : Fin 2, rankQWeightSimulationCoeff lambda mu i j b •
        (J (directions b) - (A i, -((lambda i b ^ 2)⁻¹) • v i)) := by
    rw [← simulate_fixed_weights A v lambda mu hlambda hne i j]
    simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  rw [heq]
  simpa only [Nat.cast_ofNat] using norm_finite_column_error_le
    (fun b : Fin 2 ↦ J (directions b) - (A i, -((lambda i b ^ 2)⁻¹) • v i))
    heps herr (rankQWeightSimulationCoeff lambda mu i j)

end Errors

#print axioms rankQFixedPair_pure_identities
#print axioms simulate_fixed_weights
#print axioms exists_fixed_weight_simulation_bound
#print axioms norm_simulate_fixed_weights_error_le

end GlobalEmbedding.Upgrade
