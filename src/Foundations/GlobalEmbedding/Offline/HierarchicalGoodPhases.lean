import GlobalEmbedding.Offline.GoodCovectorDensity
import GlobalEmbedding.Offline.ContinuousRankOneBasis

/-!
# Hierarchical weights for actual good phases

For any finite ordered list of actual good covectors of the original second form,
one common weight Λ > 1 makes every primary, doubled, and distinct-label signed
sum/difference good.  The proof uses the already proved actual open good cone and
a finite simultaneous small-parameter limit.  No replacement open cone or desired
sum/difference hypothesis is supplied.  Inverse-square coefficient rescaling is
proved for the same native rank-one tensor reconstruction.
-/

open GlobalEmbedding.Paper Filter
open scoped Topology BigOperators

namespace GlobalEmbedding.Offline

private theorem inverse_power_ratio {t : ℝ} (ht : t ≠ 0) {i j : ℕ} (hij : i ≤ j) :
    (t ^ j)⁻¹ * t ^ (j - i) = (t ^ i)⁻¹ := by
  have hp : t ^ j = t ^ (j - i) * t ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hij]
  rw [hp, mul_inv, mul_comm (t ^ (j - i))⁻¹ (t ^ i)⁻¹, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ ht), mul_one]

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

theorem eventually_ordered_good_weighted_phases {L : ℕ}
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : Fin L → V →L[ℝ] ℝ)
    (hgood : ∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap)
    (i j : Fin L) (hij : i < j) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      LinearSecondFormGoodCovector B
        (((t⁻¹) ^ j.val • ξ j) + (t⁻¹) ^ i.val • ξ i).toLinearMap ∧
      LinearSecondFormGoodCovector B
        (((t⁻¹) ^ j.val • ξ j) - (t⁻¹) ^ i.val • ξ i).toLinearMap := by
  have hpos : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
  have hplus : Tendsto (fun t : ℝ ↦ ξ j + t ^ (j.val - i.val) • ξ i)
      (𝓝[>] (0 : ℝ)) (𝓝 (ξ j)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ ξ j + t ^ (j.val - i.val) • ξ i) 0 :=
      continuousAt_const.add ((continuousAt_id.pow _).smul continuousAt_const)
    simpa only [zero_pow hpos.ne', zero_smul, add_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hminus : Tendsto (fun t : ℝ ↦ ξ j - t ^ (j.val - i.val) • ξ i)
      (𝓝[>] (0 : ℝ)) (𝓝 (ξ j)) := by
    have hc : ContinuousAt (fun t : ℝ ↦ ξ j - t ^ (j.val - i.val) • ξ i) 0 :=
      continuousAt_const.sub ((continuousAt_id.pow _).smul continuousAt_const)
    simpa only [zero_pow hpos.ne', zero_smul, sub_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hn := (isOpen_linearSecondFormGoodCovector B).mem_nhds (hgood j)
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hplus.eventually hn, hminus.eventually hn, htpos] with t hp hm ht
  have ht0 := ht.ne'
  have hpow : (t ^ j.val)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ ht0)
  have heplus : (t ^ j.val)⁻¹ • (ξ j + t ^ (j.val - i.val) • ξ i) =
      (t⁻¹) ^ j.val • ξ j + (t⁻¹) ^ i.val • ξ i := by
    rw [smul_add, smul_smul, inverse_power_ratio ht0 hij.le, inv_pow, inv_pow]
  have heminus : (t ^ j.val)⁻¹ • (ξ j - t ^ (j.val - i.val) • ξ i) =
      (t⁻¹) ^ j.val • ξ j - (t⁻¹) ^ i.val • ξ i := by
    rw [smul_sub, smul_smul, inverse_power_ratio ht0 hij.le, inv_pow, inv_pow]
  refine ⟨?_, ?_⟩
  · rw [← heplus]
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _ hpow).mpr hp
  · rw [← heminus]
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _ hpow).mpr hm

theorem exists_hierarchical_good_phase_weights {L : ℕ}
    (B : SymmetricSquare V →ₗ[ℝ] W) (ξ : Fin L → V →L[ℝ] ℝ)
    (hgood : ∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap) :
    ∃ Λ : ℝ, 1 < Λ ∧
      (∀ i, LinearSecondFormGoodCovector B (Λ ^ i.val • ξ i).toLinearMap) ∧
      (∀ i, LinearSecondFormGoodCovector B ((2 : ℝ) • (Λ ^ i.val • ξ i)).toLinearMap) ∧
      ∀ i j, i ≠ j →
        LinearSecondFormGoodCovector B (Λ ^ i.val • ξ i + Λ ^ j.val • ξ j).toLinearMap ∧
        LinearSecondFormGoodCovector B (Λ ^ i.val • ξ i - Λ ^ j.val • ξ j).toLinearMap := by
  have hall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i j : Fin L, i < j →
      LinearSecondFormGoodCovector B
        (((t⁻¹) ^ j.val • ξ j) + (t⁻¹) ^ i.val • ξ i).toLinearMap ∧
      LinearSecondFormGoodCovector B
        (((t⁻¹) ^ j.val • ξ j) - (t⁻¹) ^ i.val • ξ i).toLinearMap := by
    simp only [Filter.eventually_all]
    intro i j hij
    exact eventually_ordered_good_weighted_phases B ξ hgood i j hij
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have htone : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
    exact h.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht1, hpairs⟩ := (htpos.and (htone.and hall)).exists
  have hΛ : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr ht1
  have hΛ0 : t⁻¹ ≠ 0 := (zero_lt_one.trans hΛ).ne'
  refine ⟨t⁻¹, hΛ, ?_, ?_, ?_⟩
  · intro i
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _ (pow_ne_zero _ hΛ0)).mpr
      (hgood i)
  · intro i
    apply (linearSecondFormGoodCovector_continuous_smul_iff B _ (2 : ℝ) (by norm_num)).mpr
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _ (pow_ne_zero _ hΛ0)).mpr
      (hgood i)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hp := hpairs i j h
      refine ⟨?_, ?_⟩
      · simpa only [add_comm] using hp.1
      · have hn := (linearSecondFormGoodCovector_continuous_smul_iff B
          ((t⁻¹) ^ j.val • ξ j - (t⁻¹) ^ i.val • ξ i) (-1 : ℝ) (by norm_num)).mpr hp.2
        have he : (-1 : ℝ) • ((t⁻¹) ^ j.val • ξ j - (t⁻¹) ^ i.val • ξ i) =
            (t⁻¹) ^ i.val • ξ i - (t⁻¹) ^ j.val • ξ j := by
          ext v
          simp
        rwa [he] at hn
    · exact hpairs j i h

omit [FiniteDimensional ℝ V] in
theorem rank_one_inverse_square_rescaling
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ)
    (w a : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    continuousRankOneReconstruct (fun i ↦ w i • ξ i) (fun i ↦ a i / (w i) ^ 2) =
      continuousRankOneReconstruct ξ a := by
  ext x y
  simp only [continuousRankOneReconstruct_apply, smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hw i]

theorem rank_one_rescaled_coefficients_pos
    {ι : Type*} (w a : ι → ℝ) (hw : ∀ i, w i ≠ 0) (ha : ∀ i, 0 < a i) :
    ∀ i, 0 < a i / (w i) ^ 2 := by
  intro i
  exact div_pos (ha i) (sq_pos_of_ne_zero (hw i))

#print axioms eventually_ordered_good_weighted_phases
#print axioms exists_hierarchical_good_phase_weights
#print axioms rank_one_inverse_square_rescaling
#print axioms rank_one_rescaled_coefficients_pos

end GlobalEmbedding.Offline
