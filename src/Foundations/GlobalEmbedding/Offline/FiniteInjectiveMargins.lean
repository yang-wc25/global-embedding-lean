import GlobalEmbedding.Paper.LinearMapLowerBoundPerturbation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Uniform local lower bounds for a finite family of actual injective operators

The domains may depend on the finite index.  This is useful for the genuine
`SymmetricSquare (ker ξᵢ)` restrictions in a good dictionary; no common surrogate
kernel or supplied lower margin is required.  Zero-dimensional domains and the
empty index type are included.
-/

open GlobalEmbedding.Paper Filter
open scoped Topology BigOperators

namespace GlobalEmbedding.Offline

theorem finite_injective_family_local_lower_bound
    {P ι : Type*} [TopologicalSpace P] [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P → ∀ i, E i →L[ℝ] F) (p0 : P)
    (hA : ∀ i, ContinuousAt (fun p ↦ A p i) p0)
    (hinj : ∀ i, Function.Injective (A p0 i)) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ U : Set P, IsOpen U ∧ p0 ∈ U ∧
      ∀ p ∈ U, ∀ i v, μ * ‖v‖ ≤ ‖A p i v‖ := by
  classical
  have hanti (i : ι) : ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K (A p0 i) :=
    (A p0 i).toLinearMap.injective_iff_antilipschitz.mp (hinj i)
  choose K hK hanti using hanti
  let T : ℝ := 1 + ∑ i, (K i : ℝ)
  have hT : 0 < T := by dsimp [T]; positivity
  have hKi (i : ι) : (K i : ℝ) ≤ T := by
    have h := Finset.single_le_sum (fun j _ ↦ (K j).coe_nonneg) (Finset.mem_univ i)
    dsimp [T]
    linarith
  have hbase (i : ι) (v : E i) : (1 / T) * ‖v‖ ≤ ‖A p0 i v‖ := by
    have h := ZeroHomClass.bound_of_antilipschitz (A p0 i) (hanti i) v
    have hv : ‖v‖ ≤ T * ‖A p0 i v‖ :=
      h.trans (mul_le_mul_of_nonneg_right (hKi i) (norm_nonneg _))
    have hd : ‖v‖ / T ≤ ‖A p0 i v‖ :=
      (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using hv)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hd
  let μ : ℝ := (1 / T) / 2
  have hμ : 0 < μ := div_pos (div_pos zero_lt_one hT) (by norm_num)
  have hclose : ∀ᶠ p in 𝓝 p0, ∀ i, ‖A p i - A p0 i‖ < μ := by
    rw [Filter.eventually_all]
    intro i
    exact (hA i).tendsto.eventually (eventually_norm_sub_lt (A p0 i) hμ)
  have hbound : ∀ᶠ p in 𝓝 p0, ∀ i v, μ * ‖v‖ ≤ ‖A p i v‖ := by
    filter_upwards [hclose] with p hp
    intro i v
    have herr : ‖A p0 i - A p i‖ ≤ μ := by
      rw [norm_sub_rev]
      exact (hp i).le
    have h := linear_map_lower_bound_perturbation (A p0 i) (A p i)
      (1 / T) μ (hbase i) herr v
    have he : 1 / T - μ = μ := by dsimp [μ]; ring
    rwa [he] at h
  obtain ⟨U, hUsub, hU, hp0⟩ := mem_nhds_iff.mp hbound
  exact ⟨μ, hμ, U, hU, hp0, fun p hp ↦ hUsub hp⟩

theorem injective_of_positive_operator_lower_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {μ : ℝ} (hμ : 0 < μ)
    (hbound : ∀ v, μ * ‖v‖ ≤ ‖A v‖) : Function.Injective A := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change A v = 0 at hv
  have h := hbound v
  rw [hv, norm_zero] at h
  have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact norm_eq_zero.mp hz

theorem inverse_range_norm_le_of_lower_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {μ : ℝ} (hμ : 0 < μ)
    (hbound : ∀ v, μ * ‖v‖ ≤ ‖A v‖) :
    ∃ e : E ≃L[ℝ] LinearMap.range A.toLinearMap,
      (∀ v, (e v).val = A v) ∧ ‖e.symm.toContinuousLinearMap‖ ≤ μ⁻¹ := by
  let e := (LinearEquiv.ofInjective A.toLinearMap
    (injective_of_positive_operator_lower_bound A hμ hbound)).toContinuousLinearEquiv
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hμ.le)
  intro w
  change ‖e.symm w‖ ≤ μ⁻¹ * ‖w.val‖
  have h := hbound (e.symm w)
  have hw : A (e.symm w) = w.val := by
    change (e (e.symm w)).val = w.val
    rw [e.apply_symm_apply]
  rw [hw] at h
  have hd := (le_div_iff₀ hμ).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hd

#print axioms finite_injective_family_local_lower_bound
#print axioms injective_of_positive_operator_lower_bound
#print axioms inverse_range_norm_le_of_lower_bound

end GlobalEmbedding.Offline
