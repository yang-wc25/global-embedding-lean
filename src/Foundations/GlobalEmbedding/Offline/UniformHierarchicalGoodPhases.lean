import GlobalEmbedding.Offline.HierarchicalGoodPhases
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# A common hierarchy independent of the number of charts or labels

The explicit weight `M / ε + 2` depends only on an actual common good-neighborhood
radius ε and covector norm bound M.  Its definition has no family, graph, label,
dimension, or chart-count parameter.  All openness predicates below are the
original actual Good predicate.  Obtaining these uniform geometric inputs over
the allowed compact two-jet set is a separate provider obligation.
-/

open GlobalEmbedding.Paper
open scoped Topology

namespace GlobalEmbedding.Offline

noncomputable def hierarchicalGoodWeight (ε M : ℝ) : ℝ := M / ε + 2

theorem hierarchicalGoodWeight_gt_one {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    1 < hierarchicalGoodWeight ε M := by
  dsimp [hierarchicalGoodWeight]
  have h := div_nonneg hM hε.le
  linarith

theorem hierarchicalGoodWeight_small_ratio {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    (hierarchicalGoodWeight ε M)⁻¹ * M < ε := by
  have hΛ : 0 < hierarchicalGoodWeight ε M :=
    zero_lt_one.trans (hierarchicalGoodWeight_gt_one hε hM)
  have he : ε * hierarchicalGoodWeight ε M = M + 2 * ε := by
    dsimp [hierarchicalGoodWeight]
    field_simp
  have hd : M / hierarchicalGoodWeight ε M < ε :=
    (div_lt_iff₀ hΛ).mpr (by rw [he]; linarith)
  simpa only [div_eq_mul_inv, mul_comm] using hd

private theorem power_ratio_of_lt {Λ : ℝ} (hΛ : 1 < Λ) {i j : ℕ} (hij : i < j) :
    0 ≤ (Λ ^ (j - i))⁻¹ ∧ (Λ ^ (j - i))⁻¹ ≤ Λ⁻¹ ∧
      Λ ^ j * (Λ ^ (j - i))⁻¹ = Λ ^ i := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans hΛ
  have hp : Λ ≤ Λ ^ (j - i) := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ.le (show 1 ≤ j - i by omega)
  have hj : Λ ^ j = Λ ^ i * Λ ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij.le]
  refine ⟨inv_nonneg.mpr (pow_nonneg hΛ0.le _),
    (inv_le_inv₀ (pow_pos hΛ0 _) hΛ0).mpr hp, ?_⟩
  rw [hj, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hΛ0.ne'), mul_one]

theorem ordered_weighted_good_of_uniform_radius
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ξ η : V →L[ℝ] ℝ) (hξ : ‖ξ‖ ≤ M)
    (hη : ∀ ζ : V →L[ℝ] ℝ, ‖ζ - η‖ < ε →
      LinearSecondFormGoodCovector B ζ.toLinearMap)
    {i j : ℕ} (hij : i < j) :
    LinearSecondFormGoodCovector B
      ((hierarchicalGoodWeight ε M) ^ j • η +
        (hierarchicalGoodWeight ε M) ^ i • ξ).toLinearMap ∧
    LinearSecondFormGoodCovector B
      ((hierarchicalGoodWeight ε M) ^ j • η -
        (hierarchicalGoodWeight ε M) ^ i • ξ).toLinearMap := by
  let Λ := hierarchicalGoodWeight ε M
  have hΛ : 1 < Λ := hierarchicalGoodWeight_gt_one hε hM
  have hΛ0 : 0 < Λ := zero_lt_one.trans hΛ
  let r : ℝ := (Λ ^ (j - i))⁻¹
  obtain ⟨hr, hrle, hre⟩ := power_ratio_of_lt hΛ hij
  have hnorm : ‖r • ξ‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul hrle hξ (norm_nonneg ξ) (inv_nonneg.mpr hΛ0.le)).trans_lt
      (hierarchicalGoodWeight_small_ratio hε hM)
  have hp : LinearSecondFormGoodCovector B (η + r • ξ).toLinearMap :=
    hη _ (by simpa only [add_sub_cancel_left] using hnorm)
  have hm : LinearSecondFormGoodCovector B (η - r • ξ).toLinearMap :=
    hη _ (by simpa only [sub_sub_cancel_left, norm_neg] using hnorm)
  have heplus : Λ ^ j • (η + r • ξ) = Λ ^ j • η + Λ ^ i • ξ := by
    rw [smul_add, smul_smul, hre]
  have heminus : Λ ^ j • (η - r • ξ) = Λ ^ j • η - Λ ^ i • ξ := by
    rw [smul_sub, smul_smul, hre]
  constructor
  · rw [← heplus]
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _
      (pow_ne_zero _ hΛ0.ne')).mpr hp
  · rw [← heminus]
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ _
      (pow_ne_zero _ hΛ0.ne')).mpr hm

theorem labeled_weighted_good_of_uniform_radius
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ξ : ι → V →L[ℝ] ℝ) (label : ι → ℕ)
    (hnorm : ∀ i, ‖ξ i‖ ≤ M)
    (hball : ∀ i (ζ : V →L[ℝ] ℝ), ‖ζ - ξ i‖ < ε →
      LinearSecondFormGoodCovector B ζ.toLinearMap) :
    (∀ i, LinearSecondFormGoodCovector B
      ((hierarchicalGoodWeight ε M) ^ label i • ξ i).toLinearMap) ∧
    (∀ i, LinearSecondFormGoodCovector B
      ((2 : ℝ) • ((hierarchicalGoodWeight ε M) ^ label i • ξ i)).toLinearMap) ∧
    ∀ i j, label i ≠ label j →
      LinearSecondFormGoodCovector B
        ((hierarchicalGoodWeight ε M) ^ label i • ξ i +
          (hierarchicalGoodWeight ε M) ^ label j • ξ j).toLinearMap ∧
      LinearSecondFormGoodCovector B
        ((hierarchicalGoodWeight ε M) ^ label i • ξ i -
          (hierarchicalGoodWeight ε M) ^ label j • ξ j).toLinearMap := by
  let Λ := hierarchicalGoodWeight ε M
  have hΛ0 : Λ ≠ 0 := (zero_lt_one.trans (hierarchicalGoodWeight_gt_one hε hM)).ne'
  have hprimary (i : ι) : LinearSecondFormGoodCovector B (Λ ^ label i • ξ i).toLinearMap :=
    (linearSecondFormGoodCovector_continuous_smul_iff B _ _ (pow_ne_zero _ hΛ0)).mpr
      (hball i (ξ i) (by simpa using hε))
  refine ⟨hprimary, ?_, ?_⟩
  · intro i
    exact (linearSecondFormGoodCovector_continuous_smul_iff B _ (2 : ℝ) (by norm_num)).mpr
      (hprimary i)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hp := ordered_weighted_good_of_uniform_radius B hε hM
        (ξ i) (ξ j) (hnorm i) (hball j) h
      refine ⟨by simpa only [add_comm] using hp.1, ?_⟩
      have hn := (linearSecondFormGoodCovector_continuous_smul_iff B
        (Λ ^ label j • ξ j - Λ ^ label i • ξ i) (-1 : ℝ) (by norm_num)).mpr hp.2
      have he : (-1 : ℝ) • (Λ ^ label j • ξ j - Λ ^ label i • ξ i) =
          Λ ^ label i • ξ i - Λ ^ label j • ξ j := by ext v; simp
      rwa [he] at hn
    · exact ordered_weighted_good_of_uniform_radius B hε hM
        (ξ j) (ξ i) (hnorm j) (hball i) h

theorem properly_colored_phase_interactions_good
    {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddCommGroup W] [Module ℝ W] {L : ℕ}
    (B : SymmetricSquare V →ₗ[ℝ] W) (G : SimpleGraph ι) (color : G.Coloring (Fin L))
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (ξ : ι → V →L[ℝ] ℝ) (hnorm : ∀ i, ‖ξ i‖ ≤ M)
    (hball : ∀ i (ζ : V →L[ℝ] ℝ), ‖ζ - ξ i‖ < ε →
      LinearSecondFormGoodCovector B ζ.toLinearMap) :
    ∀ i j, G.Adj i j →
      LinearSecondFormGoodCovector B
        ((hierarchicalGoodWeight ε M) ^ (color i).val • ξ i +
          (hierarchicalGoodWeight ε M) ^ (color j).val • ξ j).toLinearMap ∧
      LinearSecondFormGoodCovector B
        ((hierarchicalGoodWeight ε M) ^ (color i).val • ξ i -
          (hierarchicalGoodWeight ε M) ^ (color j).val • ξ j).toLinearMap := by
  intro i j hij
  apply (labeled_weighted_good_of_uniform_radius B hε hM ξ
    (fun k ↦ (color k).val) hnorm hball).2.2 i j
  intro heq
  exact color.valid hij (Fin.ext heq)

#print axioms hierarchicalGoodWeight_gt_one
#print axioms hierarchicalGoodWeight_small_ratio
#print axioms labeled_weighted_good_of_uniform_radius
#print axioms properly_colored_phase_interactions_good

end GlobalEmbedding.Offline
