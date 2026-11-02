import GlobalEmbedding.Paper.CollarUniformNormalizedDerivatives

/-!
# Uniform canonical Taylor data on a compact analytic set

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Compactness turns genuine local joint Taylor expansions and local
uniform derivative bounds into one positive radius and one bound on the real torus slice.
-/

open Set
open scoped NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- On a compact set where a complex Banach-valued function is analytic, canonical normalized
Taylor derivatives have one positive weighted operator-norm radius and actually sum to the
function on that same radius, uniformly in the center.

Source: Proposition `prop:collar`, proof lines 530–534. Near each compact-set point choose a
genuine joint power series and a smaller positive radius δ with 2δ inside its ball. The local
uniform derivative theorem gives one bound for all nearby centers and all orders. Actual
change-of-origin expansions give normalized Taylor sums throughout a δ-ball at each nearby
center. These open neighborhoods cover the compact set. A finite subcover gives a positive
minimum radius and a finite sum of local majorants. Shrinking each local radius to that minimum
preserves the weighted norm estimate and the actual sums. The empty compact set is immediate.
-/
theorem collar_compact_taylor_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∃ M : ℝ≥0,
      (∀ x ∈ K, ∀ n : ℕ,
        ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f x‖₊ * ρ ^ n ≤ M) ∧
      (∀ x ∈ K, ∀ z ∈ Metric.eball (0 : E) (ρ : ℝ≥0∞),
        HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ •
          iteratedFDeriv ℂ n f x (fun _ : Fin n ↦ z)) (f (x + z))) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, zero_lt_one, 0, by simp⟩
  have hlocal (x : K) : ∃ δ : ℝ≥0, 0 < δ ∧ ∃ M : ℝ≥0,
      ∀ y ∈ Metric.ball x.val (δ : ℝ),
        (∀ n : ℕ, ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f y‖₊ * δ ^ n ≤ M) ∧
        (∀ z ∈ Metric.eball (0 : E) (δ : ℝ≥0∞),
          HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ •
            iteratedFDeriv ℂ n f y (fun _ : Fin n ↦ z)) (f (y + z))) := by
    obtain ⟨p, r, hp⟩ := hf x.val x.property
    obtain ⟨R, hR, hRr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
    have hRpos : 0 < R := by exact_mod_cast hR
    let δ : ℝ≥0 := R / 3
    have hδ : 0 < δ := div_pos hRpos (by norm_num)
    have hδR : δ + δ < R := by
      apply NNReal.coe_lt_coe.mp
      change (R : ℝ) / 3 + (R : ℝ) / 3 < (R : ℝ)
      have hRreal : 0 < (R : ℝ) := by exact_mod_cast hRpos
      linarith
    have hδr : ((δ + δ : ℝ≥0) : ℝ≥0∞) < r :=
      (show ((δ + δ : ℝ≥0) : ℝ≥0∞) < (R : ℝ≥0∞) by exact_mod_cast hδR).trans hRr
    obtain ⟨M, hM⟩ := collar_uniform_normalized_derivatives hp δ δ hδr
    refine ⟨δ, hδ, M, ?_⟩
    intro y hy
    have hyδ : ‖y - x.val‖₊ ≤ δ := by
      exact_mod_cast (le_of_lt (show ‖y - x.val‖ < (δ : ℝ) by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy))
    have hxy : x.val + (y - x.val) = y := by abel
    have hyr : (‖y - x.val‖₊ : ℝ≥0∞) < r := by
      apply lt_of_le_of_lt _ hδr
      exact_mod_cast hyδ.trans (le_add_right le_rfl : δ ≤ δ + δ)
    have hsmall : (δ : ℝ≥0∞) ≤ r - (‖y - x.val‖₊ : ℝ≥0∞) := by
      apply ENNReal.le_sub_of_add_le_right ENNReal.coe_ne_top
      apply le_trans _ hδr.le
      exact_mod_cast (add_le_add le_rfl hyδ : δ + ‖y - x.val‖₊ ≤ δ + δ)
    refine ⟨by simpa only [hxy] using hM (y - x.val) hyδ, ?_⟩
    intro z hz
    simpa only [hxy] using (hp.changeOrigin hyr).hasSum_iteratedFDeriv
      ((Metric.eball_subset_eball hsmall) hz)
  choose δ hδ M hlocal using hlocal
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.val (δ x : ℝ) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by exact_mod_cast hδ ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ Metric.ball x.val (δ x : ℝ))
    (fun _ ↦ Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hit, _⟩ := mem_iUnion.mp hi
    exact ⟨i, hit⟩
  let ρ : ℝ≥0 := t.inf' htne δ
  have hρ : 0 < ρ := (Finset.lt_inf'_iff htne).mpr (fun i _ ↦ hδ i)
  have hρle (i : K) (hi : i ∈ t) : ρ ≤ δ i := Finset.inf'_le _ hi
  refine ⟨ρ, hρ, ∑ i ∈ t, M i, ?_, ?_⟩
  · intro x hx n
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left' (hρle i hit) n) zero_le).trans
      (((hlocal i x hxi).1 n).trans (Finset.single_le_sum (fun _ _ ↦ zero_le) hit))
  · intro x hx z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
    exact (hlocal i x hxi).2 z ((Metric.eball_subset_eball (by exact_mod_cast hρle i hit)) hz)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_compact_taylor_bounds
