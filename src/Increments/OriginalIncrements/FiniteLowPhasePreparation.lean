import OriginalIncrements.FiniteJetNeighborhood

/-!
# Compact phase preparation keeps the actual finite low-order budget

The first/two-jet bounds are used only on the input compact carrier.
Continuity produces the surrounding open buffer. Thus the output first/two
jet constant is the explicit original low budget plus one, and no unrelated
maximum over an enlarged domain is substituted for that numerical budget.
The positive spatial margin and buffer remain fixed-input geometric outputs.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff
namespace GlobalEmbedding.Continuation.OriginalIncrements

variable {Ep Es : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]

/-- The only derivative bounds are on the actual compact input carrier.
The produced neighborhood has the explicit bound `max 0 (max A B)+1`.
Its radius is no larger than the original scale used for the second jet. -/
theorem compact_phase_preparation_from_finite_low_jets
    (psi : Ep × Es → ℝ) (K U : Set (Ep × Es))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hpsi : ContDiffOn ℝ ∞ psi U)
    (hnonzero : ∀ x ∈ K,
      (fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es) ≠ 0)
    (ell A B : ℝ) (hell : 0 < ell)
    (hFirst : ∀ x ∈ K, ‖fderiv ℝ psi x‖ ≤ A)
    (hSecond : ∀ x ∈ K, ell*‖iteratedFDeriv ℝ 2 psi x‖ ≤ B) :
    ∃ (mu R rho : ℝ) (O : Set (Ep × Es)),
      0 < mu ∧ 0 < R ∧ 0 < rho ∧ rho ≤ ell ∧
      IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧
      K ⊆ closedBall 0 R ∧
      (∀ x ∈ K, ball x rho ⊆ O) ∧
      ContDiffOn ℝ ∞ psi O ∧
      (∀ x ∈ K, mu ≤ ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) ∧
      (∀ x ∈ O, ‖fderiv ℝ psi x‖ ≤ max 0 (max A B)+1) ∧
      (∀ x ∈ O, rho*‖iteratedFDeriv ℝ 2 psi x‖ ≤ max 0 (max A B)+1) := by
  have hfirst : ContinuousOn (fderiv ℝ psi) U :=
    hpsi.continuousOn_fderiv_of_isOpen hU (by simp)
  have hspatial : ContinuousOn
      (fun x => ‖(fderiv ℝ psi x).comp (ContinuousLinearMap.inr ℝ Ep Es)‖) K :=
    ((hfirst.clm_comp continuousOn_const).norm).mono hKU
  obtain ⟨mu,hmu,hmulower⟩ := hK.exists_forall_le' hspatial
    (fun x hx => norm_pos_iff.mpr (hnonzero x hx))
  have hsecond : ContinuousOn (iteratedFDeriv ℝ 2 psi) U := by
    apply (hpsi.continuousOn_iteratedFDerivWithin (m := 2) (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hU hx).symm
  let f : Bool → Ep × Es → ℝ := fun b x => if b then ell*‖iteratedFDeriv ℝ 2 psi x‖ else ‖fderiv ℝ psi x‖
  have hf (b : Bool) : ContinuousOn (f b) U := by
    cases b
    · exact hfirst.norm
    · exact continuousOn_const.mul hsecond.norm
  have hBound (b : Bool) (x : Ep × Es) (hx : x ∈ K) : f b x ≤ max 0 (max A B) := by
    cases b
    · exact (hFirst x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hSecond x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨V,hV,hKV,hVU,hVbound⟩ := finite_input_upper_neighborhood K U hU hKU f
    (fun _ => max 0 (max A B)) hf hBound 1 zero_lt_one
  obtain ⟨r,hr,hbuffer⟩ := hK.exists_cthickening_subset_open hV hKV
  let rho := min r ell
  let O := thickening rho K
  have hrho : 0 < rho := lt_min hr hell
  have hOV : O ⊆ V :=
    ((thickening_mono (min_le_left r ell) K).trans (thickening_subset_cthickening r K)).trans hbuffer
  obtain ⟨R,hR,hRbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨mu,R,rho,O,hmu,hR,hrho,min_le_right _ _,isOpen_thickening,
    self_subset_thickening hrho K,hOV.trans hVU,?_,?_,hpsi.mono (hOV.trans hVU),hmulower,?_,?_⟩
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using hRbound x hx
  · intro x hx
    exact ball_subset_thickening hx rho
  · intro x hx
    exact (hVbound false x (hOV hx)).le
  · intro x hx
    exact (mul_le_mul_of_nonneg_right (min_le_right r ell) (norm_nonneg _)).trans
      (hVbound true x (hOV hx)).le

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.compact_phase_preparation_from_finite_low_jets
