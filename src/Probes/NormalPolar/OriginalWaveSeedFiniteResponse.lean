import NormalPolar.OriginalWaveSeedPairProjection

/-! The finite subordinate pieces share exactly the two coordinates of
their original label. No extra independent probe parameters are introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

theorem originalProbePair_finite_response
    {r : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (count : Fin r → ℕ) (f : ∀ l, Fin (count l) → ProbeParameters 1 → Y)
    (u : ProbeParameters r)
    (hf : ∀ l s, DifferentiableAt ℝ (f l s) (originalProbePairProjection l u))
    (k : Fin r) (sine : Bool) :
    fderiv ℝ (fun v : ProbeParameters r =>
      ∑ l, ∑ s, f l s (originalProbePairProjection l v)) u (Pi.single (k,sine) 1) =
      ∑ s, fderiv ℝ (f k s) (originalProbePairProjection k u)
        (Pi.single ((0 : Fin 1),sine) 1) := by
  have hd (l : Fin r) (s : Fin (count l)) :
      DifferentiableAt ℝ (fun v => f l s (originalProbePairProjection l v)) u :=
    (hf l s).comp u (originalProbePairProjection l).differentiableAt
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun l v => ∑ s, f l s (originalProbePairProjection l v))
    (fun l _ => (HasFDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hd l s).hasFDerivAt)).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply]
  have he (l : Fin r) :
      fderiv ℝ (fun v => ∑ s, f l s (originalProbePairProjection l v)) u
        (Pi.single (k,sine) 1) =
      ∑ s, fderiv ℝ (fun v => f l s (originalProbePairProjection l v)) u
        (Pi.single (k,sine) 1) := by
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun s v => f l s (originalProbePairProjection l v)) (fun s _ => hd l s)]
    simp only [ContinuousLinearMap.sum_apply]
  simp_rw [he]
  rw [Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl
    intro s _
    exact originalProbePairProjection_response k (f k s) u (hf k s) sine
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro s _
    exact originalProbePairProjection_response_other l k (Ne.symm hl) (f l s) u (hf l s) sine
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

theorem originalProbePair_finite_response_bound
    {r : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (count : Fin r → ℕ) (f : ∀ l, Fin (count l) → ProbeParameters 1 → Y)
    (u : ProbeParameters r)
    (hf : ∀ l s, DifferentiableAt ℝ (f l s) (originalProbePairProjection l u))
    (k : Fin r) (sine : Bool) (target : Fin (count k) → Y)
    (error : Fin (count k) → ℝ)
    (herror : ∀ s,
      ‖fderiv ℝ (f k s) (originalProbePairProjection k u)
        (Pi.single ((0 : Fin 1),sine) 1) - target s‖ ≤ error s) :
    ‖fderiv ℝ (fun v : ProbeParameters r =>
      ∑ l, ∑ s, f l s (originalProbePairProjection l v)) u (Pi.single (k,sine) 1) -
      ∑ s, target s‖ ≤ ∑ s, error s := by
  rw [originalProbePair_finite_response count f u hf k sine,← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => herror s))

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.originalProbePair_finite_response
#print axioms GlobalEmbedding.NormalPolar.originalProbePair_finite_response_bound

