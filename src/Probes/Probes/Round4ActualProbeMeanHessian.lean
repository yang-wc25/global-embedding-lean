import Probes.ActualPrimaryMeanParity

/-!
# Native Hessian of the actual zero-germ mean of linear probe coefficients

The original conjugate pairings and factor 1/4 are retained.  Genuine support
and noncriticality remove the other actual phase germs.  The remaining mean
is identified with an explicit continuous real bilinear map, so its parameter
Hessian is produced instead of assumed.  This module alone does not estimate
the bilinear-map norm uniformly in the small scales.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology BigOperators ComplexConjugate
namespace GlobalEmbedding.Continuation

variable {P X Λ J : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype Λ] {N : ℕ}

private local instance meanLinearSemi : SeminormedAddCommGroup (P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance meanLinearNormed : NormedAddCommGroup (P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanLinearSpace : NormedSpace ℝ (P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanBilinearSemi : SeminormedAddCommGroup (P →L[ℝ] P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance meanBilinearNormed : NormedAddCommGroup (P →L[ℝ] P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanBilinearSpace : NormedSpace ℝ (P →L[ℝ] P →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

/-- Polarization of the exact opposite-phase contribution, over the real
parameter space. Conjugation is explicit and both original orderings remain. -/
def round4ActualMeanBilinear (L : Λ → J → Fin N → P →L[ℝ] ℂ) (i j : J) :
    P →L[ℝ] P →L[ℝ] ℂ :=
  ∑ l, (1/4 : ℝ) •
    ((∑ c, (ContinuousLinearMap.mul ℝ ℂ).bilinearComp (L l i c)
      (Complex.conjCLE.toContinuousLinearMap.comp (L l j c))) +
    (∑ c, (ContinuousLinearMap.mul ℝ ℂ).bilinearComp
      (Complex.conjCLE.toContinuousLinearMap.comp (L l i c)) (L l j c)))

theorem round4ActualMeanBilinear_diagonal
    (L : Λ → J → Fin N → P →L[ℝ] ℂ) (i j : J) (u : P) :
    round4ActualMeanBilinear L i j u u =
      incrementsOppositePrimaryContribution (fun l q c => L l q c u) i j := by
  simp [round4ActualMeanBilinear,incrementsOppositePrimaryContribution,
    dotProduct,ContinuousLinearMap.bilinearComp_apply,Complex.real_smul,mul_add]

/-- The first and second native parameter derivatives of a real quadratic
bilinear expression, with its actual operator norm. -/
theorem round4_bilinear_diagonal_derivatives (B : P →L[ℝ] P →L[ℝ] ℂ) :
    ContDiff ℝ ∞ (fun u => B u u) ∧
    (∀ u, fderiv ℝ (fun v => B v v) u = (B+B.flip) u) ∧
    (∀ u, fderiv ℝ (fderiv ℝ (fun v => B v v)) u = B+B.flip) ∧
    (∀ u, ‖fderiv ℝ (fun v => B v v) u‖ ≤ (2*‖B‖)*‖u‖) ∧
    (∀ u, ‖fderiv ℝ (fderiv ℝ (fun v => B v v)) u‖ ≤ 2*‖B‖) := by
  have hd (u : P) : fderiv ℝ (fun v => B v v) u = (B+B.flip) u := by
    have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id u) (hasFDerivAt_id u)
    dsimp only [id_eq] at h
    rw [h.fderiv]
    ext v
    rfl
  have hh (u : P) : fderiv ℝ (fderiv ℝ (fun v => B v v)) u = B+B.flip := by
    rw [show fderiv ℝ (fun v => B v v) = B+B.flip from funext hd]
    exact (B+B.flip).fderiv
  have hn : ‖B+B.flip‖ ≤ 2*‖B‖ := by
    calc
      _ ≤ ‖B‖+‖B.flip‖ := norm_add_le _ _
      _ = _ := by rw [ContinuousLinearMap.opNorm_flip]; ring
  refine ⟨B.contDiff.clm_apply contDiff_id,hd,hh,?_,?_⟩
  · intro u
    rw [hd]
    exact ((B+B.flip).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  · intro u
    rw [hh]
    exact hn

/-- A genuine zero-phase mean with actual linear coefficient columns has a
uniform-in-parameter Hessian and its first response is O(norm u). The only
geometric premises concern actual support and actual phase germs. -/
theorem round4_actual_zero_mean_hessian
    (phi : Λ → X → ℝ) (L : Λ → J → Fin N → P →L[ℝ] ℂ)
    (S : Λ → Set X) (x : X)
    (hsupport : ∀ u l, x ∉ S l → ∀ q c, L l q c u = 0)
    (hdouble : ∀ l, x ∈ S l → fderiv ℝ (fun y => phi l y+phi l y) x ≠ 0)
    (hinteraction : ∀ l k, l ≠ k → x ∈ S l → x ∈ S k →
      fderiv ℝ (fun y => phi l y+phi k y) x ≠ 0 ∧
      fderiv ℝ (fun y => phi l y-phi k y) x ≠ 0)
    (i j : J) :
    let f := actualParameterZeroMean phi (fun u l q c => L l q c u) x i j
    let B := round4ActualMeanBilinear L i j
    ContDiff ℝ ∞ f ∧
      (∀ u, fderiv ℝ f u = (B+B.flip) u) ∧
      (∀ u, fderiv ℝ (fderiv ℝ f) u = B+B.flip) ∧
      (∀ u, ‖fderiv ℝ f u‖ ≤ (2*‖B‖)*‖u‖) ∧
      (∀ u, ‖fderiv ℝ (fderiv ℝ f) u‖ ≤ 2*‖B‖) := by
  intro f B
  have he : f = fun u => B u u := by
    funext u
    rw [round4ActualMeanBilinear_diagonal]
    exact increments_four_phase_zero_germ_eq_opposite phi _ S x
      (fun l hl q => funext (fun c => hsupport u l hl q c)) hdouble hinteraction i j
  rw [he]
  exact round4_bilinear_diagonal_derivatives B

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4ActualMeanBilinear_diagonal
#print axioms GlobalEmbedding.Continuation.round4_bilinear_diagonal_derivatives
#print axioms GlobalEmbedding.Continuation.round4_actual_zero_mean_hessian
