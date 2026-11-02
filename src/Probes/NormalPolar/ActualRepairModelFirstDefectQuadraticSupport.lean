import NormalPolar.ActualRepairModelFirstDefectCoefficientSupport
import Probes.ActualSecondaryOriginalForcingSupport

/-! The actual negative signed quadratic tensor can be nonzero only in its
true two-label carrier intersection. Both complete amplitude supports produce
this fact, including at inactive points with arbitrary phase behavior. -/
noncomputable section
open Set Filter Function GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_quadratic_active_pair_of_amplitudes
    {P Ep Label : Type*} [TopologicalSpace P]
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [Fintype Label] [DecidableEq Label] {m N : ℕ}
    (phase : Label → P → ℝ) (tau : ℝ)
    (R Q : Label → P → EuclideanSpace ℝ (Fin N))
    (W : Set P) (hW : IsOpen W) (K : Label → Set P)
    (hRsupport : ∀ l, tsupport (fun z : W => R l z) ⊆ Subtype.val ⁻¹' K l)
    (hQsupport : ∀ l, tsupport (fun z : W => Q l z) ⊆ Subtype.val ⁻¹' K l)
    (kappa : Ep × EuclideanSpace ℝ (Fin (m+1)) → P)
    (z : Ep × EuclideanSpace ℝ (Fin (m+1))) (hkappa : ContinuousAt kappa z)
    (hzW : kappa z ∈ W) (l l' : Label) (branch : Fin 4) :
    let H := incrementsSecondaryQuadraticForcing (fun l b x => phase l (kappa (b,x))) tau
      (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
      (fun l b (_ : Unit) x => R l (kappa (b,x)))
      (fun l b (_ : Unit) x => Q l (kappa (b,x)))
      (fun i _ => EuclideanSpace.single i 1) l l' branch z
    actualRealTensorAssembly H ≠ 0 ∨ actualImaginaryTensorAssembly H ≠ 0 → kappa z ∈ K l ∩ K l' := by
  intro H hactive
  let coeff := fun w a => incrementsSecondaryPhysicalCoefficient
    (fun l b x => phase l (kappa (b,x))) tau (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
    (fun l b (_ : Unit) x => R l (kappa (b,x)))
    (fun l b (_ : Unit) x => Q l (kappa (b,x)))
    (fun i _ => EuclideanSpace.single i 1) w a
  have hzCoeff (a : Label) (hn : kappa z ∉ K a) : coeff z a = 0 := by
    by_contra hne
    exact hn (actualRepairModelFirstDefect_coefficient_support_of_amplitudes phase tau R Q W hW K
      hRsupport hQsupport kappa z hkappa hzW a (subset_tsupport _ hne))
  by_contra hn
  have hnot : kappa z ∉ K l ∨ kappa z ∉ K l' := not_and_or.mp hn
  have hzero : H = 0 := actual_secondary_quadratic_zero_of_coefficient
    (fun l b x => phase l (kappa (b,x))) tau (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
    (fun l b (_ : Unit) x => R l (kappa (b,x)))
    (fun l b (_ : Unit) x => Q l (kappa (b,x))) z l l' branch
    (hnot.elim (fun h => Or.inl (hzCoeff l h)) (fun h => Or.inr (hzCoeff l' h)))
  have hi : actualImaginaryTensorAssembly H = 0 := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    rw [actualImaginaryTensorAssembly_basis,hzero]
    simp
  have hr : actualRealTensorAssembly H = 0 := by rw [hzero,map_zero]
  exact hactive.elim (fun h => h hr) (fun h => h hi)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_quadratic_active_pair_of_amplitudes
