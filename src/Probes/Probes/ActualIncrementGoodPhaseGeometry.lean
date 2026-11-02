import Probes.ActualIncrementAdaptedPhaseReserve
import GlobalEmbedding.Paper.IncrementsSymmetricCoordinateProducts
import GlobalEmbedding.Paper.GoodCovector
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Original Good supplies the actual chosen-chart transverse Gram

This remains purely algebraic and adds no auxiliary tangent Riemannian
metric. Original Good of the actual phase, together with actual adaptation,
produces invertibility of the SAME beta Gram in the chosen maximal chart.
The original once-sorted symmetric-product independence is reused exactly.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "D0" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ, D)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- Original algebraic Good of the actual transported first coordinate
forces the SAME original transverse beta Gram to be invertible. -/
theorem actual_increment_transverse_gram_of_good_chart (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M) (x : D)
    (hx : x ∈ chart.target)
    (hgood : GoodCovector F hF (chart.symm x)
      ((EuclideanSpace.proj 0).comp
        (mfderiv 𝓙 𝓙 chart (chart.symm x)))) :
    let β := incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m ↦ incrementsModeCoordinateDirections chart.symm x a.succ)
    (β.comp β.adjoint).IsInvertible := by
  classical
  let c : D → M := chart.symm
  let A : D →L[ℝ] TangentSpace 𝓙 (c x) := mfderiv 𝓙 𝓙 c x
  let H : TangentSpace 𝓙 (c x) →L[ℝ] D := mfderiv 𝓙 𝓙 chart (c x)
  let ξ := (EuclideanSpace.proj 0).comp H
  have hHA : H.comp A = ContinuousLinearMap.id ℝ D := by
    exact (actual_increment_maximal_chart_mdifferentiable chart hchart).comp_symm_deriv hx

  let ins : D0 →ₗ[ℝ] D :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toLinearMap.comp
      ((0 : D0 →ₗ[ℝ] ℝ).vecCons (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap)
  have hins (v : D0) : ins v 0 = 0 := rfl
  have hinss (v : D0) (a : Fin m) : ins v a.succ = v a := rfl
  let e : D0 →ₗ[ℝ] ξ.ker :=
    (A.toLinearMap.comp ins).codRestrict ξ.ker (by
      intro v
      change (H (A (ins v))) 0 = 0
      rw [← ContinuousLinearMap.comp_apply, hHA]
      exact hins v)
  have hei : Function.Injective e := by
    intro u v huv
    have h := congrArg (fun w : ξ.ker ↦ H w.val) huv
    change H (A (ins u)) = H (A (ins v)) at h
    change (H.comp A) (ins u) = (H.comp A) (ins v) at h
    rw [hHA] at h
    ext a
    exact congrArg (fun w : D ↦ w a.succ) h
  obtain ⟨p, hp⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hei)
  have hpe (v : D0) : p (e v) = v :=
    congrArg (fun L : D0 →ₗ[ℝ] D0 ↦ L v) hp
  have hli : LinearIndependent ℝ (fun q : P ↦
      symmetricSquareProduct ξ.ker (e (EuclideanSpace.single q.val.1 1))
        (e (EuclideanSpace.single q.val.2 1))) := by
    apply LinearIndependent.of_comp (symmetricSquareLinearMap p)
    change LinearIndependent ℝ (fun q : P ↦ symmetricSquareProduct D0
      (p (e (EuclideanSpace.single q.val.1 1))) (p (e (EuclideanSpace.single q.val.2 1))))
    simpa only [hpe] using
      increments_symmetric_coordinate_products_linearIndependent m
  have hg : Function.Injective
      ((trueSecondForm F hF (c x)).comp (symmetricSquareLinearMap ξ.ker.subtype)) :=
    hgood.2
  have hB := hli.map' _ (LinearMap.ker_eq_bot.mpr hg)
  have he_single (a : Fin m) :
      (e (EuclideanSpace.single a 1)).val =
        incrementsModeCoordinateDirections c x a.succ := by
    change A (ins (EuclideanSpace.single a 1)) = A (EuclideanSpace.single a.succ 1)
    congr 1
    ext b
    refine Fin.cases ?_ (fun j ↦ ?_) b
    · simp [hins]
    · simp [hinss, PiLp.single_apply]
  have hcols : LinearIndependent ℝ (fun q : P ↦
      incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) := by
    convert hB using 1
    funext q
    symm
    change trueSecondForm F hF (c x)
      (symmetricSquareLinearMap ξ.ker.subtype
        (symmetricSquareProduct ξ.ker (e (EuclideanSpace.single q.val.1 1))
          (e (EuclideanSpace.single q.val.2 1)))) = _
    change trueSecondForm F hF (c x)
      (symmetricSquareProduct (TangentSpace 𝓙 (c x))
        (e (EuclideanSpace.single q.val.1 1)).val
        (e (EuclideanSpace.single q.val.2 1)).val) = _
    rw [he_single, he_single]
    rfl
  have hambi : Function.Injective (incrementsModeAmbientTransverseFrame F hF c x) := by
    intro u v huv
    have hs : (∑ q : P, (u q - v q) •
        incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      change (∑ q : P, (u q - v q) •
        (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ : V)) = 0
      have h := sub_eq_zero.mpr huv
      simpa [incrementsModeAmbientTransverseFrame, sub_smul, Finset.sum_sub_distrib] using h
    ext q
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hcols) _ hs q)
  have hi := (frame_gram_positive_invertible
    (incrementsModeAmbientTransverseFrame F hF c x) hambi).2.2
  rwa [incrementsModeAmbientTransverseFrame_gram] at hi

/-- The actual good phase differential supplies the SAME original beta Gram
on every adapted chosen-chart point. No Gram or inverse estimate is assumed. -/
theorem actual_increment_transverse_gram_of_good_phase
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F)
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (hgood : GoodCovector F hF (chart.symm x)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) psi (chart.symm x)))) :
    let beta := incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ)
    (beta.comp beta.adjoint).IsInvertible := by
  apply actual_increment_transverse_gram_of_good_chart F hF chart hchart x (hOt hx)
  rw [← actual_increment_phaseCovector_eq_chosen_chart psi chart hchart O hO hOt x hx hpsi hadapt]
  exact hgood

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_gram_of_good_chart
#print axioms GlobalEmbedding.Continuation.actual_increment_transverse_gram_of_good_phase
