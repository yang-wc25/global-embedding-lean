import Probes.ActualOriginalUnitFreeNormal
import Probes.ActualIncrementFreeNormalKernel

/-! The actual normalized two-projection field satisfies the ORIGINAL freedom
condition on ker(d phase), not merely its once-sorted coordinate rows. The
converse bridge uses the genuine inverse-chart derivative and the full
transverse coordinate expansion, including both orders of every pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_chart_free_of_transverse_kernel
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (chart : OpenPartialHomeomorph M D) (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ chart.target)
    (xi : TangentSpace 𝓙 (chart.symm x) →L[ℝ] ℝ)
    (hxi : xi = (EuclideanSpace.proj 0).comp (mfderiv 𝓙 𝓙 chart (chart.symm x)))
    (normal : normalSpace (I := 𝓙) F (chart.symm x))
    (hbeta : incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) normal = 0) :
    ∀ u v : xi.ker, inner ℝ
      ((trueSecondForm F hF (chart.symm x)
        (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) u.val v.val)) : V)
      (normal : V) = 0 := by
  classical
  let A : D →L[ℝ] TangentSpace 𝓙 (chart.symm x) := mfderiv 𝓙 𝓙 chart.symm x
  let H : TangentSpace 𝓙 (chart.symm x) →L[ℝ] D := mfderiv 𝓙 𝓙 chart (chart.symm x)
  let direction : Fin m → TangentSpace 𝓙 (chart.symm x) :=
    fun a => incrementsModeCoordinateDirections chart.symm x a.succ
  have hAH : A.comp H = ContinuousLinearMap.id ℝ _ := by
    have hHA : H.comp A = ContinuousLinearMap.id ℝ D :=
      (actual_increment_maximal_chart_mdifferentiable chart hchart).comp_symm_deriv hx
    apply ContinuousLinearMap.ext
    intro v
    apply (actual_increment_maximal_chart_mdifferentiable chart hchart).mfderiv_injective
      (chart.map_target hx)
    change (H.comp A) (H v) = H v
    rw [hHA]
    rfl
  have hExpansion (u : xi.ker) :
      (u : TangentSpace 𝓙 (chart.symm x)) = ∑ a : Fin m, H u a.succ • direction a := by
    have hzero : H u 0 = 0 := by
      have hh := u.property
      change xi u = 0 at hh
      exact (congrArg (fun L : TangentSpace 𝓙 (chart.symm x) →L[ℝ] ℝ =>
        L (u : TangentSpace 𝓙 (chart.symm x))) hxi).symm.trans hh
    have hs : H u = ∑ a : Fin m, H u a.succ • EuclideanSpace.single a.succ 1 := by
      ext i
      refine Fin.cases ?_ (fun b => ?_) i
      · simp [hzero]
      · simp [Pi.single_apply]
    have hh := congrArg A hs
    have hAu : A (H u) = u := by
      change (A.comp H) u = u
      rw [hAH]
      rfl
    rw [hAu,map_sum] at hh
    change (u : TangentSpace 𝓙 (chart.symm x)) =
      ∑ a : Fin m, H u a.succ • A (EuclideanSpace.single a.succ 1)
    simpa only [map_smul] using hh
  have hColumns (a b : Fin m) : inner ℝ
      ((trueSecondForm F hF (chart.symm x)
        (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) (direction a) (direction b))) : V)
      (normal : V) = 0 := by
    have hSorted (a b : Fin m) (hab : a ≤ b) : inner ℝ
        ((trueSecondForm F hF (chart.symm x)
          (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) (direction a) (direction b))) : V)
        (normal : V) = 0 := by
      have hh := congrArg (fun z => z (⟨(a,b),hab⟩ : {p : Fin m × Fin m // p.1 ≤ p.2})) hbeta
      exact hh
    rcases le_total a b with hab | hba
    · exact hSorted a b hab
    · rw [symmetricSquareProduct_comm]
      exact hSorted b a hba
  intro u v
  rw [hExpansion u,hExpansion v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, sum_inner,
    real_inner_smul_left, hColumns, mul_zero, Finset.sum_const_zero]

theorem actual_increment_phase_free_of_transverse_kernel
    (F : M → V) (hF : ContMDiff 𝓙 𝓘(ℝ,V) ∞ F)
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
    (hadapt : ∀ z ∈ O, psi (chart.symm z) = z 0)
    (normal : normalSpace (I := 𝓙) F (chart.symm x))
    (hbeta : incrementsTransversePairing F hF (chart.symm x)
      (fun a : Fin m => incrementsModeCoordinateDirections chart.symm x a.succ) normal = 0) :
    let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
    ∀ u v : xi.ker, inner ℝ
      ((trueSecondForm F hF (chart.symm x)
        (symmetricSquareProduct (TangentSpace 𝓙 (chart.symm x)) u.val v.val)) : V)
      (normal : V) = 0 :=
  actual_increment_chart_free_of_transverse_kernel F hF chart hchart x (hOt hx) _
    (actual_increment_phaseCovector_eq_chosen_chart psi chart hchart O hO hOt x hx hpsi hadapt)
    normal hbeta

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_increment_chart_free_of_transverse_kernel
#print axioms GlobalEmbedding.Continuation.actual_increment_phase_free_of_transverse_kernel
