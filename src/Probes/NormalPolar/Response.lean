import NormalPolar.Smooth
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Native parameter response of the same actual normal polar operator

The constant is obtained from the derivative of the explicit universal
operator formula on a fixed compact set. It is chosen before all parameters,
source points and actual frames. Projection and first-jet response estimates
then control the derivative of that same formula by the native chain rule.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A uniform derivative bound for the actual universal polar formula. Its
domain contains every pair of orthogonal projections with gap at most 1/2. -/
theorem exists_actualPolarPair_derivative_bound_reserve (q : ℝ) (hq : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P R : V →L[ℝ] V,
      ‖P‖ ≤ 1 → ‖R‖ ≤ 1 → ‖P - R‖ ≤ q →
      ‖fderiv ℝ (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
        actualPolarOperator p.1 p.2) (P, R)‖ ≤ C := by
  let U : Set ((V →L[ℝ] V) × (V →L[ℝ] V)) := {p | ‖p.1 - p.2‖ < 1}
  let K : Set ((V →L[ℝ] V) × (V →L[ℝ] V)) :=
    Metric.closedBall 0 1 ∩ {p | ‖p.1 - p.2‖ ≤ q}
  have hU : IsOpen U := isOpen_lt ((continuous_fst.sub continuous_snd).norm) continuous_const
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le ((continuous_fst.sub continuous_snd).norm) continuous_const)
  have hsub : K ⊆ U := by
    intro p hp
    change ‖p.1 - p.2‖ < 1
    exact hp.2.trans_lt hq
  have hdiff : ContDiffOn ℝ ∞
      (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) ↦ actualPolarOperator p.1 p.2) U := by
    intro p hp
    exact (contDiffAt_actualPolarPair p hp).contDiffWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((hdiff.continuousOn_fderiv_of_isOpen hU (by simp)).mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun P R hP hR hgap ↦ ?_⟩
  apply (hC (P, R) ?_).trans (le_max_left _ _)
  refine ⟨?_, hgap⟩
  simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] using max_le hP hR

theorem exists_actualPolarPair_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P R : V →L[ℝ] V,
      ‖P‖ ≤ 1 → ‖R‖ ≤ 1 → ‖P - R‖ ≤ (1 / 2 : ℝ) →
      ‖fderiv ℝ (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
        actualPolarOperator p.1 p.2) (P, R)‖ ≤ C :=
  exists_actualPolarPair_derivative_bound_reserve (1 / 2 : ℝ) (by norm_num)

/-- A reserve is selected before all parameters, on their unchanged domain. -/
def polarResponseConstantOn (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (q : ℝ) (hq : q < 1) : ℝ :=
  (exists_actualPolarPair_derivative_bound_reserve (V := V) q hq).choose

theorem polarResponseConstantOn_nonneg (q : ℝ) (hq : q < 1) :
    0 ≤ polarResponseConstantOn V q hq :=
  (exists_actualPolarPair_derivative_bound_reserve (V := V) q hq).choose_spec.1

theorem norm_fderiv_actualPolarPair_le_reserve (q : ℝ) (hq : q < 1)
    (P R : V →L[ℝ] V) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hgap : ‖P - R‖ ≤ q) :
    ‖fderiv ℝ (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
      actualPolarOperator p.1 p.2) (P, R)‖ ≤ polarResponseConstantOn V q hq :=
  (exists_actualPolarPair_derivative_bound_reserve (V := V) q hq).choose_spec.2
    P R hP hR hgap

/-- A fixed constant depending only on the finite ambient space. -/
def polarResponseConstant (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : ℝ :=
  (exists_actualPolarPair_derivative_bound (V := V)).choose

theorem polarResponseConstant_nonneg : 0 ≤ polarResponseConstant V :=
  (exists_actualPolarPair_derivative_bound (V := V)).choose_spec.1

theorem norm_fderiv_actualPolarPair_le (P R : V →L[ℝ] V)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hgap : ‖P - R‖ ≤ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (fun p : (V →L[ℝ] V) × (V →L[ℝ] V) ↦
      actualPolarOperator p.1 p.2) (P, R)‖ ≤ polarResponseConstant V :=
  (exists_actualPolarPair_derivative_bound (V := V)).choose_spec.2 P R hP hR hgap

section Parameter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem norm_fderiv_actualPolarOperator_apply_le_reserve (q : ℝ) (hq : q < 1)
    (P : V →L[ℝ] V) (R : X → V →L[ℝ] V) (u a : X)
    (hR : DifferentiableAt ℝ R u) (hPnorm : ‖P‖ ≤ 1) (hRnorm : ‖R u‖ ≤ 1)
    (hgap : ‖P - R u‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator P (R z)) u a‖ ≤
      polarResponseConstantOn V q hq * ‖fderiv ℝ R u a‖ := by
  let f : X → (V →L[ℝ] V) × (V →L[ℝ] V) := fun z ↦ (P, R z)
  let op : ((V →L[ℝ] V) × (V →L[ℝ] V)) → (V →L[ℝ] V) :=
    fun p ↦ actualPolarOperator p.1 p.2
  have hop : DifferentiableAt ℝ op (f u) :=
    (contDiffAt_actualPolarPair (V := V) (P, R u) (hgap.trans_lt hq)).differentiableAt (by simp)
  have hf := (hasFDerivAt_const P u).prodMk hR.hasFDerivAt
  have hh := hop.hasFDerivAt.comp u hf
  change HasFDerivAt (fun z ↦ actualPolarOperator P (R z)) _ u at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply]
  calc
    _ ≤ ‖fderiv ℝ op (f u)‖ * ‖((0 : V →L[ℝ] V), fderiv ℝ R u a)‖ :=
      (fderiv ℝ op (f u)).le_opNorm _
    _ ≤ polarResponseConstantOn V q hq * ‖fderiv ℝ R u a‖ := by
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
        mul_le_mul_of_nonneg_right
          (norm_fderiv_actualPolarPair_le_reserve q hq P (R u) hPnorm hRnorm hgap)
          (norm_nonneg ((0 : V →L[ℝ] V), fderiv ℝ R u a))

theorem norm_fderiv_actualFramePolarOperator_apply_le_reserve
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (q : ℝ) (hq : q < 1)
    (A : X → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : X)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (hgap : ‖(LinearMap.range A₀.toLinearMap)ᗮ.starProjection -
      (LinearMap.range (A u).toLinearMap)ᗮ.starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator
        (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      polarResponseConstantOn V q hq *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  apply (norm_fderiv_actualPolarOperator_apply_le_reserve q hq _ _ u a
    (differentiableAt_actualNormalProjection_fixed_metric A A₀ u hA hinj hmetric)
    (Submodule.starProjection_norm_le _) (Submodule.starProjection_norm_le _) hgap).trans
  exact mul_le_mul_of_nonneg_left
    (norm_fderiv_actualNormalProjection_fixed_metric_apply_le A A₀ u a hA hinj hmetric)
    (polarResponseConstantOn_nonneg q hq)

theorem norm_fderiv_actualFramePolarOperator_from_firstJet_gap_le_reserve
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (q : ℝ) (hq : q < 1)
    (A : X → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : X)
    (hA : DifferentiableAt ℝ A u) (hinj₀ : Function.Injective A₀)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (hgap : ‖(A₀.adjoint.comp A₀).inverse‖ * (‖A u‖ + ‖A₀‖) * ‖A u - A₀‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator
        (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      polarResponseConstantOn V q hq *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  apply norm_fderiv_actualFramePolarOperator_apply_le_reserve q hq A A₀ u a hA hinj hmetric
  rw [norm_sub_rev]
  exact (norm_actualNormalProjection_sub_fixed_metric_le (A u) A₀
    hinj.self_of_nhds hinj₀ hmetric.self_of_nhds).trans hgap

/-- The reference projection is fixed in the parameter direction. This is a
native derivative of the one actual operator, with no assumed response. -/
theorem norm_fderiv_actualPolarOperator_apply_le
    (P : V →L[ℝ] V) (R : X → V →L[ℝ] V) (u a : X)
    (hR : DifferentiableAt ℝ R u) (hPnorm : ‖P‖ ≤ 1) (hRnorm : ‖R u‖ ≤ 1)
    (hgap : ‖P - R u‖ ≤ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator P (R z)) u a‖ ≤
      polarResponseConstant V * ‖fderiv ℝ R u a‖ := by
  let f : X → (V →L[ℝ] V) × (V →L[ℝ] V) := fun z ↦ (P, R z)
  let q : ((V →L[ℝ] V) × (V →L[ℝ] V)) → (V →L[ℝ] V) :=
    fun p ↦ actualPolarOperator p.1 p.2
  have hgap' : ‖P - R u‖ < 1 := hgap.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hq : DifferentiableAt ℝ q (f u) :=
    (contDiffAt_actualPolarPair (V := V) (P, R u) hgap').differentiableAt (by simp)
  have hf := (hasFDerivAt_const P u).prodMk hR.hasFDerivAt
  have hh := hq.hasFDerivAt.comp u hf
  change HasFDerivAt (fun z ↦ actualPolarOperator P (R z)) _ u at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply]
  calc
    _ ≤ ‖fderiv ℝ q (f u)‖ * ‖((0 : V →L[ℝ] V), fderiv ℝ R u a)‖ :=
      (fderiv ℝ q (f u)).le_opNorm _
    _ ≤ polarResponseConstant V * ‖fderiv ℝ R u a‖ := by
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
        mul_le_mul_of_nonneg_right
          (norm_fderiv_actualPolarPair_le P (R u) hPnorm hRnorm hgap)
          (norm_nonneg ((0 : V →L[ℝ] V), fderiv ℝ R u a))

/-- The actual fixed-metric normal projection response, already computed from
the native first jet, gives the actual same-Q parameter response. -/
theorem norm_fderiv_actualFramePolarOperator_apply_le
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D]
    (A : X → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : X)
    (hA : DifferentiableAt ℝ A u)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (hgap : ‖(LinearMap.range A₀.toLinearMap)ᗮ.starProjection -
      (LinearMap.range (A u).toLinearMap)ᗮ.starProjection‖ ≤ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator
        (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      polarResponseConstant V *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  apply (norm_fderiv_actualPolarOperator_apply_le _ _ u a
    (differentiableAt_actualNormalProjection_fixed_metric A A₀ u hA hinj hmetric)
    (Submodule.starProjection_norm_le _) (Submodule.starProjection_norm_le _) hgap).trans
  exact mul_le_mul_of_nonneg_left
    (norm_fderiv_actualNormalProjection_fixed_metric_apply_le A A₀ u a hA hinj hmetric)
    polarResponseConstant_nonneg

/-- Both closeness and response of Q now follow from the actual first jet;
there is no separately supplied projection or identification estimate. -/
theorem norm_fderiv_actualFramePolarOperator_from_firstJet_gap_le
    {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D]
    (A : X → D →L[ℝ] V) (A₀ : D →L[ℝ] V) (u a : X)
    (hA : DifferentiableAt ℝ A u) (hinj₀ : Function.Injective A₀)
    (hinj : ∀ᶠ z in 𝓝 u, Function.Injective (A z))
    (hmetric : ∀ᶠ z in 𝓝 u, (A z).adjoint.comp (A z) = A₀.adjoint.comp A₀)
    (hgap : ‖(A₀.adjoint.comp A₀).inverse‖ * (‖A u‖ + ‖A₀‖) *
      ‖A u - A₀‖ ≤ (1 / 2 : ℝ)) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator
        (LinearMap.range A₀.toLinearMap)ᗮ.starProjection
        (LinearMap.range (A z).toLinearMap)ᗮ.starProjection) u a‖ ≤
      polarResponseConstant V *
        (2 * ‖(A₀.adjoint.comp A₀).inverse‖ * ‖A u‖ * ‖fderiv ℝ A u a‖) := by
  apply norm_fderiv_actualFramePolarOperator_apply_le A A₀ u a hA hinj hmetric
  rw [norm_sub_rev]
  exact (norm_actualNormalProjection_sub_fixed_metric_le (A u) A₀
    hinj.self_of_nhds hinj₀ hmetric.self_of_nhds).trans hgap

end Parameter
end GlobalEmbedding.NormalPolar
