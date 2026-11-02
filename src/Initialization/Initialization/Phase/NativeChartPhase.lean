import Initialization.Phase.ChartPhase
import Initialization.Assembly.ChartImmersion
import Initialization.Phase.AlgebraicKernelTransport
import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.BestPhaseMaximumAttainment

/-!
# The original true second form in an arbitrary actual smooth chart

The chart normal Hessian is transported to the original normal-valued second
fundamental form by the actual chart differential. This is an exact algebraic
identity; it does not identify different auxiliary tangent norms or claim that
an inverse chart is smooth away from its target.
-/

noncomputable section
open Manifold IsManifold Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance nativeChartRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance nativeChartSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {N : ℕ}

/-- The genuine chart differential is an equivalence of the actual tangent
space with the chart's model. No quantitative norm claim is made here. -/
def initializationChartTangentEquiv (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (x : M) (hx : x ∈ e.source) :
    TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (mvfderiv 𝓘(ℝ, E) e x).toLinearMap
    ((initialization_chart_mdifferentiable e he).mfderiv_bijective hx)).toContinuousLinearEquiv

@[simp] theorem initializationChartTangentEquiv_apply (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (x : M) (hx : x ∈ e.source)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    initializationChartTangentEquiv e he x hx v = mvfderiv 𝓘(ℝ, E) e x v := rfl

/-- The actual coordinate derivative has precisely the original tangent image.
Surjectivity of the genuine inverse-chart derivative proves both inclusions. -/
theorem initialization_chart_normalSpace
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) :
    normalSpace (I := 𝓘(ℝ, E)) H x =
      (LinearMap.range (fderiv ℝ (H ∘ e.symm) (e x)).toLinearMap)ᗮ := by
  have hd (v : E) : fderiv ℝ (H ∘ e.symm) (e x) v =
      mvfderiv 𝓘(ℝ, E) H x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) v) := by
    convert initialization_coordinate_fderiv_apply H hH e he (e.map_source hx) v using 1
    rw [e.left_inv hx]
  have hs : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) :=
    ((initialization_chart_mdifferentiable e he).symm.mfderiv_bijective (e.map_source hx)).2
  have hr : LinearMap.range (mvfderiv 𝓘(ℝ, E) H x).toLinearMap =
      LinearMap.range (fderiv ℝ (H ∘ e.symm) (e x)).toLinearMap := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hs v
      exact ⟨u, (hd u).trans (congrArg (mvfderiv 𝓘(ℝ, E) H x) hu)⟩
    · rintro ⟨v, rfl⟩
      exact ⟨mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) v, (hd v).symm⟩
  exact congrArg Submodule.orthogonal hr

/-- Actual chartwise normal second jets evaluate to the original normal-valued
second form after the actual chart differential in both arguments. -/
theorem initialization_chart_secondForm_product
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) (v w : TangentSpace 𝓘(ℝ, E) x) :
    chartNormalSecondJet (H ∘ e.symm) (e x)
      (symmetricSquareProduct E (initializationChartTangentEquiv e he x hx v)
        (initializationChartTangentEquiv e he x hx w)) =
      (trueSecondForm H hH x (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x) v w) :
        EuclideanSpace ℝ (Fin N)) := by
  have hrep : ContDiffAt ℝ 2 (H ∘ e.symm) (e x) :=
    ((hH.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn).contDiffAt
      (e.open_target.mem_nhds (e.map_source hx)) |>.of_le (by simp)
  have hprojection := congrArg (fun U : Submodule ℝ (EuclideanSpace ℝ (Fin N)) ↦
    U.starProjection) (initialization_chart_normalSpace H hH e he x hx)
  rw [chartNormalSecondJet_product hrep, ← hprojection, trueSecondForm_product]
  have h := (second_form_chart_invariance_general H x (hH.contMDiffAt.of_le (by simp))).2.1
    e (maximalAtlas_subset_of_le (by simp) he) hx v w
  exact congrArg Subtype.val h

/-- The complete actual normal second-form operator is identified on the whole
original binary quotient, not only its generating products. -/
theorem initialization_chart_trueSecondForm
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) :
    (chartNormalSecondJet (H ∘ e.symm) (e x)).toLinearMap.comp
      (symmetricSquareLinearMap (initializationChartTangentEquiv e he x hx).toLinearMap) =
      (normalSpace (I := 𝓘(ℝ, E)) H x).subtype.comp (trueSecondForm H hH x) := by
  apply (symmetricSquareRelations (TangentSpace 𝓘(ℝ, E) x)).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change chartNormalSecondJet (H ∘ e.symm) (e x)
    (symmetricSquareLinearMap (initializationChartTangentEquiv e he x hx).toLinearMap
      (symmetricSquareProduct (TangentSpace 𝓘(ℝ, E) x) v w)) = _
  rw [initialization_symmetricSquareLinearMap_product]
  exact initialization_chart_secondForm_product H hH e he x hx v w

/-- A genuine good hyperplane of the actual chart normal Hessian pulls back to
an actual original GoodCovector. This statement has no auxiliary metric input. -/
theorem initialization_goodCovector_of_chart
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : M) (hx : x ∈ e.source) (ξ : E →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (hinj : Function.Injective (covectorRestriction
      (chartNormalSecondJet (H ∘ e.symm) (e x)) ξ)) :
    GoodCovector H hH x
      (ξ.comp (initializationChartTangentEquiv e he x hx).toContinuousLinearMap) := by
  refine ⟨coefficientCovector_ne_zero (initializationChartTangentEquiv e he x hx) ξ hξ, ?_⟩
  have ht := initialization_kernel_pullback_injective
    (initializationChartTangentEquiv e he x hx) ξ
    (chartNormalSecondJet (H ∘ e.symm) (e x)) hinj
  have heq := initialization_chart_trueSecondForm H hH e he x hx
  intro u v huv
  apply ht
  let inclusion := symmetricSquareLinearMap
    (ξ.comp (initializationChartTangentEquiv e he x hx).toContinuousLinearMap).ker.subtype
  have hu := congrArg (fun L ↦ L (inclusion u)) heq
  have hv := congrArg (fun L ↦ L (inclusion v)) heq
  exact hu.trans ((congrArg (normalSpace (I := 𝓘(ℝ, E)) H x).subtype huv).trans hv.symm)

/-- Positive phase in a covering genuine smooth buffered atlas gives the
original norm-independent PhaseRegular predicate of the very same global map.
No global smoothness of chart representatives outside their targets is used. -/
theorem initialization_phaseRegular_of_bufferedAtlas
    (hdim : 2 ≤ Module.finrank ℝ E)
    (H : M → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ H)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hphase : ∀ i y, y ∈ (A.chart i).target →
      0 < chartPhaseMargin (H ∘ (A.chart i).symm) y) : PhaseRegular H hH := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  have hx : x ∈ (A.chart i).source := A.inner_subset i hi
  let R := chartNormalSecondJet (H ∘ (A.chart i).symm) ((A.chart i) x)
  obtain ⟨ξ, hunit, hbest⟩ := best_phase_maximum_attainment hdim R
  have hξ : ξ ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hunit
    exact zero_ne_one hunit
  have hinj : Function.Injective (covectorRestriction R ξ) := by
    apply (covector_restriction_bound hdim R ξ).2.2.mp
    rw [hbest]
    exact hphase i _ ((A.chart i).map_source hx)
  exact ⟨ξ.comp (initializationChartTangentEquiv (A.chart i) (hA.chart_mem i) x hx).toContinuousLinearMap,
    initialization_goodCovector_of_chart H hH (A.chart i) (hA.chart_mem i) x hx ξ hξ hinj⟩

end GlobalEmbedding.Initialization
