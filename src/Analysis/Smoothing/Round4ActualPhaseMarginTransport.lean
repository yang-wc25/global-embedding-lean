import Smoothing.Round4ActualChartMarginTransport

/-! The coordinate restricted margin applies to the actual original phase
whose germ is the frozen linear coordinate covector. Its literal mfderiv,
its literal kernel, and the actual true second form occur in the conclusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle Filter
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance phaseTransportRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance phaseTransportSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The true differential of the same frozen linear phase is the genuine
chart pullback of its fixed covector. Equality is supplied by an open germ. -/
theorem round4_actual_linear_phase_covector_eq_chart
    (psi : M → ℝ) (chart : OpenPartialHomeomorph M D)
    (hchart : chart ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set D) (hO : IsOpen O) (hOt : O ⊆ chart.target) (x : D) (hx : x ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x))
    (xi : D →L[ℝ] ℝ) (hphase : ∀ z ∈ O, psi (chart.symm z) = xi z) :
    (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (chart.symm x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (chart.symm x)) =
      xi.comp (mfderiv 𝓙 𝓙 chart (chart.symm x)) := by
  let c : D → M := chart.symm
  let A : D →L[ℝ] TangentSpace 𝓙 (c x) := mfderiv 𝓙 𝓙 c x
  let H : TangentSpace 𝓙 (c x) →L[ℝ] D := mfderiv 𝓙 𝓙 chart (c x)
  let d : TangentSpace 𝓙 (c x) →L[ℝ] ℝ :=
    (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (c x))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) psi (c x))
  have hc : MDifferentiableAt 𝓙 𝓙 c x :=
    (actual_increment_maximal_chart_mdifferentiable chart hchart).mdifferentiableAt_symm (hOt hx)
  have heq : psi ∘ c =ᶠ[𝓝 x] (xi : D → ℝ) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hx) hphase
  have hp : fderiv ℝ (psi ∘ c) x = xi := heq.fderiv_eq.trans xi.fderiv
  have hm := mfderiv_comp x hpsi hc
  rw [mfderiv_eq_fderiv, hp] at hm
  have hchain : d.comp A = xi := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L => tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (c x))
      (L ((tangentSpaceCastModel 𝓙 x).symm v))) hm
    change xi v = d (A v) at h
    exact h.symm
  have hAH : A.comp H = ContinuousLinearMap.id ℝ (TangentSpace 𝓙 (c x)) := by
    ext v
    exact (actualIncrementChartDerivativeEquiv chart hchart x (hOt hx)).apply_symm_apply v
  change d = xi.comp H
  calc
    d = d.comp (A.comp H) := by rw [hAH, ContinuousLinearMap.comp_id]
    _ = (d.comp A).comp H := rfl
    _ = _ := by rw [hchain]

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "X" => Ep × D
variable [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance phaseTransportTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance phaseTransportTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance phaseTransportTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

/-- The actual uniform-template coordinate operator yields the original
restricted true-second-form margin for the SAME phase, including its exact
kernel norm and the explicit inverse-chart differential loss. -/
theorem round4_actual_coordinate_margin_to_phase
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (psi : Ep → M → ℝ) (xi : D →L[ℝ] ℝ)
    (hphase : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = xi z.2)
    (z : X) (hz : z ∈ O)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hInverse : ‖(actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 (hcoord z hz)).toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤
      ‖covectorRestriction (round4ActualPhaseOperatorInChart F e z) xi w‖) :
    let dpsi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
      (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
    ∀ w : SymmetricSquare dpsi.ker, (eta/C)*‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) dpsi w‖ := by
  let slice := fun p => {x : D | (p,x) ∈ O}
  have hs : IsOpen (slice z.1) := hO.preimage (continuous_const.prodMk continuous_id)
  have hd := round4_actual_linear_phase_covector_eq_chart (psi z.1) (e z.1) (he z.1)
    (slice z.1) hs (fun x hx => hcoord (z.1,x) hx) z.2 hz hpsi xi
    (fun x hx => hphase (z.1,x) hx)
  intro dpsi
  let Margin := fun a : TangentSpace 𝓙 ((e z.1).symm z.2) →L[ℝ] ℝ =>
    ∀ w : SymmetricSquare a.ker, (eta/C)*‖w‖ ≤
      ‖covectorRestriction (trueSecondFormL (F z.1) (hF z.1) ((e z.1).symm z.2)) a w‖
  change Margin dpsi
  exact Eq.mpr (congrArg Margin hd)
    (round4_actual_coordinate_margin_to_intrinsic F hF e he O hO hJoint z hz
      (hcoord z hz) xi eta C heta hC hInverse hmargin)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_coordinate_margin_to_phase
