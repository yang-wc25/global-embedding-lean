import GlobalEmbedding.Offline.ActualHessianJet
import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth actual spatial Hessians of a jointly smooth probe family

Only the spatial variable is differentiated. The derivatives are the native
derivatives of each actual slice, identified with restrictions of the joint
derivative by the native chain rule. This is a geometric consumer of joint
smoothness, not a construction of the probe family or its remainders.
-/

noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section FirstDerivative
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual spatial derivative is the joint derivative on the actual
vertical source subspace. Parameters are held fixed before differentiating. -/
theorem actual_spatial_fderiv_eq_joint
    (f : P × X → Y) {z : P × X} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x ↦ f (z.1, x)) z.2 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ P X) := by
  exact (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv

/-- The native parameter derivative of the same actual family is the joint
derivative restricted to horizontal directions. No angular column
coefficients are differentiated in this identity. -/
theorem actual_parameter_fderiv_eq_joint
    (f : P × X → Y) {z : P × X} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun u ↦ f (u, z.2)) z.1 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ P X) := by
  exact (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)).fderiv

/-- Restriction to the actual parameter slice preserves differentiability. -/
theorem actual_parameter_differentiableAt
    (f : P × X → Y) {z : P × X} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun u ↦ f (u, z.2)) z.1 :=
  (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)).differentiableAt

/-- Joint smoothness gives joint smoothness of the actual slice derivative
on the same open product-space domain. No partial derivative is supplied. -/
theorem contDiffOn_actual_spatial_fderiv
    {Ω : Set (P × X)} (hΩ : IsOpen Ω) {f : P × X → Y}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2) Ω := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω := hf.fderiv_of_isOpen hΩ (by simp)
  have hV := hD.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inr ℝ P X))
  apply hV.congr
  intro z hz
  exact actual_spatial_fderiv_eq_joint f
    ((hf.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))

/-- Iterating the proved spatial derivative identity retains the actual
second spatial derivative of each slice, while preserving parameter smoothness. -/
theorem contDiffOn_actual_spatial_second_fderiv
    {Ω : Set (P × X)} (hΩ : IsOpen Ω) {f : P × X → Y}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fderiv ℝ (fun x ↦ f (z.1, x))) z.2) Ω := by
  exact contDiffOn_actual_spatial_fderiv hΩ (contDiffOn_actual_spatial_fderiv hΩ hf)

end FirstDerivative

section HessianJet
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- The literal original-quotient Hessian jet of the actual slices is jointly
smooth, via the already accepted continuous linear Hessian descent. -/
theorem contDiffOn_actual_spatial_hessianJet
    {Ω : Set (P × X)} (hΩ : IsOpen Ω) {f : P × X → Y}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (fun z ↦ coordinateHessianJet (fun x ↦ f (z.1, x)) z.2) Ω := by
  exact (actualHessianLift (E := X) (F := Y)).contDiff.comp_contDiffOn
    (contDiffOn_actual_spatial_second_fderiv hΩ hf)

end HessianJet

#print axioms actual_spatial_fderiv_eq_joint
#print axioms actual_parameter_fderiv_eq_joint
#print axioms actual_parameter_differentiableAt
#print axioms contDiffOn_actual_spatial_fderiv
#print axioms contDiffOn_actual_spatial_second_fderiv
#print axioms contDiffOn_actual_spatial_hessianJet

end GlobalEmbedding.Upgrade
