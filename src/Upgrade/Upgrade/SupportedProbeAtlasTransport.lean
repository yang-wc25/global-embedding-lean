import Upgrade.ProbeInterface
import GlobalEmbedding.Paper.SymmetricSquareLinearMapEquality
import GlobalEmbedding.Paper.SymmetricSquareMapComposition
import GlobalEmbedding.Paper.SymmetricSquareMapIdentity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Actual atlas inverse frames and fixed base-point normalization

The probe estimates use the inverse differential of a selected buffered atlas
chart. That differential need not be the identity at the packet center. We
construct its actual inverse equivalence from maximal-atlas compatibility and
normalize by the fixed inverse at the center. The resulting source frame is
exactly the identity there. Transporting the already differentiated probe
response through the fixed symmetric-square operator retains every remainder,
with a fixed operator-norm multiplier and no fast-angle differentiation.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Smooth maximal-atlas membership supplies the actual two-sided
differentiability needed for the chart differential equivalence. -/
theorem probeAtlasChart_mdifferentiable
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count) :
    (A.chart i).MDifferentiable IM IM := by
  constructor
  · intro z hz
    exact (contMDiffAt_of_mem_maximalAtlas (hA.chart_mem i) hz).mdifferentiableAt
      (by simp) |>.mdifferentiableWithinAt
  · intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz).mdifferentiableAt
      (by simp) |>.mdifferentiableWithinAt

/-- This is the actual inverse derivative of the chosen atlas chart. -/
def probeAtlasInverseFrameEquiv
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) : E ≃L[ℝ] E :=
  ((probeAtlasChart_mdifferentiable A hA i).mfderiv hx).symm

/-- No frame is guessed: the equivalence has exactly the `probeAtlasFrame`
operator appearing in the original probe response estimate. -/
theorem probeAtlasInverseFrameEquiv_toContinuousLinearMap
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) :
    (probeAtlasInverseFrameEquiv A hA i x hx).toContinuousLinearMap = probeAtlasFrame A i x := by
  ext v
  rfl

/-- The source frame used by the provider is genuinely invertible at every
point in a specified support, using exactly the actual support containment. -/
theorem probeAtlasFrame_bijective_on_support
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ A.support i) : Function.Bijective (probeAtlasFrame A i x) := by
  rw [← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x (hA.support_subset i hx)]
  exact (probeAtlasInverseFrameEquiv A hA i x (hA.support_subset i hx)).bijective

/-- Fixed normalization on the right preserves the actual varying source
frame. Only the factor at the selected center is held constant. -/
def probeAtlasNormalizedFrame
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) : E →L[ℝ] E :=
  (probeAtlasFrame A i z).comp
    (probeAtlasInverseFrameEquiv A hA i x hx).symm.toContinuousLinearMap

theorem probeAtlasNormalizedFrame_self
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) :
    probeAtlasNormalizedFrame A hA i x hx x = ContinuousLinearMap.id ℝ E := by
  rw [probeAtlasNormalizedFrame,
    ← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx]
  apply ContinuousLinearMap.ext
  intro v
  exact (probeAtlasInverseFrameEquiv A hA i x hx).apply_symm_apply v

/-- Every actual normalized frame is still an equivalence on the source. -/
theorem probeAtlasNormalizedFrame_bijective
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ (A.chart i).source) :
    Function.Bijective (probeAtlasNormalizedFrame A hA i x hx z) := by
  have hframe : Function.Bijective (probeAtlasFrame A i z) := by
    rw [← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i z hz]
    exact (probeAtlasInverseFrameEquiv A hA i z hz).bijective
  exact hframe.comp (probeAtlasInverseFrameEquiv A hA i x hx).symm.bijective

/-- The normalized frame's actual equivalence, for the original support
transport dictionary. Both derivatives are those of the same smooth chart. -/
def probeAtlasNormalizedFrameEquiv
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ (A.chart i).source) :
    E ≃L[ℝ] E :=
  (probeAtlasInverseFrameEquiv A hA i x hx).symm.trans
    (probeAtlasInverseFrameEquiv A hA i z hz)

theorem probeAtlasNormalizedFrameEquiv_toContinuousLinearMap
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M) (hz : z ∈ (A.chart i).source) :
    (probeAtlasNormalizedFrameEquiv A hA i x hx z hz).toContinuousLinearMap =
      probeAtlasNormalizedFrame A hA i x hx z := by
  unfold probeAtlasNormalizedFrame
  rw [← probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i z hz]
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- The fixed original-quotient operator through which provider responses
are transported after differentiation. It does not depend on parameters,
the current source point, or any fast angle. -/
def probeAtlasNormalizationSquare
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) : SymmetricSquare E →L[ℝ] SymmetricSquare E :=
  LinearMap.toContinuousLinearMap (symmetricSquareLinearMap
    (probeAtlasInverseFrameEquiv A hA i x hx).symm.toLinearMap)

/-- The new normalized expression is exactly the old provider expression
postcomposed with the one fixed square operator; source variation is retained. -/
theorem probeTensorInFrame_normalized
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (z : M)
    (B : SymmetricSquare E →L[ℝ] V) :
    probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) B =
      (probeTensorInFrame (probeAtlasFrame A i z) B).comp
        (probeAtlasNormalizationSquare A hA i x hx) := by
  apply ContinuousLinearMap.ext
  intro q
  change B (symmetricSquareLinearMap
      ((probeAtlasFrame A i z).comp
        (probeAtlasInverseFrameEquiv A hA i x hx).symm.toContinuousLinearMap).toLinearMap q) =
    B (symmetricSquareLinearMap (probeAtlasFrame A i z).toLinearMap
      (symmetricSquareLinearMap (probeAtlasInverseFrameEquiv A hA i x hx).symm.toLinearMap q))
  have he : symmetricSquareLinearMap
      (probeAtlasInverseFrameEquiv A hA i x hx).symm.toLinearMap =
        symmetricSquareMap
          (probeAtlasInverseFrameEquiv A hA i x hx).symm.toContinuousLinearMap :=
    symmetric_square_linear_map_eq _
  rw [symmetric_square_linear_map_eq, symmetric_square_linear_map_eq, he,
    symmetricSquareMap_comp]

/-- Normalization makes the packet-center leading tensor literally the
original native tensor, without falsely identifying an arbitrary atlas frame
with the identity. -/
theorem probeTensorInFrame_normalized_self
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (B : SymmetricSquare E →L[ℝ] V) :
    probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx x) B = B := by
  rw [probeAtlasNormalizedFrame_self]
  apply ContinuousLinearMap.ext
  intro q
  change B (symmetricSquareLinearMap (ContinuousLinearMap.id ℝ E).toLinearMap q) = B q
  rw [symmetric_square_linear_map_eq, symmetricSquareMap_id]

section ParameterDerivative
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Native parameter differentiation through a fixed target operator. This
is used for the original fixed normal projection after source normalization. -/
theorem fderiv_fixed_tensor_left_transport
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (C : P → X →L[ℝ] Y) {u : P} (hC : DifferentiableAt ℝ C u)
    (J : Y →L[ℝ] Z) (d : P) :
    fderiv ℝ (fun v ↦ J.comp (C v)) u d = J.comp (fderiv ℝ C u d) := by
  let L : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Z) :=
    (ContinuousLinearMap.compL ℝ X Y Z) J
  have hder := (L.hasFDerivAt.comp u hC.hasFDerivAt).fderiv
  exact congrArg (fun T : P →L[ℝ] (X →L[ℝ] Z) ↦ T d) hder

/-- Native differentiation commutes with this fixed right source transport.
In applications K is the actual `probeAtlasNormalizationSquare`. -/
theorem fderiv_fixed_tensor_right_transport
    (C : P → X →L[ℝ] Y) {u : P} (hC : DifferentiableAt ℝ C u)
    (K : X →L[ℝ] X) (d : P) :
    fderiv ℝ (fun v ↦ (C v).comp K) u d = (fderiv ℝ C u d).comp K := by
  let L : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Y) :=
    (ContinuousLinearMap.compL ℝ X X Y).flip K
  have hder := (L.hasFDerivAt.comp u hC.hasFDerivAt).fderiv
  exact congrArg (fun T : P →L[ℝ] (X →L[ℝ] Y) ↦ T d) hder

/-- The complete differentiated remainder survives source normalization with
its fixed norm multiplier. No endpoint or tail term is dropped. -/
theorem fixed_tensor_right_transport_error
    (C : P → X →L[ℝ] Y) {u : P} (hC : DifferentiableAt ℝ C u)
    (K : X →L[ℝ] X) (d : P) (a : ℝ) (T : X →L[ℝ] Y) :
    ‖fderiv ℝ (fun v ↦ (C v).comp K) u d - a • T.comp K‖ ≤
      ‖fderiv ℝ C u d - a • T‖ * ‖K‖ := by
  rw [fderiv_fixed_tensor_right_transport C hC K d]
  have heq : (fderiv ℝ C u d).comp K - a • T.comp K =
      (fderiv ℝ C u d - a • T).comp K := by
    ext v
    rfl
  rw [heq]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end ParameterDerivative

#print axioms probeAtlasChart_mdifferentiable
#print axioms probeAtlasInverseFrameEquiv
#print axioms probeAtlasInverseFrameEquiv_toContinuousLinearMap
#print axioms probeAtlasFrame_bijective_on_support
#print axioms probeAtlasNormalizedFrame_self
#print axioms probeAtlasNormalizedFrame_bijective
#print axioms probeAtlasNormalizedFrameEquiv
#print axioms probeAtlasNormalizedFrameEquiv_toContinuousLinearMap
#print axioms probeTensorInFrame_normalized
#print axioms probeTensorInFrame_normalized_self
#print axioms fderiv_fixed_tensor_right_transport
#print axioms fderiv_fixed_tensor_left_transport
#print axioms fixed_tensor_right_transport_error

end GlobalEmbedding.Upgrade
