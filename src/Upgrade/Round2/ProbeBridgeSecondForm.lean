import Round2.ProbeBridgeLegalHessian
import Upgrade.SupportedProbeJointSmooth

/-!
# Native Hessian responses to the same identified true second form

The original probes construction estimates an actual parameter derivative of
the coordinate Hessian. This file computes, from the actual family and the
same normal identification, the derivative demanded by `ExactProbeFamily`.
Both effects of the identification are retained: its zeroth-order error on
the old normal principal column, and its parameter derivative acting on the
actual current Hessian. No incidence rank or desired response formula is a
hypothesis, and no missing repaired probe family is asserted to exist.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section Operators
variable {P S V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A principal response estimate for an actual operator product. The
identification derivative is evaluated on the current Hessian. -/
theorem norm_parameter_identified_operator_response_sub_le
    (Q : P → V →L[ℝ] V) (H : P → S →L[ℝ] V)
    (P₀ : V →L[ℝ] V) (L : S →L[ℝ] V) (u d : P)
    (hQ : DifferentiableAt ℝ Q u) (hH : DifferentiableAt ℝ H u)
    (hQnorm : ‖Q u‖ ≤ 1) (hL : P₀.comp L = L) :
    ‖fderiv ℝ (fun v ↦ (Q v).comp (H v)) u d - L‖ ≤
      ‖fderiv ℝ H u d - L‖ + ‖Q u - P₀‖ * ‖L‖ +
        ‖fderiv ℝ Q u d‖ * ‖H u‖ := by
  rw [fderiv_clm_comp hQ hH]
  change ‖(Q u).comp (fderiv ℝ H u d) +
      (fderiv ℝ Q u d).comp (H u) - L‖ ≤ _
  have heq : (Q u).comp (fderiv ℝ H u d) +
      (fderiv ℝ Q u d).comp (H u) - L =
      ((Q u).comp (fderiv ℝ H u d) - L) +
        (fderiv ℝ Q u d).comp (H u) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (incidence_identification_comparison (Q u) P₀ (fderiv ℝ H u d) L hQnorm hL)
    (ContinuousLinearMap.opNorm_comp_le _ _))

end Operators

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

-- These are Mathlib's unchanged native operator-norm instances. Naming
-- them locally prevents repeated expensive search for nested bilinear maps.
private noncomputable local instance probeBridgeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance probeBridgeBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance probeBridgeBilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) := ContinuousLinearMap.toNormedSpace

/-- The two actual factors in the identified-Hessian expression are
parameter differentiable because the original geometry is jointly smooth.
No differentiability of a separately chosen second-form carrier is assumed. -/
theorem ProbeGeometry.atlas_hessian_parameter_factors_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ
      (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v)
        (g.normalIdentification t v) z) u ∧
    DifferentiableAt ℝ
      (fun v ↦ fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)) u := by
  have hu' : u ∈ Metric.ball 0 g.radius := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨hu', (A.chart i).map_source hz⟩
  have hopen : IsOpen (Metric.ball (0 : ProbeParameters r) g.radius ×ˢ (A.chart i).target) :=
    Metric.isOpen_ball.prod (A.chart i).open_target
  have hFcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)
  have hH := contDiffOn_actual_spatial_second_fderiv hopen hFcoords
  have hQcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
      (g.map t w.1) (g.normalIdentification t w.1) w.2)
    (g.normalIdentification_smooth t ht htt)
  constructor
  · have h := actual_parameter_differentiableAt _
      ((hQcoords.contDiffAt (hopen.mem_nhds hw)).differentiableAt (by simp))
    simpa only [(A.chart i).left_inv hz] using h
  · exact actual_parameter_differentiableAt _
      ((hH.contDiffAt (hopen.mem_nhds hw)).differentiableAt (by simp))

/-- Native differentiation of the SAME identified true form in the actual
atlas inverse frame. The Hessian lift is fixed and continuous linear; the
moving normal identification contributes its genuine parameter derivative. -/
theorem ProbeGeometry.identified_secondForm_parameter_formula
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d =
      (normalIdentificationOperator (n := n) F₀ (g.map t u)
        (g.normalIdentification t u) z).comp
          (actualHessianLift (fderiv ℝ
            (fun v ↦ fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)) u d)) +
      (fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v)
        (g.normalIdentification t v) z) u d).comp (probeAtlasSecondJet A (g.map t u) i z) := by
  obtain ⟨hQ, hH⟩ := g.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz
  let H := fun v : ProbeParameters r ↦
    fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)
  have hL : HasFDerivAt (fun v ↦ actualHessianLift (H v))
      ((actualHessianLift («E» := E) (F := V)).comp (fderiv ℝ H u)) u :=
    (actualHessianLift («E» := E) (F := V)).hasFDerivAt.comp u hH.hasFDerivAt
  have heq : (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) z)) =
      fun v ↦ (normalIdentificationOperator (n := n) F₀ (g.map t v)
        (g.normalIdentification t v) z).comp (actualHessianLift (H v)) := by
    funext v
    exact identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (g.map t v)
      (g.slice_smooth t v) (g.normalIdentification t v) A hA i z hz
  rw [heq]
  exact congrArg
    (fun D : ProbeParameters r →L[ℝ] (SymmetricSquare E →L[ℝ] V) ↦ D d)
    (hQ.hasFDerivAt.clm_comp hL).fderiv

/-- The complete geometric conversion of an actual native bilinear
Hessian response into the exact operator-norm expression required by probes.
Every error on the right is a native error of the same map or identification.
The legal principal tensor and its old-normal projection identity are proved
from the actual wave. -/
theorem ProbeGeometry.identified_secondForm_response_native_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) (wave : LocalLegalWave F₀ hF₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) (coefficient : ℝ) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ ≤
      actualHessianLiftConstant E V *
        ‖fderiv ℝ
          (fun v ↦ fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)) u d -
          coefficient • phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
            (wave.value ∘ (A.chart i).symm) (A.chart i z)‖ +
      ‖normalIdentificationOperator (n := n) F₀ (g.map t u) (g.normalIdentification t u) z -
          (normalSpace (I := IM) F₀ z).starProjection‖ *
        ‖coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ +
      ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v)
          (g.normalIdentification t v) z) u d‖ *
        ‖probeAtlasSecondJet A (g.map t u) i z‖ := by
  obtain ⟨hQ, hH⟩ := g.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz
  let Q := fun v : ProbeParameters r ↦ normalIdentificationOperator (n := n) F₀
    (g.map t v) (g.normalIdentification t v) z
  let H := fun v : ProbeParameters r ↦
    fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)
  let L := coefficient • phaseRankOneHessian (wave.phase ∘ (A.chart i).symm)
    (wave.value ∘ (A.chart i).symm) (A.chart i z)
  let T := coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)
  have hLT : actualHessianLift L = T := by
    dsimp only [L, T]
    rw [map_smul, wave.actualHessianLift_phaseRankOneHessian_in_atlas A hA i z hz]
  have hT : (normalSpace (I := IM) F₀ z).starProjection.comp T = T := by
    dsimp only [T]
    rw [ContinuousLinearMap.comp_smul, wave.normalProjection_comp_tensor_in_frame]
  have hLH : HasFDerivAt (fun v ↦ actualHessianLift (H v))
      ((actualHessianLift («E» := E) (F := V)).comp (fderiv ℝ H u)) u :=
    (actualHessianLift («E» := E) (F := V)).hasFDerivAt.comp u hH.hasFDerivAt
  have hnorm := norm_parameter_identified_operator_response_sub_le Q
    (fun v ↦ actualHessianLift (H v)) (normalSpace (I := IM) F₀ z).starProjection
    T u d hQ hLH.differentiableAt
    (normalIdentificationOperator_norm_le_one F₀ (g.map t u) (g.normalIdentification t u) z) hT
  have hderiv : fderiv ℝ (fun v ↦ actualHessianLift (H v)) u d =
      actualHessianLift (fderiv ℝ H u d) := by
    exact congrArg
      (fun D : ProbeParameters r →L[ℝ] (SymmetricSquare E →L[ℝ] V) ↦ D d) hLH.fderiv
  have hraw : ‖fderiv ℝ (fun v ↦ actualHessianLift (H v)) u d - T‖ ≤
      actualHessianLiftConstant E V * ‖fderiv ℝ H u d - L‖ := by
    rw [hderiv, ← hLT]
    exact actualHessianLift_sub_norm_le _ _
  have heq : (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) z)) =
      fun v ↦ (Q v).comp (actualHessianLift (H v)) := by
    funext v
    exact identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (g.map t v)
      (g.slice_smooth t v) (g.normalIdentification t v) A hA i z hz
  rw [heq]
  exact hnorm.trans (add_le_add (add_le_add hraw le_rfl) le_rfl)

#print axioms norm_parameter_identified_operator_response_sub_le
#print axioms ProbeGeometry.atlas_hessian_parameter_factors_differentiable
#print axioms ProbeGeometry.identified_secondForm_parameter_formula
#print axioms ProbeGeometry.identified_secondForm_response_native_bound

end GlobalEmbedding.Upgrade
