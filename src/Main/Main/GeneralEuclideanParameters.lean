import Main.GeneralExactProbeFamily
import Upgrade.SupportedValueParameterTransport
import Upgrade.SupportedProbeJointSmooth

/-!
# The same full probes on a genuine Euclidean parameter ball

The construction uses the Pi sup norm on (Fin r × Bool) → ℝ. The actual
continuous linear equivalence from Euclidean space has coordinate norm at
most the Euclidean norm; it is not asserted to be an isometry. The Euclidean
ball of the SAME radius lies inside the admitted coordinate ball. Actual
chain rules transport the same map and normal identification, the original
directional estimates, and all four sine/cosine responses.
-/

noncomputable section
open Set Function Filter Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

abbrev EuclideanProbeParameters (r : ℕ) := EuclideanSpace ℝ (Fin r × Bool)

/-- Actual coordinate equivalence, with no isometry claim. -/
abbrev euclideanProbeCoordinates (r : ℕ) :
    EuclideanProbeParameters r ≃L[ℝ] ProbeParameters r :=
  EuclideanSpace.equiv (Fin r × Bool) ℝ

theorem euclideanProbeCoordinates_norm_le {r : ℕ} (u : EuclideanProbeParameters r) :
    ‖euclideanProbeCoordinates r u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro k
  exact PiLp.norm_apply_le u k

theorem euclideanProbeCoordinates_mem_ball {r : ℕ} {radius : ℝ}
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < radius) :
    ‖euclideanProbeCoordinates r u‖ < radius :=
  (euclideanProbeCoordinates_norm_le u).trans_lt hu

/-- Honest Euclidean coordinate direction for one original sine/cosine label. -/
def euclideanProbeDirection {r : ℕ} (l : Fin r) (b : Bool) : EuclideanProbeParameters r :=
  (euclideanProbeCoordinates r).symm (Pi.single (l,b) 1)

@[simp] theorem euclideanProbeCoordinates_direction {r : ℕ} (l : Fin r) (b : Bool) :
    euclideanProbeCoordinates r (euclideanProbeDirection l b) = Pi.single (l,b) 1 :=
  (euclideanProbeCoordinates r).apply_symm_apply _

@[simp] theorem euclideanProbeDirection_apply {r : ℕ} (l : Fin r) (b : Bool)
    (k : Fin r × Bool) :
    euclideanProbeDirection l b k = (Pi.single (l,b) (1:ℝ) : ProbeParameters r) k := rfl

@[simp] theorem euclideanProbeDirection_norm {r : ℕ} (l : Fin r) (b : Bool) :
    ‖euclideanProbeDirection l b‖ = 1 := by
  change ‖(PiLp.single 2 (l,b) (1:ℝ) : EuclideanProbeParameters r)‖ = 1
  simp only [PiLp.norm_single,norm_one]

/-- A generic native chain rule, avoiding any special assumption about the
observable being pulled back to Euclidean parameters. -/
theorem euclideanProbeCoordinates_fderiv_comp
    {r : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ProbeParameters r → W) (u direction : EuclideanProbeParameters r)
    (hf : DifferentiableAt ℝ f (euclideanProbeCoordinates r u)) :
    fderiv ℝ (f ∘ euclideanProbeCoordinates r) u direction =
      fderiv ℝ f (euclideanProbeCoordinates r u) (euclideanProbeCoordinates r direction) := by
  have hcomp := hf.hasFDerivAt.comp u (euclideanProbeCoordinates r).hasFDerivAt
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] using
    congrArg (fun L => L direction) hcomp.fderiv

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Joint smoothness is restricted to the genuine Euclidean ball of the
original radius and composed with the actual fixed coordinate equivalence. -/
theorem euclideanProbeCoordinates_contMDiffOn
    {r : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ProbeParameters r × M → W) (radius : ℝ)
    (hf : ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IM) 𝓘(ℝ,W) ∞ f
      (Metric.ball 0 radius ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ,EuclideanProbeParameters r)).prod IM) 𝓘(ℝ,W) ∞
      (fun z : EuclideanProbeParameters r × M => f (euclideanProbeCoordinates r z.1,z.2))
      (Metric.ball 0 radius ×ˢ univ) := by
  have hchange : ContMDiff ((𝓘(ℝ,EuclideanProbeParameters r)).prod IM)
      ((𝓘(ℝ,ProbeParameters r)).prod IM) ∞
      (fun z : EuclideanProbeParameters r × M => (euclideanProbeCoordinates r z.1,z.2)) :=
    ((euclideanProbeCoordinates r).contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact hf.comp hchange.contMDiffOn (by
    intro z hz
    refine ⟨?_,mem_univ _⟩
    simpa only [Metric.mem_ball,dist_zero_right] using
      euclideanProbeCoordinates_mem_ball z.1
        (show ‖z.1‖ < radius by simpa only [Metric.mem_ball,dist_zero_right] using hz.1))

namespace GeneralExactProbeFamily
variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
  {hF₀ : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F₀}
  {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
  {r : ℕ} {waves : Fin r → OpenSupportedLegalWave F₀ hF₀}

def euclideanMap (d : GeneralExactProbeFamily F₀ hF₀ A waves) :
    ℝ → EuclideanProbeParameters r → M → V :=
  fun t u => d.map t (euclideanProbeCoordinates r u)

def euclideanNormalIdentification (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (u : EuclideanProbeParameters r) (x : M) :
    normalSpace (I := IM) (d.euclideanMap t u) x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x :=
  d.normalIdentification t (euclideanProbeCoordinates r u) x

@[simp] theorem euclideanMap_slice (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (u : EuclideanProbeParameters r) :
    d.euclideanMap t u = d.map t (euclideanProbeCoordinates r u) := rfl

theorem euclideanMap_slice_smooth (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (u : EuclideanProbeParameters r) :
    ContMDiff IM 𝓘(ℝ,V) ∞ (d.euclideanMap t u) :=
  d.slice_smooth t (euclideanProbeCoordinates r u)

theorem euclideanMap_joint_smooth (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold) :
    ContMDiffOn ((𝓘(ℝ,EuclideanProbeParameters r)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry (d.euclideanMap t)) (Metric.ball 0 d.radius ×ˢ univ) := by
  have hchange : ContMDiff ((𝓘(ℝ,EuclideanProbeParameters r)).prod IM)
      ((𝓘(ℝ,ProbeParameters r)).prod IM) ∞
      (fun z : EuclideanProbeParameters r × M => (euclideanProbeCoordinates r z.1,z.2)) :=
    ((euclideanProbeCoordinates r).contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact (d.joint_smooth t ht htt).comp hchange.contMDiffOn (by
    intro z hz
    refine ⟨?_,mem_univ _⟩
    simpa only [Metric.mem_ball,dist_zero_right] using
      euclideanProbeCoordinates_mem_ball z.1
        (show ‖z.1‖ < d.radius by simpa only [Metric.mem_ball,dist_zero_right] using hz.1))

/-- The ambient operator of exactly the same normal identification, composed
with the fixed Euclidean-to-coordinate parameter map. -/
def euclideanNormalOperator (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (u : EuclideanProbeParameters r) (x : M) : V →L[ℝ] V :=
  normalIdentificationOperator (n := n) F₀ (d.map t (euclideanProbeCoordinates r u))
    (d.normalIdentification t (euclideanProbeCoordinates r u)) x

@[simp] theorem euclideanNormalOperator_eq
    (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (u : EuclideanProbeParameters r) (x : M) :
    d.euclideanNormalOperator t u x =
      normalIdentificationOperator (n := n) F₀ (d.euclideanMap t u)
        (d.euclideanNormalIdentification t u) x := rfl

theorem euclideanNormalIdentification_joint_smooth
    (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold) :
    ContMDiffOn ((𝓘(ℝ,EuclideanProbeParameters r)).prod IM) 𝓘(ℝ,V →L[ℝ] V) ∞
      (Function.uncurry (d.euclideanNormalOperator t))
      (Metric.ball 0 d.radius ×ˢ univ) := by
  exact euclideanProbeCoordinates_contMDiffOn
    (fun z : ProbeParameters r × M => normalIdentificationOperator (n := n)
      F₀ (d.map t z.1) (d.normalIdentification t z.1) z.2)
    d.radius (d.normalIdentification_smooth t ht htt)

theorem euclidean_metric (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius) (x : M) :
    inducedMetric (I := IM) (d.euclideanMap t u) x = inducedMetric (I := IM) F₀ x :=
  d.metric t ht htt (euclideanProbeCoordinates r u) (euclideanProbeCoordinates_mem_ball u hu) x

theorem euclidean_closeness (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius) :
    probeAtlasCj A 2 (d.euclideanMap t u-F₀) ≤
      ENNReal.ofReal (d.constant*t^((44:ℝ)/5)) :=
  d.closeness t ht htt (euclideanProbeCoordinates r u) (euclideanProbeCoordinates_mem_ball u hu)

theorem euclidean_spatial_C3 (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius) :
    probeAtlasCj A 3 (d.euclideanMap t u) ≤ ENNReal.ofReal d.constant :=
  d.spatial_C3 t ht htt (euclideanProbeCoordinates r u) (euclideanProbeCoordinates_mem_ball u hu)

/-- Native differentiation in the Euclidean direction is the old native
derivative in its literal scalar coordinate direction. -/
theorem euclideanMap_parameterDerivative (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (direction : EuclideanProbeParameters r) (x : M) :
    fderiv ℝ (fun v => d.euclideanMap t v x) u direction =
      fderiv ℝ (fun v => d.map t v x) (euclideanProbeCoordinates r u)
        (euclideanProbeCoordinates r direction) := by
  have hD := d.toProbeGeometry.value_parameter_differentiable t ht htt
    (euclideanProbeCoordinates r u) (euclideanProbeCoordinates_mem_ball u hu) x
  have hcomp := hD.hasFDerivAt.comp u (euclideanProbeCoordinates r).hasFDerivAt
  simpa only [euclideanMap,Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] using congrArg (fun L => L direction) hcomp.fderiv

theorem euclidean_parameter_C1 (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (direction : EuclideanProbeParameters r) :
    probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => d.euclideanMap t v x) u direction) ≤
      ENNReal.ofReal (d.constant*t^(10:ℕ)*‖direction‖) := by
  have heq := funext (d.euclideanMap_parameterDerivative t ht htt u hu direction)
  rw [heq]
  exact (d.parameter_C1 t ht htt (euclideanProbeCoordinates r u)
    (euclideanProbeCoordinates_mem_ball u hu) (euclideanProbeCoordinates r direction)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (euclideanProbeCoordinates_norm_le direction)
        (mul_nonneg d.constant_nonneg (pow_nonneg ht.le _))))

theorem euclidean_parameter_C2 (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (direction : EuclideanProbeParameters r) :
    probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => d.euclideanMap t v x) u direction) ≤
      ENNReal.ofReal (d.constant*t^((44:ℝ)/5)*‖direction‖) := by
  have heq := funext (d.euclideanMap_parameterDerivative t ht htt u hu direction)
  rw [heq]
  exact (d.parameter_C2 t ht htt (euclideanProbeCoordinates r u)
    (euclideanProbeCoordinates_mem_ball u hu) (euclideanProbeCoordinates r direction)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (euclideanProbeCoordinates_norm_le direction)
        (mul_nonneg d.constant_nonneg (Real.rpow_nonneg ht.le _))))

theorem euclidean_secondForm_parameterDerivative
    (d : GeneralExactProbeFamily F₀ hF₀ A waves) (hA : IsSmoothBufferedAtlas A)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (direction : EuclideanProbeParameters r) (i : Fin A.count) (x : M)
    (hx : x ∈ (A.chart i).source) :
    fderiv ℝ (fun v => probeTensorInFrame (probeAtlasFrame A i x)
      (identifiedTrueSecondForm (n := n) F₀ (d.euclideanMap t v)
        (d.euclideanMap_slice_smooth t v) (d.euclideanNormalIdentification t v) x))
      u direction =
    fderiv ℝ (fun v => probeTensorInFrame (probeAtlasFrame A i x)
      (identifiedTrueSecondForm (n := n) F₀ (d.map t v) (d.slice_smooth t v)
        (d.normalIdentification t v) x))
      (euclideanProbeCoordinates r u) (euclideanProbeCoordinates r direction) := by
  let H : ProbeParameters r → (SymmetricSquare E →L[ℝ] V) := fun v =>
    probeTensorInFrame (probeAtlasFrame A i x)
      (identifiedTrueSecondForm (n := n) F₀ (d.map t v) (d.slice_smooth t v)
        (d.normalIdentification t v) x)
  have hD : DifferentiableAt ℝ H (euclideanProbeCoordinates r u) :=
    d.toProbeGeometry.identified_trueSecondForm_parameter_differentiable
      A hA i t ht htt (euclideanProbeCoordinates r u)
        (euclideanProbeCoordinates_mem_ball u hu) x hx
  change fderiv ℝ (H ∘ euclideanProbeCoordinates r) u direction =
    fderiv ℝ H (euclideanProbeCoordinates r u) (euclideanProbeCoordinates r direction)
  exact euclideanProbeCoordinates_fderiv_comp H u direction hD

/-- Both cosine and sine second-form responses on the entire genuine
Euclidean ball, with the original scale, weights, modulus and constant. -/
theorem euclidean_secondForm_response
    (d : GeneralExactProbeFamily F₀ hF₀ A waves) (hA : IsSmoothBufferedAtlas A)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (l : Fin r) (b : Bool) (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
    ‖fderiv ℝ (fun v => probeTensorInFrame (probeAtlasFrame A i x)
      (identifiedTrueSecondForm (n := n) F₀ (d.euclideanMap t v)
        (d.euclideanMap_slice_smooth t v) (d.euclideanNormalIdentification t v) x))
        u (euclideanProbeDirection l b) -
      (t^((44:ℝ)/5)*probeTrig b (d.weight l*(waves l).phase x/t^((6:ℝ)/5))) •
        probeTensorInFrame (probeAtlasFrame A i x) ((waves l).tensor x)‖ ≤
      t^((44:ℝ)/5)*(d.etaB t+d.constant*‖u‖) := by
  rw [d.euclidean_secondForm_parameterDerivative hA t ht htt u hu
    (euclideanProbeDirection l b) i x (hA.support_subset i hx),
    euclideanProbeCoordinates_direction]
  exact (d.secondForm_response t ht htt (euclideanProbeCoordinates r u)
    (euclideanProbeCoordinates_mem_ball u hu) l b i x hx).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (euclideanProbeCoordinates_norm_le u) d.constant_nonneg))
        (Real.rpow_nonneg ht.le _))

/-- Both cosine and sine value responses on the same Euclidean ball. -/
theorem euclidean_value_response (d : GeneralExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < d.threshold)
    (u : EuclideanProbeParameters r) (hu : ‖u‖ < d.radius)
    (l : Fin r) (b : Bool) (x : M) :
    ‖fderiv ℝ (fun v => d.euclideanMap t v x) u (euclideanProbeDirection l b) -
      (-(t^((56:ℝ)/5))*(d.weight l^2)⁻¹*
        probeTrig b (d.weight l*(waves l).phase x/t^((6:ℝ)/5))) • (waves l).value x‖ ≤
      t^((56:ℝ)/5)*(d.etaV t+d.constant*‖u‖) := by
  rw [d.euclideanMap_parameterDerivative t ht htt u hu (euclideanProbeDirection l b) x,
    euclideanProbeCoordinates_direction]
  exact (d.value_response t ht htt (euclideanProbeCoordinates r u)
    (euclideanProbeCoordinates_mem_ball u hu) l b x).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (euclideanProbeCoordinates_norm_le u) d.constant_nonneg))
        (Real.rpow_nonneg ht.le _))

end GeneralExactProbeFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.euclideanProbeCoordinates_norm_le
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclideanMap_joint_smooth
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclideanNormalIdentification_joint_smooth
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclidean_parameter_C1
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclidean_parameter_C2
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclidean_secondForm_response
#print axioms GlobalEmbedding.Continuation.GeneralExactProbeFamily.euclidean_value_response

