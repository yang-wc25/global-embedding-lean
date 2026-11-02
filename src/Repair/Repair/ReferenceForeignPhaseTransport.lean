import Smoothing.Round4OriginalTensorReconstruction
import GlobalEmbedding.Offline.UniformHierarchicalGoodPhases

/-!
# Cross-host hierarchical phases on the actual chart overlap

Source: the uniform phase preparation in the proof of `thm:repair`.
The foreign covector is pulled back by the derivative of the literal
transition `other ∘ host.symm`.  A single hierarchy depends only on the
common covector-ball radius, covector bound and first transition bound.
The result is the original intrinsic `GoodCovector` at the same source
point, for both signs.  No overlap is inferred from local multiplicity.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Bundle
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation

def repairReferenceHierarchy (radius covectorBound transitionBound : ℝ) : ℝ :=
  hierarchicalGoodWeight radius (covectorBound*transitionBound)

theorem repair_reference_hierarchy_gt_one
    {radius covectorBound transitionBound : ℝ}
    (hr : 0 < radius) (hM : 0 ≤ covectorBound) (hT : 0 ≤ transitionBound) :
    1 < repairReferenceHierarchy radius covectorBound transitionBound :=
  hierarchicalGoodWeight_gt_one hr (mul_nonneg hM hT)

theorem repair_reference_foreign_weighted_good
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup V] [Module ℝ V]
    (B : SymmetricSquare E →ₗ[ℝ] V)
    (radius covectorBound transitionBound : ℝ)
    (hr : 0 < radius) (hM : 0 ≤ covectorBound) (hT : 0 ≤ transitionBound)
    (xi eta : E →L[ℝ] ℝ) (transition : E →L[ℝ] E)
    (hxi : ‖xi‖ ≤ covectorBound) (htransition : ‖transition‖ ≤ transitionBound)
    (hball : ∀ zeta : E →L[ℝ] ℝ, ‖zeta-eta‖ < radius →
      LinearSecondFormGoodCovector B zeta.toLinearMap)
    (i j : ℕ) (hij : i < j) :
    let weight := repairReferenceHierarchy radius covectorBound transitionBound
    LinearSecondFormGoodCovector B
      (weight^j • eta + weight^i • (xi.comp transition)).toLinearMap ∧
    LinearSecondFormGoodCovector B
      (weight^j • eta - weight^i • (xi.comp transition)).toLinearMap := by
  have hforeign : ‖xi.comp transition‖ ≤ covectorBound*transitionBound :=
    (xi.opNorm_comp_le transition).trans
      (mul_le_mul hxi htransition (norm_nonneg transition) hM)
  exact ordered_weighted_good_of_uniform_radius B hr (mul_nonneg hM hT)
    (xi.comp transition) eta hforeign hball hij

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

/-- The first transition derivative is precisely the composition of the
two actual chart differentials, on their genuine overlap. -/
theorem repair_reference_actual_transition_derivative
    (host other : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hother : other ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ host.target) (hxo : host.symm x ∈ other.source) :
    fderiv ℝ (other ∘ host.symm) x =
      (mfderiv 𝓙 𝓙 other (host.symm x)).comp
        (mfderiv 𝓙 𝓙 host.symm x) := by
  have hh := mfderiv_comp x
    ((actual_increment_maximal_chart_mdifferentiable other hother).mdifferentiableAt hxo)
    ((actual_increment_maximal_chart_mdifferentiable host hhost).mdifferentiableAt_symm hx)
  rw [mfderiv_eq_fderiv] at hh
  exact hh

/-- Pulling the foreign covector back to the dominant chart and then to
the tangent fiber gives the original foreign covector exactly. -/
theorem repair_reference_foreign_covector_transport
    (host other : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hother : other ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (x : D) (hx : x ∈ host.target) (hxo : host.symm x ∈ other.source)
    (xi : D →L[ℝ] ℝ) :
    (xi.comp (fderiv ℝ (other ∘ host.symm) x)).comp
      (mfderiv 𝓙 𝓙 host (host.symm x)) =
        xi.comp (mfderiv 𝓙 𝓙 other (host.symm x)) := by
  rw [repair_reference_actual_transition_derivative host other hhost hother x hx hxo]
  ext v
  let A := actualIncrementChartDerivativeEquiv host hhost x hx
  have hv : A (A.symm v) = v := A.apply_symm_apply v
  change xi (mfderiv 𝓙 𝓙 other (host.symm x)
      (A (A.symm v))) = xi (mfderiv 𝓙 𝓙 other (host.symm x) v)
  rw [hv]

variable [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance tangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance tangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance tangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "X" => Ep × D

/-- Both actual signed phases are good on the actual overlap.  The radius
is a local template radius and the only foreign-chart cost is the original
transition derivative bound.  Both signs use the SAME hierarchy. -/
theorem repair_reference_actual_cross_host_good
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (host other : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hother : other ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 (host.symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ host.target)
    (hothercoord : host.symm z.2 ∈ other.source)
    (radius covectorBound transitionBound : ℝ)
    (hr : 0 < radius) (hM : 0 ≤ covectorBound) (hT : 0 ≤ transitionBound)
    (xi eta : D →L[ℝ] ℝ) (hxi : ‖xi‖ ≤ covectorBound)
    (htransition : ‖fderiv ℝ (other ∘ host.symm) z.2‖ ≤ transitionBound)
    (hball : ∀ zeta : D →L[ℝ] ℝ, ‖zeta-eta‖ < radius →
      LinearSecondFormGoodCovector
        (round4ActualPhaseOperatorInChart F (fun _ => host) z).toLinearMap zeta.toLinearMap)
    (i j : ℕ) (hij : i < j) :
    let weight := repairReferenceHierarchy radius covectorBound transitionBound
    GoodCovector (F z.1) (hF z.1) (host.symm z.2)
      (weight^j • eta.comp (mfderiv 𝓙 𝓙 host (host.symm z.2)) +
        weight^i • xi.comp (mfderiv 𝓙 𝓙 other (host.symm z.2))) ∧
    GoodCovector (F z.1) (hF z.1) (host.symm z.2)
      (weight^j • eta.comp (mfderiv 𝓙 𝓙 host (host.symm z.2)) -
        weight^i • xi.comp (mfderiv 𝓙 𝓙 other (host.symm z.2))) := by
  intro weight
  have hpair := repair_reference_foreign_weighted_good
    (round4ActualPhaseOperatorInChart F (fun _ => host) z).toLinearMap
    radius covectorBound transitionBound hr hM hT xi eta
    (fderiv ℝ (other ∘ host.symm) z.2) hxi htransition hball i j hij
  have htransport := repair_reference_foreign_covector_transport host other hhost hother
    z.2 hcoord hothercoord xi
  have hp := round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
    O hO hJoint z hz hcoord _ hpair.1
  have hm := round4_actual_coordinate_good_to_intrinsic F hF (fun _ => host) (fun _ => hhost)
    O hO hJoint z hz hcoord _ hpair.2
  constructor
  · convert hp using 1
    ext v
    have hv := congrArg (fun L => L v) htransport
    change xi (fderiv ℝ (other ∘ host.symm) z.2 (mfderiv 𝓙 𝓙 host (host.symm z.2) v)) =
      xi (mfderiv 𝓙 𝓙 other (host.symm z.2) v) at hv
    change weight^j*eta (mfderiv 𝓙 𝓙 host (host.symm z.2) v)+
        weight^i*xi (mfderiv 𝓙 𝓙 other (host.symm z.2) v) =
      weight^j*eta (mfderiv 𝓙 𝓙 host (host.symm z.2) v)+
        weight^i*xi (fderiv ℝ (other ∘ host.symm) z.2 (mfderiv 𝓙 𝓙 host (host.symm z.2) v))
    rw [hv]
  · convert hm using 1
    ext v
    have hv := congrArg (fun L => L v) htransport
    change xi (fderiv ℝ (other ∘ host.symm) z.2 (mfderiv 𝓙 𝓙 host (host.symm z.2) v)) =
      xi (mfderiv 𝓙 𝓙 other (host.symm z.2) v) at hv
    change weight^j*eta (mfderiv 𝓙 𝓙 host (host.symm z.2) v)-
        weight^i*xi (mfderiv 𝓙 𝓙 other (host.symm z.2) v) =
      weight^j*eta (mfderiv 𝓙 𝓙 host (host.symm z.2) v)-
        weight^i*xi (fderiv ℝ (other ∘ host.symm) z.2 (mfderiv 𝓙 𝓙 host (host.symm z.2) v))
    rw [hv]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_foreign_weighted_good
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_transition_derivative
#print axioms GlobalEmbedding.Continuation.repair_reference_foreign_covector_transport
#print axioms GlobalEmbedding.Continuation.repair_reference_actual_cross_host_good
