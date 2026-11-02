import Repair.ReferenceSignedReserve
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-!
# Actual slice phases for the native compact-parameter datum

The coordinate operator is the literal original spatial operator.  A
constant dummy parameter only supplies the existing joint chart interface;
the equality with every genuine parameter-family operator is definitional.
Consequently the following constructors apply to arbitrary parameter
manifolds, without a Euclidean-parameter restriction on the final datum.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped ContDiff TensorProduct Topology
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance referenceSliceRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance referenceSliceSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "I" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

def repairReferenceSliceOperator (F : M → V) (host : OpenPartialHomeomorph M D)
    (x : D) : SymmetricSquare D →L[ℝ] V :=
  round4ActualPhaseOperatorInChart (fun (_ : ℝ) => F) (fun _ => host) (0,x)

theorem repair_reference_slice_operator_eq
    {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (F : Ep → M → V) (host : OpenPartialHomeomorph M D) (p : Ep) (x : D) :
    repairReferenceSliceOperator (F p) host x =
      round4ActualPhaseOperatorInChart F (fun _ => host) (p,x) := rfl

theorem repair_reference_slice_joint_smooth
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (fun z : ℝ × D => F (host.symm z.2))
      (Set.univ ×ˢ host.target) := by
  have hf : ContDiffOn ℝ ∞ (F ∘ host.symm) host.target :=
    (hF.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hhost)).contDiffOn
  exact hf.comp contDiffOn_snd (fun _ hz => hz.2)

variable [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance referenceSliceTangentNormed (x : M) : NormedAddCommGroup (TangentSpace I x) := inferInstance
private local instance referenceSliceTangentSpace (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance
private local instance referenceSliceTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace I x) := inferInstance

/-- The actual scalar linear phase has precisely the native chart
covector at every point of the chart source, with no outside derivative. -/
theorem repair_reference_source_linear_covector
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (xi : D →L[ℝ] ℝ) (x : M) (hx : x ∈ host.source) :
    round4HostPhaseCovector host xi x = xi.comp (mfderiv I I host x) := by
  have hh := round4HostPhaseCovector_eq host hhost xi (host x) (host.map_source hx)
  have hx' : host.symm (host x)=x := host.left_inv hx
  exact hx' ▸ hh

variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
    EuclideanSpace ℝ (Fin N)) ×
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

theorem repair_reference_slice_template_good
    (C : UniformActualGoodDictionaryCover K)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (host : OpenPartialHomeomorph M D) (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hx : x ∈ host.source) (index : C.indices)
    (hindex : repairReferenceSliceOperator F host (host x) ∈ (C.template index).operatorDomain)
    (a : EdgePair (Module.finrank ℝ D+1)) :
    GoodCovector F hF x (((C.template index).covectors a).comp (mfderiv I I host x)) := by
  have hg := ((C.template index).operator_control _ hindex a).1
  have hh := round4_actual_coordinate_good_to_intrinsic (fun (_ : ℝ) => F) (fun _ => hF)
    (fun _ => host) (fun _ => hhost) (Set.univ ×ˢ host.target)
    (isOpen_univ.prod host.open_target) (repair_reference_slice_joint_smooth F hF host hhost)
    (0,host x) ⟨mem_univ _,host.map_source hx⟩ (host.map_source hx)
    ((C.template index).covectors a) hg
  have hx' : host.symm (host x)=x := host.left_inv hx
  exact hx' ▸ hh

/-- The complete actual cross-host interaction, in the original tangent
fiber, produced from the fixed numerical template cover and transitions. -/
theorem repair_reference_slice_signed_good
    (C : UniformActualGoodDictionaryCover K) (R transitionBound : ℝ)
    (hT : 0 ≤ transitionBound)
    (F : M → V) (hF : ContMDiff I 𝓘(ℝ,V) ∞ F)
    (host other : OpenPartialHomeomorph M D)
    (hhost : host ∈ IsManifold.maximalAtlas I ∞ M)
    (hother : other ∈ IsManifold.maximalAtlas I ∞ M)
    (x : M) (hx : x ∈ host.source) (hxo : x ∈ other.source)
    (dominant foreign : C.indices)
    (hB : ‖repairReferenceSliceOperator F host (host x)‖ ≤ R)
    (hdom : repairReferenceSliceOperator F host (host x) ∈ (C.template dominant).operatorDomain)
    (a b : EdgePair (Module.finrank ℝ D+1))
    (htransition : ‖fderiv ℝ (other ∘ host.symm) (host x)‖ ≤ transitionBound)
    {i j : ℕ} (hij : i < j) :
    let w := repairReferenceSignedHierarchy C R transitionBound
    GoodCovector F hF x
      (w^j • ((C.template dominant).covectors a).comp (mfderiv I I host x)+
        w^i • ((C.template foreign).covectors b).comp (mfderiv I I other x)) ∧
    GoodCovector F hF x
      (w^j • ((C.template dominant).covectors a).comp (mfderiv I I host x)-
        w^i • ((C.template foreign).covectors b).comp (mfderiv I I other x)) := by
  intro w
  have hball (eta : D →L[ℝ] ℝ)
      (heta : ‖eta-(C.template dominant).covectors a‖ < incrementUniformSignedRadius C R) :
      LinearSecondFormGoodCovector
        (repairReferenceSliceOperator F host (host x)).toLinearMap eta.toLinearMap := by
    exact (increment_uniform_signed_control C R _ hB dominant hdom a eta 1 (by norm_num)
      (by simpa using heta)).1
  have hx' : host.symm (host x)=x := host.left_inv hx
  have hh := repair_reference_actual_cross_host_good (fun (_ : ℝ) => F) (fun _ => hF)
    host other hhost hother (Set.univ ×ˢ host.target)
    (isOpen_univ.prod host.open_target) (repair_reference_slice_joint_smooth F hF host hhost)
    (0,host x) ⟨mem_univ _,host.map_source hx⟩ (host.map_source hx)
    (by simpa only [hx'] using hxo)
    (incrementUniformSignedRadius C R) C.covectorBound transitionBound
    (incrementUniformSignedRadius_pos C R) C.covectorBound_pos.le hT
    ((C.template foreign).covectors b) ((C.template dominant).covectors a)
    ((C.bounds foreign).2.2.2.2 b) htransition hball i j hij
  exact hx' ▸ hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_slice_operator_eq
#print axioms GlobalEmbedding.Continuation.repair_reference_slice_template_good
#print axioms GlobalEmbedding.Continuation.repair_reference_slice_signed_good
