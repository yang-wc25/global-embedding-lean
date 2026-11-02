import GlobalEmbedding.Paper.IncrementsOriginalDecompositionExtension
import GlobalEmbedding.Paper.IncrementsOriginalReserveInputs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The original symmetric-fiber topology makes every actual linear tensor
functional continuous. Consequently the fixed positive-reserve neighborhood
is an actual open subset of the unchanged native symmetric fiber. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

local instance round3PositiveRawAdd (x : M) :
    AddCommGroup (LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
  LinearMap.addCommGroup

theorem round3_original_symmetric_linear_continuous (x : M)
    (L : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) →ₗ[ℝ] ℝ) :
    let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
    Continuous (fun A : {A : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) // A.IsSymm} => L A.val) := by
  let K := LinearMap.eqLocus (LinearMap.BilinForm.flipHom (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toLinearMap
    (LinearMap.id : Module.End ℝ
      (LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)))
  let _ : AddCommGroup K := Submodule.addCommGroup K
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  let _ : TopologicalSpace K := incrementsOriginalSymmetricEqLocusTopology (n := n) x
  let ev : K →ₗ[ℝ] (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x → ℝ) :=
    { toFun := fun A v w => A.val v w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let _ : IsTopologicalAddGroup K := isTopologicalAddGroup_induced ev.toAddMonoidHom
  let _ : ContinuousSMul ℝ K := continuousSMul_induced ev
  have hevinj : Function.Injective ev := by
    intro A B h
    apply Subtype.ext
    ext v w
    exact congrFun (congrFun h v) w
  let _ : T2Space K := hevinj.isEmbedding_induced.t2Space
  let l : K →ₗ[ℝ] ℝ :=
    { toFun := fun A => L A.val
      map_add' := fun A B => L.map_add A.val B.val
      map_smul' := fun r A => L.map_smul r A.val }
  exact l.continuous_of_finiteDimensional.comp
    (incrementsOriginalSymmetricFiberEqLocusHomeomorph (n := n) x).continuous

def round3OriginalPositiveCone (D : IncrementsOriginalNativeData n d N M P)
    (reserve : ℝ) (p : P) (x : M) :=
  {A : {A : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) // A.IsSymm} |
    ∀ ν, (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
      reserve < D.linearArgument ν p x A.val}

theorem round3_original_positive_cone_open
    (D : IncrementsOriginalNativeData n d N M P) (reserve : ℝ) (p : P) (x : M) :
    @IsOpen _ (incrementsOriginalSymmetricFiberTopology (n := n) x)
      (round3OriginalPositiveCone D reserve p x) := by
  let _ := incrementsOriginalSymmetricFiberTopology (n := n) x
  change IsOpen {A : {A : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) // A.IsSymm} |
    ∀ ν, (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν →
    reserve < D.linearArgument ν p x A.val}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro ν
  by_cases hν : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν
  · simpa only [hν, iInter_true] using
      isOpen_lt continuous_const (round3_original_symmetric_linear_continuous x (D.linearArgument ν p x))
  · simp only [hν, iInter_false, isOpen_univ]

#print axioms round3_original_symmetric_linear_continuous
#print axioms round3_original_positive_cone_open
end GlobalEmbedding.Continuation
