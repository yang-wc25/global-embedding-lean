import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.IsometricMap
import GlobalEmbedding.Paper.Parallelizable
import GlobalEmbedding.Paper.TargetDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Literal conclusion of the original small exact immersion corollary

This definition has no repair supplier, numerical phase reserve, atlas,
frequency, connectedness or nonemptiness field.  Its metric is the actual
native bilinear metric and its image bound is a strict uniform supremum.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold Bundle
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Continuation.RepairClosure
universe uM

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

structure SmallExactImmersionConclusion
    (metric : (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (r : ℝ) (F : M → V) : Prop where
  smooth : ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ F
  exact_metric : inducedMetric (I := 𝓘(ℝ,Es)) F = metric
  immersion : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,Es) 𝓘(ℝ,V) F x)
  phase_regular : PhaseRegular F smooth
  image_bound : (⨆ x : M, ENNReal.ofReal ‖F x‖) < ENNReal.ofReal r

theorem SmallExactImmersionConclusion.isometricMap
    {metric : (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)}
    {r : ℝ} {F : M → V} (h : SmallExactImmersionConclusion metric r F) :
    GlobalEmbedding.Paper.isometricMap metric F := by
  intro x v w
  exact congrArg (fun A => A v w) (congrFun h.exact_metric x)

/-- Empty closed sources need no parameter point and no artificial
nonemptiness assumption. Their actual zero map satisfies every clause. -/
theorem small_exact_immersion_empty [IsEmpty M]
    (metric : (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (r : ℝ) (hr : 0 < r) :
    SmallExactImmersionConclusion metric r (fun _ : M => (0 : V)) := by
  refine { smooth := contMDiff_const
           exact_metric := ?_
           immersion := ?_
           phase_regular := ?_
           image_bound := ?_ }
  · funext x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x
  · simpa using (ENNReal.ofReal_pos.mpr hr)

/-- The complete original corollary, independently stated with only its
original geometric input. There is no repair or initialization producer in
this statement module's imports. -/
def SmallExactImmersionStatement : Prop :=
  ∀ {n : ℕ} {M : Type uM} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
    (_hn : 2 ≤ n)
    (_hpar : IsParallelizable (M := M) 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) n)
    (metric0 : ContMDiffRiemannianMetric 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) : M → Type _))
    (r : ℝ) (_hr : 0 < r),
    ∃ F : M → EuclideanSpace ℝ (Fin (closedAmbientDimension n)),
      SmallExactImmersionConclusion (fun x => (metric0.inner x).toLinearMap₁₂) r F

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.small_exact_immersion_empty
