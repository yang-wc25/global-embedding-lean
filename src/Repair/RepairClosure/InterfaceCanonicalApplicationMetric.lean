import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import GlobalEmbedding.Paper.InducedMetric

/-!
# Literal scaled target metric for the canonical repair application

The target is exactly T² times the original given smooth metric, viewed
as native bilinear forms. No new auxiliary metric or tangent norm is
installed. These pointwise facts are independent of repair.
-/

noncomputable section
open GlobalEmbedding.Paper Manifold IsManifold Bundle Set Function
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.RepairClosure

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ,Es)

/-- The actual original target T²g as a native tensor. -/
def canonicalScaledMetric
    (g : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _))
    (T : ℝ) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  T^2 • (g.inner x).toLinearMap₁₂

@[simp] theorem canonicalScaledMetric_apply
    (g : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _))
    (T : ℝ) (x : M) (v w : TangentSpace I x) :
    canonicalScaledMetric g T x v w = T^2 * g.inner x v w := rfl

theorem canonicalScaledMetric_isSymm
    (g : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _))
    (T : ℝ) (x : M) : (canonicalScaledMetric g T x).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro v w
  simp only [canonicalScaledMetric_apply, g.symm x w v]

theorem canonicalScaledMetric_pos
    (g : ContMDiffRiemannianMetric I ∞ Es (TangentSpace I : M → Type _))
    (T : ℝ) (hT : 0 < T) (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < canonicalScaledMetric g T x v v :=
  mul_pos (sq_pos_of_pos hT) (g.pos x v hv)

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.canonicalScaledMetric_isSymm
#print axioms GlobalEmbedding.Continuation.RepairClosure.canonicalScaledMetric_pos
