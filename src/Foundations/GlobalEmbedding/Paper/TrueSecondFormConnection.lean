import GlobalEmbedding.Paper.TrueSecondFormEvaluation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open Manifold
open scoped TensorProduct ContDiff Topology
namespace GlobalEmbedding.Paper

/-- The actual true second form equals the projected covariant Hessian for every
actual source connection, hence in particular for every torsion-free connection.
Proof: C∞ implies C² at x; use the general-I connection theorem and the proved
product evaluation of the exact quotient map.
Source: `defn:phase`, connection-independence of B_F. -/
theorem trueSecondForm_connection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (V : ∀ z : M, TangentSpace I z)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x) (v : TangentSpace I x) :
    let push : M → EuclideanSpace ℝ (Fin N) := fun z ↦
      tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f z)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f z (V z))
    (normalSpace (I := I) f x).starProjection
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (push x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) push x v) -
        tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x (cov V x v))) =
      (trueSecondForm f hf x (symmetricSquareProduct (TangentSpace I x) v (V x)) :
        EuclideanSpace ℝ (Fin N)) := by
  have hf2 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x :=
    (hf x).of_le (by norm_num)
  simpa only [trueSecondForm_product] using
    (second_form_chart_invariance_general f x hf2).2.2.2 V cov hV v

end GlobalEmbedding.Paper
