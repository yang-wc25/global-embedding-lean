import GlobalEmbedding.Paper.CenteredNormalHessian
import GlobalEmbedding.Paper.GeneralChartContDiff
import GlobalEmbedding.Paper.NormalProjectedGeneralMaximalChart
import GlobalEmbedding.Paper.GeneralChartTangentTransport
import GlobalEmbedding.Paper.TangentSectionExtensionGeneral
import GlobalEmbedding.Paper.NormalProjectedCovariantHessianGeneral

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- The true normal coordinate Hessian is a symmetric normal-valued real bilinear map,
independent of every maximal C² chart and equal to the projected covariant Hessian for
every source connection. Every tangent vector admits a C¹ local field representative.

Proof: the centered definition is a real bilinear normal-valued map by construction.
Ordinary C² coordinate regularity gives symmetry of the second derivative. The projected
second-order chain rule proves invariance under every maximal-atlas extended chart;
the actual chart differential transports tangent vectors by the proved transition law.
Tangent-bundle trivializations give C¹ representatives. Differentiating their actual
pushforward leaves the coordinate Hessian plus a tangent term; the connection correction
is another tangent term. Both disappear under the normal projection.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`.
This is the arbitrary-model version: only the actual source manifold is boundaryless.
No nonzero-dimensional, finite-dimensional, connectedness or nonempty restriction is added. -/
theorem second_form_chart_invariance_general
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hf : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 f x) :
    (∀ v w : TangentSpace I x, centeredNormalHessian f x v w = centeredNormalHessian f x w v) ∧
    (∀ (e : OpenPartialHomeomorph M H), e ∈ IsManifold.maximalAtlas I 2 M →
      x ∈ e.source → ∀ v w : TangentSpace I x,
      (normalSpace (I := I) f x).orthogonalProjectionOnto
        (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x)
          (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
            (mfderiv I 𝓘(ℝ, E) (e.extend I) x v))
          (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
            (mfderiv I 𝓘(ℝ, E) (e.extend I) x w))) = centeredNormalHessian f x v w) ∧
    (∀ w : TangentSpace I x, ∃ V : ∀ z : M, TangentSpace I z,
      V x = w ∧ ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x) ∧
    (∀ (V : ∀ z : M, TangentSpace I z)
      (cov : CovariantDerivative I E (TangentSpace I : M → Type _)),
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun z ↦ Bundle.TotalSpace.mk' E z (V z)) x →
      ∀ v : TangentSpace I x,
      let push : M → EuclideanSpace ℝ (Fin N) := fun z ↦
        tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f z)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f z (V z))
      (normalSpace (I := I) f x).starProjection
        (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (push x)
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) push x v) -
          tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x (cov V x v))) =
        (centeredNormalHessian f x v (V x) : EuclideanSpace ℝ (Fin N))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w
    change (normalSpace (I := I) f x).orthogonalProjectionOnto
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)) =
      (normalSpace (I := I) f x).orthogonalProjectionOnto
        (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
          (tangentSpaceCastModel I x w) (tangentSpaceCastModel I x v))
    congr 1
    exact (contDiffAt_general_chart_representative hf).isSymmSndFDerivAt (by norm_num)
      (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)
  · intro e he hx v w
    apply Subtype.ext
    change (normalSpace (I := I) f x).starProjection
      (fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x)
        (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
          (mfderiv I 𝓘(ℝ, E) (e.extend I) x v))
        (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
          (mfderiv I 𝓘(ℝ, E) (e.extend I) x w))) =
      (normalSpace (I := I) f x).starProjection
        (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
          (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w))
    have hh := normal_projected_hessian_general_maximal_chart f x e he hx hf
      (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
        (mfderiv I 𝓘(ℝ, E) (e.extend I) x v))
      (tangentSpaceCastModel 𝓘(ℝ, E) (e.extend I x)
        (mfderiv I 𝓘(ℝ, E) (e.extend I) x w))
    simpa only [general_chart_transition_tangent_transport x e he hx v,
      general_chart_transition_tangent_transport x e he hx w] using hh
  · exact exists_tangent_section_contMDiffAt_general x
  · intro V cov hV v
    exact normal_projected_covariant_hessian_general f x V cov hf hV v

end GlobalEmbedding.Paper
