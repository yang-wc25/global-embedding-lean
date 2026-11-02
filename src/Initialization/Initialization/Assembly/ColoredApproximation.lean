import Initialization.Assembly.FullCore
import Initialization.Geometry.PaperReferenceGeometry

/-!
# Complete candidate for the original colored approximation proposition

Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, lines 787–823.

For an arbitrary closed parallelizable n-manifold, n≥2, and an arbitrary
native smooth positive metric, this theorem produces all fixed construction
data and reference reserves before the two real frequencies. Its actual map is
`metricInitializationMap G g f S K T hK`, and its actual scaled atlas is
`initializationAtlas G T hT`. The original component-partial/MAX paper norm is
used explicitly, together with stronger operator-valued Fréchet estimates.

This is an isolated candidate declaration. It does not edit Challenge, register
a target acceptance, or change the original strict progress count of 9/16.
-/

noncomputable section
open Bundle Manifold Set Metric IsManifold
open scoped ContDiff

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Full colored approximation, including the original paper C^j norm.

`ColoredApproximationCore` expands to the actual map's global smoothness and
uniform value bound; the real T⁻¹-scale smooth buffered atlas with compact
enlarged supports covering its inner domains; the uniform support graph degree;
all transition, target-metric and map reference bounds; positive ellipticity;
the true induced-metric error; and, after the internally produced thresholds,
global differential injectivity, actual-map uniform ellipticity, the original
native `PhaseRegular` predicate, and a uniform positive original chart phase
margin. Every one of these fields is proved by `colored_approximation_core`.

The only input hypotheses are n≥2, compactness/Hausdorff smooth-manifold data,
the original parallelizability predicate and the given smooth positive metric.
In particular the desired map, uniform bounds and phase margin are outputs.
No connectedness, nonemptiness, integer-frequency or parameter-sequence
restriction is imposed.
-/
theorem colored_approximation
    (hn : 2 ≤ n)
    (hpar : IsParallelizable (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)) :
    ∃ (G : PreparedCharts M n)
      (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)
      (S : FreeHopfProduct (fun _ : Fin n ↦ G.palette) →
        EuclideanSpace ℝ (Fin (closedAmbientDimension n)))
      (B : InitializationReserves) (R C Rtransition Rmetric : ℕ → ℝ),
      ColoredApproximationCore G g f S B ∧
      (∀ j, 0 < R j ∧ 0 < C j ∧ 0 < Rtransition j ∧ 0 < Rmetric j) ∧
      (∀ (T : ℝ) (hT : 1 ≤ T) (j : ℕ),
        initializationTransitionPaperCjNorm G j T hT ≤ ENNReal.ofReal (Rtransition j) ∧
        initializationTargetMetricPaperCjNorm G g f j T hT ≤ ENNReal.ofReal (Rmetric j)) ∧
      ∀ (K T : ℝ) (hK : 1 ≤ K) (hKT : K ≤ T) (j : ℕ),
        initializationMapPaperCjNorm G g f S j K T hK (hK.trans hKT) ≤
          ENNReal.ofReal (R j) ∧
        initializationMetricPaperCjNorm G g f S j K T hK (hK.trans hKT) ≤
          ENNReal.ofReal (C j * (K⁻¹ + K / T)) := by
  obtain ⟨G, f, S, B, hcore⟩ := colored_approximation_core hn hpar g
  obtain ⟨R, hR, href⟩ :=
    exists_initializationMap_paper_reference_bounds G g f S hcore.selector_smooth
  obtain ⟨C, hC, herr⟩ := exists_initializationMetric_paper_error_bounds
    G g f S hcore.selector_smooth hcore.selector_gram
  obtain ⟨Rtransition, ht, htransition⟩ := exists_initializationTransition_paper_reference_bounds G
  obtain ⟨Rmetric, hm, hmetric⟩ := exists_initializationTargetMetric_paper_reference_bounds G g f
  exact ⟨G, f, S, B, R, C, Rtransition, Rmetric, hcore,
    fun j ↦ ⟨hR j, hC j, ht j, hm j⟩,
    fun T hT j ↦ ⟨htransition T hT j, hmetric T hT j⟩,
    fun K T hK hKT j ↦ ⟨href K T hK hKT j, herr K T hK hKT j⟩⟩

end GlobalEmbedding.Initialization
