import GlobalEmbedding.Paper.PeriodicFlatTorusLieAddGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Genuine smooth principal period-one torus bundles

Source: `main.tex`, `lem:balanced`, lines371–418. Native trivializations retain the
actual projection, base and action; no global product or section is assumed.
The original flat torus atlas is reused verbatim. Compactness is a separate hypothesis
of the final correction theorem, so the data and local identities also work without it.
-/

noncomputable section

open Set WithLp
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- The same period-one flat torus already used by the actual periodic Holder theory. -/
abbrev PeriodOneTorus (a : ℕ) := PiLp 2 (fun _ : Fin a => AddCircle (1 : ℝ))

local instance periodOneTorusChartedSpace (a : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin a)) (PeriodOneTorus a) :=
  periodicFlatTorusChartedSpace a

local instance periodOneTorusManifold (a : ℕ) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) ∞ (PeriodOneTorus a) :=
  periodic_flat_torus_isManifold a ∞

variable {E H EB HB M B ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace B] [ChartedSpace HB B]

/-- Native equivariant smooth local trivializations of the actual principal torus action.
The torus and action are genuine native data. Every local target is a product only over
its own baseSet; there is no global trivialization. Covering the base also includes the
usual surjectivity requirement, which is proved from these actual trivializations below. -/
structure PrincipalTorusBundle (a : ℕ) (I : ModelWithCorners ℝ E H)
    (J : ModelWithCorners ℝ EB HB) (π : M → B)
    [IsManifold I ∞ M] [IsManifold J ∞ B] [AddAction (PeriodOneTorus a) M] where
  trivialization : ι → Bundle.Trivialization (PeriodOneTorus a) π
  cover_base : ∀ b : B, ∃ i : ι, b ∈ (trivialization i).baseSet
  projection_invariant : ∀ (t : PeriodOneTorus a) (x : M), π (t +ᵥ x) = π x
  smooth_action : ContMDiffVAdd 𝓘(ℝ, EuclideanSpace ℝ (Fin a)) I ∞ (PeriodOneTorus a) M
  equivariant : ∀ (i : ι) (x : M), x ∈ (trivialization i).source →
    ∀ t : PeriodOneTorus a,
      (trivialization i (t +ᵥ x)).2 = (trivialization i x).2 + t
  smooth_trivialization : ∀ i : ι,
    ContMDiffOn I (J.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) ∞
      (trivialization i).toOpenPartialHomeomorph (trivialization i).source
  smooth_inverse : ∀ i : ι,
    ContMDiffOn (J.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin a))) I ∞
      (trivialization i).toOpenPartialHomeomorph.symm (trivialization i).target

namespace PrincipalTorusBundle

variable {a : ℕ} {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ EB HB}
  {π : M → B} [IsManifold I ∞ M] [IsManifold J ∞ B]
  [AddAction (PeriodOneTorus a) M]
  (S : PrincipalTorusBundle (ι := ι) a I J π)

include S

theorem exists_mem_source (x : M) : ∃ i : ι, x ∈ (S.trivialization i).source := by
  obtain ⟨i, hi⟩ := S.cover_base (π x)
  exact ⟨i, (S.trivialization i).mem_source.mpr hi⟩

theorem action_mem_source (i : ι) (x : M) (hx : x ∈ (S.trivialization i).source)
    (t : PeriodOneTorus a) : t +ᵥ x ∈ (S.trivialization i).source := by
  apply (S.trivialization i).mem_source.mpr
  rw [S.projection_invariant]
  exact (S.trivialization i).mem_source.mp hx

/-- Equivariance of the full native chart, including its genuine projection component. -/
theorem action_coord (i : ι) (x : M) (hx : x ∈ (S.trivialization i).source)
    (t : PeriodOneTorus a) :
    S.trivialization i (t +ᵥ x) = (π x, (S.trivialization i x).2 + t) := by
  apply Prod.ext
  · exact ((S.trivialization i).coe_fst (S.action_mem_source i x hx t)).trans
      (S.projection_invariant t x)
  · exact S.equivariant i x hx t

/-- The base cover and genuine full-fiber native targets imply projection surjectivity. -/
theorem projection_surjective : Function.Surjective π := by
  intro b
  obtain ⟨i, hi⟩ := S.cover_base b
  have ht : (b, (0 : PeriodOneTorus a)) ∈ (S.trivialization i).target :=
    (S.trivialization i).mem_target.mpr hi
  exact ⟨(S.trivialization i).toOpenPartialHomeomorph.symm (b, 0),
    (S.trivialization i).proj_symm_apply ht⟩

/-- The actual torus action is free, as follows from native chart equivariance. -/
theorem action_injective (x : M) : Function.Injective (fun t : PeriodOneTorus a => t +ᵥ x) := by
  intro t u h
  obtain ⟨i, hi⟩ := S.exists_mem_source x
  have hh := congrArg (fun y => (S.trivialization i y).2) h
  rw [S.equivariant i x hi t, S.equivariant i x hi u] at hh
  exact add_left_cancel hh

/-- The action is transitive on each actual projection fiber. -/
theorem transitive_fiber {x y : M} (hπ : π x = π y) :
    ∃ t : PeriodOneTorus a, t +ᵥ x = y := by
  obtain ⟨i, hx⟩ := S.exists_mem_source x
  have hy : y ∈ (S.trivialization i).source := by
    apply (S.trivialization i).mem_source.mpr
    rw [← hπ]
    exact (S.trivialization i).mem_source.mp hx
  let t := (S.trivialization i y).2 - (S.trivialization i x).2
  refine ⟨t, ?_⟩
  apply (S.trivialization i).toOpenPartialHomeomorph.injOn (S.action_mem_source i x hx t) hy
  change S.trivialization i (t +ᵥ x) = S.trivialization i y
  rw [S.action_coord i x hx t]
  apply Prod.ext
  · exact hπ.trans ((S.trivialization i).coe_fst hy).symm
  · dsimp [t]
    abel

/-- The projection is genuinely manifold-smooth, derived from its actual local charts. -/
theorem contMDiff_projection : ContMDiff I J ∞ π := by
  intro x
  obtain ⟨i, hi⟩ := S.exists_mem_source x
  have hlocal := ((S.smooth_trivialization i).contMDiffAt
    ((S.trivialization i).open_source.mem_nhds hi)).fst
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(S.trivialization i).open_source.mem_nhds hi] with y hy
  exact ((S.trivialization i).coe_fst hy).symm

/-- Compactness of the original total space implies compactness of the actual base. -/
theorem compactSpace_base [CompactSpace M] : CompactSpace B := by
  constructor
  rw [← Set.range_eq_univ.mpr S.projection_surjective]
  exact isCompact_range S.contMDiff_projection.continuous

end PrincipalTorusBundle

#print axioms PrincipalTorusBundle.action_injective
#print axioms PrincipalTorusBundle.transitive_fiber
#print axioms PrincipalTorusBundle.contMDiff_projection
#print axioms PrincipalTorusBundle.projection_surjective
#print axioms PrincipalTorusBundle.compactSpace_base
#print axioms PrincipalTorusBundle.action_coord

end GlobalEmbedding.Paper
