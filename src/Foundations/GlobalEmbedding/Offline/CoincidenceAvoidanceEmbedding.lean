import GlobalEmbedding.Offline.UniformDiagonalSeparation
import GlobalEmbedding.Paper.InducedMetric
import GlobalEmbedding.Targets.FiniteParameterAvoidance
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# From actual coincidence rank to a parameter giving an embedding

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`thm:upgrade`, the final value-coincidence avoidance and compact-source embedding
step; original node `upgrade-remove-value-coincidences`.

This consumer uses the original accepted `finite_parameter_avoidance` on the
actual difference of the two values of the same family. It does not construct the
probe family or its joint derivative rank. Those are genuine remaining provider
obligations. The final theorem combines this consumer with the preceding actual
immersion/finite-atlas diagonal separation, rather than assuming the perturbed
map is injective.

This is an isolated offline candidate, not an original target acceptance receipt.
-/

noncomputable section

open Filter Function Manifold Set MeasureTheory
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

/-- The actual value-coincidence equation, in the existing scalar coordinates of
the original Euclidean target. Both source values of the same family are kept.
Source: `thm:upgrade`, final value-coincidence equation. -/
def euclideanCoincidenceMap {p N : ℕ} {M : Type*}
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N)) :
    (Fin p → ℝ) × (M × M) → Fin N → ℝ :=
  fun z ↦ EuclideanSpace.equiv (Fin N) ℝ (G z.1 z.2.1 - G z.1 z.2.2)

/-- The actual coincidence equation vanishes exactly at equal family values.
Proof: the existing scalar-coordinate map is a linear equivalence.
Source: `thm:upgrade`, the value-incidence zero set. -/
theorem euclideanCoincidenceMap_eq_zero_iff {p N : ℕ} {M : Type*}
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (z : (Fin p → ℝ) × (M × M)) :
    euclideanCoincidenceMap G z = 0 ↔ G z.1 z.2.1 = G z.1 z.2.2 := by
  change EuclideanSpace.equiv (Fin N) ℝ (G z.1 z.2.1 - G z.1 z.2.2) = 0 ↔ _
  rw [← (EuclideanSpace.equiv (Fin N) ℝ).map_zero]
  rw [(EuclideanSpace.equiv (Fin N) ℝ).injective.eq_iff, sub_eq_zero]

/-- Equality of the ORIGINAL actual induced metrics preserves injectivity of the
actual manifold differential, point by point.

Proof: a nonzero difference of tangent vectors has strictly positive `γ(f)(v,v)`
by the original metric positivity theorem. If the `g` differential identifies the
vectors, `γ(g)(v,v)=0`, contradicting the exact equality. Smoothness is not needed
for this algebraic consequence of the total `mfderiv` definition.
Source: `thm:upgrade`, preservation of immersion under exact metric repair. -/
theorem immersion_of_inducedMetric_eq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (f g : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hmetric : GlobalEmbedding.Paper.inducedMetric (I := I) g x =
      GlobalEmbedding.Paper.inducedMetric (I := I) f x)
    (hinj : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)) :
    Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) g x) := by
  intro v w hvw
  by_contra hne
  have hvwne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos := GlobalEmbedding.Paper.inducedMetric_pos_of_injective_mfderiv f x hinj hvwne
  have hzero : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) g x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hmetriczero : GlobalEmbedding.Paper.inducedMetric (I := I) g x (v - w) (v - w) = 0 := by
    simp only [GlobalEmbedding.Paper.inducedMetric_apply, hzero, map_zero]
  rw [hmetric] at hmetriczero
  exact (ne_of_gt hpos) hmetriczero

section AvoidanceConsumer

variable {p N : ℕ} {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [SecondCountableTopology M]

local instance pairChartedSpace : ChartedSpace (E × E) (M × M) :=
  prodChartedSpace E M E M

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [SecondCountableTopology M] in
/-- Joint smoothness of the SAME original family implies joint smoothness of its
actual two-value difference on the parameter domain. Both evaluations are
composed with native smooth product projections, subtracted, and passed through
the existing Euclidean scalar-coordinate equivalence.
Source: `thm:upgrade`, actual coincidence-map smoothness. -/
theorem contMDiffOn_euclideanCoincidenceMap
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N)) (P : Set (Fin p → ℝ))
    (hG : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (P ×ˢ Set.univ)) :
    ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ) ∞
      (euclideanCoincidenceMap G) (P ×ˢ Set.univ) := by
  have hpairfst : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (Prod.fst : M × M → M) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hpairsnd : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (Prod.snd : M × M → M) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hfirst : ContMDiff
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E)) ∞
      (fun z : (Fin p → ℝ) × (M × M) ↦ (z.1, z.2.1)) :=
    contMDiff_fst.prodMk (hpairfst.comp contMDiff_snd)
  have hsecond : ContMDiff
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E)) ∞
      (fun z : (Fin p → ℝ) × (M × M) ↦ (z.1, z.2.2)) :=
    contMDiff_fst.prodMk (hpairsnd.comp contMDiff_snd)
  have hleft := hG.comp (hfirst.contMDiffOn (s := P ×ˢ Set.univ))
    (fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩)
  have hright := hG.comp (hsecond.contMDiffOn (s := P ×ˢ Set.univ))
    (fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩)
  have hdiff := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap.contMDiff.comp_contMDiffOn
    (hleft.sub hright)
  exact hdiff

/-- The original finite-parameter avoidance theorem removes every actual
off-diagonal-neighborhood coincidence of one family for some parameter in any
given nonempty open parameter domain.

The rank condition is on the actual joint manifold derivative of the actual
two-value difference and only at relevant coincidences. Its lower bound is
strictly larger than the real dimension of the pair source. No existence of a
good parameter, nullity conclusion, or injectivity is assumed.

Proof: apply the accepted `finite_parameter_avoidance` to the relevant incidence
set `{(u,x,y) | u∈P, (x,y)∉V, G(u,x)=G(u,y)}`. Its parameter projection is null;
a nonempty open Euclidean parameter set has positive Lebesgue volume, hence is
not contained in that projection. Source: `upgrade-remove-value-coincidences`.
-/
theorem exists_parameter_without_offDiagonal_coincidences
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (P : Set (Fin p → ℝ)) (hP : IsOpen P) (hPne : P.Nonempty)
    (V : Set (M × M))
    (hD : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      𝓘(ℝ, Fin N → ℝ) ∞
      (euclideanCoincidenceMap G) (P ×ˢ Set.univ))
    {k : ℕ} (hdim : 2 * Module.finrank ℝ E < k)
    (hrank : ∀ z : (Fin p → ℝ) × (M × M),
      z.1 ∈ P → z.2 ∉ V → G z.1 z.2.1 = G z.1 z.2.2 →
      k ≤ Module.finrank ℝ (LinearMap.range
        (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
          (euclideanCoincidenceMap G) z).toLinearMap)) :
    ∃ u ∈ P, ∀ x y, (x, y) ∉ V → G u x ≠ G u y := by
  let : IsManifold 𝓘(ℝ, E × E) ∞ (M × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (n := ∞) M M
  let R : Set ((Fin p → ℝ) × (M × M)) :=
    {z | z.1 ∈ P ∧ z.2 ∉ V ∧ G z.1 z.2.1 = G z.1 z.2.2}
  have hnull : volume (Prod.fst '' R) = 0 := by
    apply GlobalEmbedding.Paper.finite_parameter_avoidance
      (a := 2 * Module.finrank ℝ E) (E := E × E)
      (by simp [Module.finrank_prod, two_mul]) P hP (euclideanCoincidenceMap G)
      hD R
      (fun z hz ↦ ⟨hz.1, (euclideanCoincidenceMap_eq_zero_iff G z).mpr hz.2.2⟩)
      hdim
    intro z hz
    exact hrank z hz.1 hz.2.1 hz.2.2
  have hnot : ¬ P ⊆ Prod.fst '' R := by
    intro hsub
    exact (hP.measure_pos volume hPne).ne' (measure_mono_null hsub hnull)
  obtain ⟨u, huP, huBad⟩ := Set.not_subset.mp hnot
  refine ⟨u, huP, ?_⟩
  intro x y hxy hcoin
  exact huBad ⟨(u, x, y), ⟨huP, hxy, hcoin⟩, rfl⟩

/-- If the already constructed fixed diagonal neighborhood is separated by the
family, actual off-diagonal coincidence rank produces a closed embedding.

Proof: select a parameter by the preceding application of the original avoidance
theorem, split every pair according to membership in the SAME `V`, and combine
injectivity with compactness and continuity using native
`Continuous.isClosedEmbedding`. The next theorem discharges this local-separation
input using the original finite-atlas `C¹` norm. Source: the last paragraph of
`thm:upgrade`. -/
theorem exists_closedEmbedding_of_offDiagonal_rank
    [CompactSpace M]
    (G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N))
    (P : Set (Fin p → ℝ)) (hP : IsOpen P) (hPne : P.Nonempty)
    (V : Set (M × M))
    (hG : ∀ u ∈ P, Continuous (G u))
    (hlocal : ∀ u ∈ P, ∀ x y, (x, y) ∈ V → G u x = G u y → x = y)
    (hD : ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E))
      𝓘(ℝ, Fin N → ℝ) ∞
      (euclideanCoincidenceMap G) (P ×ˢ Set.univ))
    {k : ℕ} (hdim : 2 * Module.finrank ℝ E < k)
    (hrank : ∀ z : (Fin p → ℝ) × (M × M),
      z.1 ∈ P → z.2 ∉ V → G z.1 z.2.1 = G z.1 z.2.2 →
      k ≤ Module.finrank ℝ (LinearMap.range
        (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, Fin N → ℝ)
          (euclideanCoincidenceMap G) z).toLinearMap)) :
    ∃ u ∈ P, Topology.IsClosedEmbedding (G u) := by
  obtain ⟨u, huP, havoid⟩ :=
    exists_parameter_without_offDiagonal_coincidences G P hP hPne V hD hdim hrank
  refine ⟨u, huP, (hG u huP).isClosedEmbedding ?_⟩
  intro x y hxy
  by_cases hv : (x, y) ∈ V
  · exact hlocal u huP x y hv hxy
  · exact (havoid x y hv hxy).elim

end AvoidanceConsumer

section PaperNormEndpoint

open GlobalEmbedding.Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [CompactSpace M]

local instance coordinatePairChartedSpace :
    ChartedSpace ((Fin n → ℝ) × (Fin n → ℝ)) (M × M) :=
  prodChartedSpace (Fin n → ℝ) M (Fin n → ℝ) M

/-- A fixed compact immersion supplies a finite ORIGINAL componentwise atlas
`C¹` tolerance and the SAME diagonal neighborhood such that any jointly smooth
same-metric parameter family satisfying that tolerance and the actual
off-diagonal coincidence rank bound contains a smooth immersive closed embedding.

The family, its exact metric identity, and its actual joint rank remain provider
hypotheses: they are precisely the missing probe/rank construction in the upgrade
argument, and this theorem does not claim to prove them. The conclusion's global
injectivity and derivative injectivity are both derived. In particular this does
not mistake a smooth topological embedding for an immersion.

Proof: use `exists_paperAtlasC1_uniform_diagonal_separation` for the native chart
norm control, derive joint smoothness of the actual coincidence map from the
same family, apply the already accepted original avoidance theorem and positive
volume of the open parameter domain, and obtain a closed embedding by compactness.
Exact equality of the actual induced metrics then gives differential injectivity.
Source: the final avoidance/embedding consumer of `thm:upgrade`.
-/
theorem exists_paperAtlasC1_sameMetric_embedding_criterion
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (hinj : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x)) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ delta : ℝ, ∃ V : Set (M × M),
      0 < delta ∧
      (∀ x, 0 < r x ∧ Metric.closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) (r x) ⊆
        interior (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target) ∧
      IsOpen V ∧ Set.diagonal M ⊆ V ∧
      (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧ IsCompact Vᶜ ∧
      (∀ z ∈ Vᶜ, z.1 ≠ z.2) ∧
      ∀ (p : ℕ) (P : Set (Fin p → ℝ)), IsOpen P → P.Nonempty →
        ∀ G : (Fin p → ℝ) → M → EuclideanSpace ℝ (Fin N),
        ContMDiffOn ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, Fin n → ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (P ×ˢ Set.univ) →
        (∀ u ∈ P, ∀ x, inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) (G u) x =
          inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) f x) →
        (∀ u ∈ P,
          let e := EuclideanSpace.equiv (Fin N) ℝ
          let cf : centers → (Fin n → ℝ) → Fin N → ℝ :=
            fun x ↦ e ∘ f ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).symm
          let cg : centers → (Fin n → ℝ) → Fin N → ℝ :=
            fun x ↦ e ∘ G u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).symm
          let O : centers → Set (Fin n → ℝ) :=
            fun x ↦ interior (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1).target
          let S : centers → Set (Fin n → ℝ) :=
            fun x ↦ Metric.closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) x.1 x.1) (r x.1)
          (paperAtlasCj 1 (fun x ↦ cg x - cf x) O S).toReal < delta) →
        ∀ k : ℕ, 2 * n < k →
        (∀ z : (Fin p → ℝ) × (M × M), z.1 ∈ P → z.2 ∉ V →
          G z.1 z.2.1 = G z.1 z.2.2 →
          k ≤ Module.finrank ℝ (LinearMap.range
            (mfderiv ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)))
              𝓘(ℝ, Fin N → ℝ) (euclideanCoincidenceMap G) z).toLinearMap)) →
        ∃ u ∈ P,
          ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (G u) ∧
          (∀ x, Function.Injective
            (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (G u) x)) ∧
          Topology.IsClosedEmbedding (G u) ∧
          (∀ x, inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) (G u) x =
            inducedMetric (I := 𝓘(ℝ, Fin n → ℝ)) f x) := by
  obtain ⟨centers, r, delta, V, hdelta, hball, hV, hdiag, hsym, hcompact, hoff, hsep⟩ :=
    exists_paperAtlasC1_uniform_diagonal_separation f hf hinj
  refine ⟨centers, r, delta, V, hdelta, hball, hV, hdiag, hsym, hcompact, hoff, ?_⟩
  intro p P hP hPne G hG hmetric hclose k hdim hrank
  have hsmooth (u : Fin p → ℝ) (hu : u ∈ P) :
      ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (G u) := by
    intro x
    have hat : ContMDiffAt ((𝓘(ℝ, Fin p → ℝ)).prod 𝓘(ℝ, Fin n → ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (Function.uncurry G) (u, x) :=
      hG.contMDiffAt ((hP.prod isOpen_univ).mem_nhds ⟨hu, Set.mem_univ x⟩)
    exact hat.curry_right
  have hlocal (u : Fin p → ℝ) (hu : u ∈ P) :
      ∀ x y, (x, y) ∈ V → G u x = G u y → x = y :=
    (hsep (G u) (hsmooth u hu)).2 (hclose u hu)
  obtain ⟨u, hu, hembed⟩ := exists_closedEmbedding_of_offDiagonal_rank
    G P hP hPne V (fun u hu ↦ (hsmooth u hu).continuous) hlocal
    (contMDiffOn_euclideanCoincidenceMap G P hG)
    (by simpa only [Module.finrank_fin_fun] using hdim) hrank
  exact ⟨u, hu, hsmooth u hu,
    fun x ↦ immersion_of_inducedMetric_eq f (G u) x (hmetric u hu x) (hinj x),
    hembed, hmetric u hu⟩

end PaperNormEndpoint

#print axioms euclideanCoincidenceMap_eq_zero_iff
#print axioms immersion_of_inducedMetric_eq
#print axioms contMDiffOn_euclideanCoincidenceMap
#print axioms exists_parameter_without_offDiagonal_coincidences
#print axioms exists_closedEmbedding_of_offDiagonal_rank
#print axioms exists_paperAtlasC1_sameMetric_embedding_criterion

end GlobalEmbedding.Offline
