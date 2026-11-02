import GlobalEmbedding.Offline.BoundedSquareCutoffSum

/-!
# Actual transfer of scaled cutoff bounds through smooth chart transitions

Source: the overlap-transition and bounded-square-sum children of
`initialization-colored-cutoffs-square-partition` in the original DAG.

The uniform transition derivative sequence is an explicit geometric provider
input. The conclusions here are proved with the actual chart maps, actual
iterated Fréchet derivatives, and their actual equalities on overlap germs.
No existence of uniform normal-coordinate data is asserted.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Function Filter Manifold IsManifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the outer map has actual derivative bounds `B_i*K^i` and the coordinate
change has actual scale-independent bounds `T_i`, their composition has actual
bounds `A_j*K^j`. The sequence `A` is chosen before the scale, maps, domains,
or point. Only the nonzero-order transition derivatives are used.

Proof: through order `j`, bound the outer derivatives by
`(sum_{i≤j} B_i)*K^j`, and the `i`-th transition derivative by
`(1+sum_{l≤j} T_l)^i`. Apply the native all-order composition bound. This is
the genuine analytic step needed to transfer the scaled bump estimates.
Source: the second proof step of the original bounded-square-sum node. -/
theorem exists_scaled_composition_derivative_bounds
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (K : ℝ), 1 ≤ K → ∀ (g : F → ℝ) (f : E → F) (U : Set E) (V : Set F),
      IsOpen U → IsOpen V → ContDiffOn ℝ ∞ g V → ContDiffOn ℝ ∞ f U →
      MapsTo f U V → ∀ x ∈ U,
      (∀ i, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ B i * K ^ i) →
      (∀ i, 1 ≤ i → ‖iteratedFDeriv ℝ i f x‖ ≤ T i) →
      ∀ j, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ A j * K ^ j := by
  let P : ℕ → ℝ := fun j ↦ ∑ i ∈ Finset.range (j + 1), B i
  let Q : ℕ → ℝ := fun j ↦ 1 + ∑ i ∈ Finset.range (j + 1), T i
  have hP (j : ℕ) : 0 ≤ P j := Finset.sum_nonneg (fun i _ ↦ hB i)
  have hQ (j : ℕ) : 1 ≤ Q j := by
    dsimp only [Q]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (j + 1)) ↦ hT i)]
  have hBP (j i : ℕ) (hij : i ≤ j) : B i ≤ P j :=
    Finset.single_le_sum (fun l _ ↦ hB l) (by simpa using hij)
  have hTQ (j i : ℕ) (hij : i ≤ j) : T i ≤ Q j := by
    have hle : T i ≤ ∑ l ∈ Finset.range (j + 1), T l :=
      Finset.single_le_sum (fun l _ ↦ hT l) (by simpa using hij)
    dsimp only [Q]
    linarith
  refine ⟨fun j ↦ (j.factorial : ℝ) * P j * Q j ^ j,
    fun j ↦ mul_nonneg (mul_nonneg (by positivity) (hP j))
      (pow_nonneg (zero_le_one.trans (hQ j)) j), ?_⟩
  intro K hK g f U V hU hV hg hf hmap x hx hgBound hfBound j
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hout (i : ℕ) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i g V (f x)‖ ≤ P j * K ^ j := by
    rw [iteratedFDerivWithin_of_isOpen i hV (hmap hx)]
    exact (hgBound i).trans (mul_le_mul (hBP j i hij)
      (pow_le_pow_right₀ hK hij) (pow_nonneg hKnonneg i) (hP j))
  have hin (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f U x‖ ≤ Q j ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hx]
    exact (hfBound i hi).trans ((hTQ j i hij).trans
      (le_self_pow₀ (hQ j) (by omega)))
  have hcomp := norm_iteratedFDerivWithin_comp_le hg hf (n := j) (by simp)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hx hout hin
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hcomp
  exact hcomp.trans_eq (by ring)

end Composition

section ActualCharts

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual chart transition is smooth on its genuine overlap domain.
Proof: compose the native smooth chart with the native smooth inverse chart.
Source: the smoothness premise of the overlap-transition node. -/
theorem contDiffOn_actualChartTransition
    (p q : OpenPartialHomeomorph M E)
    (hp : p ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hq : q ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) :
    ContDiffOn ℝ ∞ (q ∘ p.symm) (p.symm.trans q).source := by
  have hsub : (p.symm.trans q).source ⊆ p.target := fun _ hy ↦ hy.1
  exact ((contMDiffOn_of_mem_maximalAtlas hq).comp
    ((contMDiffOn_symm_of_mem_maximalAtlas hp).mono hsub) (fun _ hy ↦ hy.2)).contDiffOn

omit [NormedSpace ℝ E] [ChartedSpace E M] in
/-- The actual chart representative equals the actual own-chart
representative composed with the actual transition, on a neighborhood of any
point of overlap. Source: transferring native jets rather than substituting an
independently specified derivative family. -/
theorem actualChartPullback_eventuallyEq_transition
    (b : M → ℝ) (p q : OpenPartialHomeomorph M E) (y : E)
    (hy : y ∈ (p.symm.trans q).source) :
    (b ∘ p.symm) =ᶠ[𝓝 y] ((b ∘ q.symm) ∘ (q ∘ p.symm)) := by
  filter_upwards [(p.symm.trans q).open_source.mem_nhds hy] with z hz
  change b (p.symm z) = b (q.symm (q (p.symm z)))
  have hzq : p.symm z ∈ q.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage] using hz.2
  exact congrArg b (q.left_inv hzq).symm

/-- Own-chart derivative bounds and genuine uniform transition derivative
bounds give the mixed-chart bounds used by the finite-overlap square sum.
The constants are independent of scale, cutoff, both charts, and overlap point.

The conclusion is about the SAME actual cutoff pulled back by the chosen
chart. It follows from the preceding actual equality of germs, not from an
assumed equality of derivatives. The transition provider remains explicit.
Source: the analytic transfer in the original bounded-square-sum node. -/
theorem exists_actualChart_cutoff_transfer_bounds
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : M → ℝ),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b →
      ∀ p q : OpenPartialHomeomorph M E,
      p ∈ maximalAtlas 𝓘(ℝ, E) ∞ M → q ∈ maximalAtlas 𝓘(ℝ, E) ∞ M →
      ∀ y ∈ (p.symm.trans q).source,
      (∀ j, ‖iteratedFDeriv ℝ j (b ∘ q.symm) (q (p.symm y))‖ ≤ B j * K ^ j) →
      (∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j (q ∘ p.symm) y‖ ≤ T j) →
      ∀ j, ‖iteratedFDeriv ℝ j (b ∘ p.symm) y‖ ≤ A j * K ^ j := by
  obtain ⟨A, hA, hbound⟩ := exists_scaled_composition_derivative_bounds
    (E := E) (F := E) B T hB hT
  refine ⟨A, hA, ?_⟩
  intro K hK b hb p q hp hq y hy hbBound htBound j
  have hg : ContDiffOn ℝ ∞ (b ∘ q.symm) q.target :=
    (hb.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hq)).contDiffOn
  have hmap : MapsTo (q ∘ p.symm) (p.symm.trans q).source q.target :=
    fun _ hz ↦ q.map_source hz.2
  rw [(actualChartPullback_eventuallyEq_transition b p q y hy).iteratedFDeriv ℝ j |>.eq_of_nhds]
  exact hbound K hK (b ∘ q.symm) (q ∘ p.symm) (p.symm.trans q).source q.target
    (p.symm.trans q).open_source q.open_target hg
    (contDiffOn_actualChartTransition p q hp hq) hmap y hy hbBound htBound j

end ActualCharts

section SquareSumEndpoint

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual bounded-square-sum conclusion now follows directly from
OWN-chart bounds and the original actual transition derivative provider.
No mixed-chart derivative bound or square-sum derivative bound is assumed.

The remaining geometric inputs are precisely the separated-net coverage,
support multiplicity, genuine charts covering their own cutoff supports, and
uniform derivatives of those charts' true transition maps at active overlaps.
The output constants are chosen before the scale, family, or chart choices.
Source: the full bounded-square-sum child after its stated geometric providers.
-/
theorem exists_squareCutoffSum_bounds_from_chartTransitions
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : ι → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b i)) →
      (∀ x, ∃ i, b i x = 1) →
      (∀ x, (activeCutoffIndices b x).card ≤ D) →
      ∀ e : ι → OpenPartialHomeomorph M E,
      (∀ i, e i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) →
      (∀ i, tsupport (b i) ⊆ (e i).source) →
      (∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (b i ∘ (e i).symm) y‖ ≤ B j * K ^ j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (e p).target,
        (e p).symm y ∈ tsupport (b i) →
        ‖iteratedFDeriv ℝ j (e i ∘ (e p).symm) y‖ ≤ T j) →
      (∀ x, 1 ≤ squareCutoffSum b x) ∧
      (∀ x, ∀ᶠ y in 𝓝 x, (Finset.univ.filter (fun i ↦ b i y ≠ 0)).card ≤ D) ∧
      ∀ p j, ∀ y ∈ (e p).target,
        ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ (e p).symm) y‖ ≤ C j * K ^ j := by
  obtain ⟨A, hA, htransfer⟩ := exists_actualChart_cutoff_transfer_bounds
    (E := E) (M := M) B T hB hT
  obtain ⟨C, hC, hsum⟩ := exists_uniform_squareCutoffSum_bounds
    (E := E) (M := M) A hA D
  refine ⟨C, hC, ?_⟩
  intro ι _ K hK b hb hcover hmult e he hsupp hown htrans
  apply hsum ι K hK b hb hcover hmult e he
  intro p i j y hy hi
  have hiSource : (e p).symm y ∈ (e i).source := hsupp i hi
  have hoverlap : y ∈ ((e p).symm.trans (e i)).source := ⟨hy, hiSource⟩
  exact htransfer K hK (b i) (hb i) (e p) (e i) (he p) (he i) y hoverlap
    (fun l ↦ hown i l _ ((e i).map_source hiSource))
    (fun l hl ↦ htrans p i l hl y hy hi) j

/-- The same actual cutoffs now yield a smooth square partition with genuine
uniform derivatives in each own chart. In this endpoint the derivative bounds
for the actual denominator are PROVED from support multiplicity and actual
chart transitions, rather than passed in as a conclusion-shaped premise.

This is the analytic colored-partition construction after the explicit normal
geometry, net, and transition providers. It does not manufacture any of those
geometric providers or assume existence of such charts on every manifold.
Source: scaled-bumps → bounded-square-sum → square-normalization in the DAG.
-/
theorem exists_normalizedCutoff_bounds_from_chartProviders
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : ι → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b i)) →
      (∀ x, ∃ i, b i x = 1) →
      (∀ x, (activeCutoffIndices b x).card ≤ D) →
      ∀ e : ι → OpenPartialHomeomorph M E,
      (∀ i, e i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) →
      (∀ i, tsupport (b i) ⊆ (e i).source) →
      (∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (b i ∘ (e i).symm) y‖ ≤ B j * K ^ j) →
      (∀ p i j, 1 ≤ j → ∀ y ∈ (e p).target,
        (e p).symm y ∈ tsupport (b i) →
        ‖iteratedFDeriv ℝ j (e i ∘ (e p).symm) y‖ ≤ T j) →
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (squareNormalizedCutoff b i)) ∧
      (∀ x, ∑ i, squareNormalizedCutoff b i x ^ 2 = 1) ∧
      (∀ i, Function.support (squareNormalizedCutoff b i) ⊆ Function.support (b i)) ∧
      (∀ i, tsupport (squareNormalizedCutoff b i) ⊆ tsupport (b i)) ∧
      ∀ i j, ∀ y ∈ (e i).target,
        ‖iteratedFDeriv ℝ j (squareNormalizedCutoff b i ∘ (e i).symm) y‖ ≤ A j * K ^ j := by
  obtain ⟨C, hC, hsum⟩ := exists_squareCutoffSum_bounds_from_chartTransitions
    (E := E) (M := M) B T hB hT D
  obtain ⟨A, hA, hnormalize⟩ := exists_uniform_squareNormalizedCutoffs
    (E := E) (M := M) B C hB hC
  refine ⟨A, hA, ?_⟩
  intro ι _ K hK b hb hcover hmult e he hsupp hown htrans
  obtain ⟨hpos, _, hSBound⟩ := hsum ι K hK b hb hcover hmult e he hsupp hown htrans
  exact hnormalize ι K hK b hb hpos e he hown hSBound

end SquareSumEndpoint

#print axioms exists_scaled_composition_derivative_bounds
#print axioms contDiffOn_actualChartTransition
#print axioms actualChartPullback_eventuallyEq_transition
#print axioms exists_actualChart_cutoff_transfer_bounds
#print axioms exists_squareCutoffSum_bounds_from_chartTransitions
#print axioms exists_normalizedCutoff_bounds_from_chartProviders

end GlobalEmbedding.Offline
