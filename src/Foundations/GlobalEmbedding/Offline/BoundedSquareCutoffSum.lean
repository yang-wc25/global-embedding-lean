import GlobalEmbedding.Offline.SquareCutoffNormalization

/-!
# Actual square-sum bounds from local support multiplicity

Source: `literature/parallelizable-stable-plus-one/main.tex`, the colored square
partition in `prop:initialization`, and original node
`initialization-colored-cutoffs-square-partition-bounded-square-sum`.

This file consumes the genuine geometric providers: a uniform bound on the
number of topological supports through a point, unit plateaux covering the
manifold, and actual derivatives of the overlapping cutoffs in the chart being
used. It proves that all other terms have zero jets, so its constants depend on
the overlap bound, never the total number of centers. It does not claim the
uniform normal-coordinate or transition providers have been constructed.

This is an isolated offline candidate, not a main-library acceptance receipt.
-/

noncomputable section

open Function Filter Manifold IsManifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Offline

section Supports

variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

/-- The actual finite set of pre-cutoffs whose topological supports contain
the point. Topological support, rather than mere nonzero value, is essential
when estimating derivatives at boundary points. -/
def activeCutoffIndices (b : ι → X → ℝ) (x : X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i ↦ x ∈ tsupport (b i))

@[simp]
theorem mem_activeCutoffIndices (b : ι → X → ℝ) (x : X) (i : ι) :
    i ∈ activeCutoffIndices b x ↔ x ∈ tsupport (b i) := by
  classical
  simp [activeCutoffIndices]

/-- Near a fixed point, every actually nonzero cutoff belongs to the finite
set of topological supports through that point. Proof: each excluded cutoff is
identically zero on a neighborhood; finitely intersect those neighborhoods.
Source: the local active-multiplicity step of the bounded-square-sum node. -/
theorem eventually_nonzero_mem_activeCutoffIndices (b : ι → X → ℝ) (x : X) :
    ∀ᶠ y in 𝓝 x, ∀ i, b i y ≠ 0 → i ∈ activeCutoffIndices b x := by
  classical
  apply Filter.eventually_all.2
  intro i
  by_cases hi : x ∈ tsupport (b i)
  · exact Filter.Eventually.of_forall (fun _ _ ↦ (mem_activeCutoffIndices b x i).2 hi)
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hi] with y hy
    exact fun h ↦ (h hy).elim

/-- A bound on the actual support multiplicity gives the same bound for the
number of nonzero summands throughout one neighborhood of the point.
Source: the explicit "nonzero near any point" conclusion of the original node. -/
theorem eventually_nonzero_card_le (b : ι → X → ℝ) (x : X) (D : ℕ)
    (hD : (activeCutoffIndices b x).card ≤ D) :
    ∀ᶠ y in 𝓝 x, (Finset.univ.filter (fun i ↦ b i y ≠ 0)).card ≤ D := by
  classical
  filter_upwards [eventually_nonzero_mem_activeCutoffIndices b x] with y hy
  exact (Finset.card_le_card (fun i hi ↦ hy i (Finset.mem_filter.mp hi).2)).trans hD

end Supports

section DerivativeBounds

variable {E X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

/-- Every actual jet of a cutoff pulled back by a map continuous at the point
vanishes if that point is outside its actual topological support. No global
continuity of the coordinate map outside its chart domain is required.

Proof: pull back the genuine zero germ and use locality of native iterated
Fréchet derivatives. Source: eliminating inactive terms in the square sum. -/
theorem iteratedFDeriv_comp_eq_zero_off_tsupport
    (b : X → ℝ) (c : E → X) (x : E) (hc : ContinuousAt c x)
    (hb : c x ∉ tsupport b) (j : ℕ) :
    iteratedFDeriv ℝ j (b ∘ c) x = 0 := by
  have hz : b ∘ c =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hb).comp_tendsto hc
  simpa using (hz.iteratedFDeriv ℝ j).eq_of_nhds

/-- A scale-independent derivative bound for the square of ONE actual
cutoff. The explicit binomial convolution retains the exact scale `K^j`.
Source: the product-rule step of the bounded-square-sum node. -/
theorem norm_iteratedFDeriv_sq_le
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (K : ℝ) (hK : 0 ≤ K)
    (f : E → ℝ) (O : Set E) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (x : E) (hx : x ∈ O)
    (hbound : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ B j * K ^ j) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f y ^ 2) x‖ ≤
      (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B l * B (j - l)) * K ^ j := by
  have hfull (l : ℕ) (a : E → ℝ) :
      iteratedFDerivWithin ℝ l a O x = iteratedFDeriv ℝ l a x :=
    iteratedFDerivWithin_of_isOpen l hO hx
  have hmul := norm_iteratedFDerivWithin_mul_le hf hf hO.uniqueDiffOn hx
    (n := j) (by simp)
  simp only [hfull, ← pow_two] at hmul
  apply hmul.trans
  calc
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l f x‖ *
        ‖iteratedFDeriv ℝ (j - l) f x‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (B l * K ^ l) *
        (B (j - l) * K ^ (j - l)) := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hbound l) (by positivity))
        (hbound (j - l)) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg (hB l) (pow_nonneg hK l)))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hlj : l ≤ j := by simpa using hl
      have hpowers : K ^ l * K ^ (j - l) = K ^ j := by
        rw [← pow_add, Nat.add_sub_of_le hlj]
      calc
        (j.choose l : ℝ) * (B l * K ^ l) * (B (j - l) * K ^ (j - l)) =
          ((j.choose l : ℝ) * B l * B (j - l)) * (K ^ l * K ^ (j - l)) := by ring
        _ = _ := by rw [hpowers]

/-- Uniform actual derivatives of the same finite square sum, with constants
depending on the local overlap bound `D` and the derivative sequence `B`, not
on the size of the finite family.

Only the genuinely active cutoffs need bounds in the chart being used. All
other jets are proved zero from their actual manifold support and continuity
of the chart inverse at the point. Source: the full derivative calculation of
the original bounded-square-sum node, given its transition-provider bounds. -/
theorem exists_squareCutoffSum_bounds_of_multiplicity
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (D : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 0 ≤ K → ∀ (b : ι → X → ℝ) (c : E → X) (O : Set E),
      IsOpen O → (∀ i, ContDiffOn ℝ ∞ (b i ∘ c) O) →
      ∀ x ∈ O, ContinuousAt c x → (activeCutoffIndices b (c x)).card ≤ D →
      (∀ i, c x ∈ tsupport (b i) → ∀ j,
        ‖iteratedFDeriv ℝ j (b i ∘ c) x‖ ≤ B j * K ^ j) →
      ∀ j, ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ c) x‖ ≤ C j * K ^ j := by
  classical
  let Q : ℕ → ℝ := fun j ↦
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B l * B (j - l)
  have hQ (j : ℕ) : 0 ≤ Q j :=
    Finset.sum_nonneg (fun l _ ↦ mul_nonneg (mul_nonneg (by positivity) (hB l)) (hB _))
  refine ⟨fun j ↦ (D : ℝ) * Q j, fun j ↦ mul_nonneg (by positivity) (hQ j), ?_⟩
  intro ι _ K hK b c O hO hb x hx hc hD hbound j
  let A := activeCutoffIndices b (c x)
  have hsum : iteratedFDeriv ℝ j (squareCutoffSum b ∘ c) x =
      ∑ i, iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x := by
    apply iteratedFDeriv_fun_sum_apply
    intro i _
    exact (((hb i).pow 2).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have hinactive (i : ι) (hi : i ∉ A) :
      iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x = 0 := by
    have hi' : c x ∉ tsupport (b i) := by simpa [A] using hi
    have hz : (fun y ↦ b i (c y) ^ 2) =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi').comp_tendsto hc] with y hy
      change b i (c y) = 0 at hy
      simp only [hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simpa using (hz.iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x) =
      ∑ i ∈ A, iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x := by
    exact (Finset.sum_subset (Finset.subset_univ A) (fun i _ hi ↦ hinactive i hi)).symm
  rw [hsum, hfiltered]
  calc
    ‖∑ i ∈ A, iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x‖ ≤
        ∑ i ∈ A, ‖iteratedFDeriv ℝ j (fun y ↦ b i (c y) ^ 2) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ A, Q j * K ^ j := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_iteratedFDeriv_sq_le B hB K hK (b i ∘ c) O hO (hb i) x hx
        (hbound i ((mem_activeCutoffIndices b (c x) i).1 hi)) j
    _ = (A.card : ℝ) * (Q j * K ^ j) := by simp
    _ ≤ (D : ℝ) * (Q j * K ^ j) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (mul_nonneg (hQ j) (pow_nonneg hK j))
    _ = _ := by ring

end DerivativeBounds

section ManifoldEndpoint

variable {E M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual bounded-square-sum conclusion in each genuine smooth chart.
The geometric overlap/transition provider is explicit: at most `D` actual
topological supports at a point, and bounds for the active cutoff derivatives
in the chosen chart. Unit plateaux imply the exact lower bound one; no lower
bound on an abstract replacement denominator is assumed.

The sequence `C` is chosen before `K`, all cutoffs, and all charts. Every
inactive summand is eliminated using its actual zero germ. Empty manifolds and
empty finite families are allowed. Source: the original bounded-square-sum
node, conditional only on the geometric provider inputs stated there. -/
theorem exists_uniform_squareCutoffSum_bounds
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (D : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (ι : Type*) [Fintype ι],
      ∀ (K : ℝ), 1 ≤ K → ∀ (b : ι → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b i)) →
      (∀ x, ∃ i, b i x = 1) →
      (∀ x, (activeCutoffIndices b x).card ≤ D) →
      ∀ e : ι → OpenPartialHomeomorph M E,
      (∀ p, e p ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) →
      (∀ p i j, ∀ y ∈ (e p).target, (e p).symm y ∈ tsupport (b i) →
        ‖iteratedFDeriv ℝ j (b i ∘ (e p).symm) y‖ ≤ B j * K ^ j) →
      (∀ x, 1 ≤ squareCutoffSum b x) ∧
      (∀ x, ∀ᶠ y in 𝓝 x, (Finset.univ.filter (fun i ↦ b i y ≠ 0)).card ≤ D) ∧
      ∀ p j, ∀ y ∈ (e p).target,
        ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ (e p).symm) y‖ ≤ C j * K ^ j := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_squareCutoffSum_bounds_of_multiplicity
    (E := E) (X := M) B hB D
  refine ⟨C, hC, ?_⟩
  intro ι _ K hK b hb hcover hmult e he hactive
  refine ⟨fun x ↦ one_le_squareCutoffSum_of_plateau b x (hcover x),
    fun x ↦ eventually_nonzero_card_le b x D (hmult x), ?_⟩
  intro p j y hy
  have hc : ContinuousAt (e p).symm y := (e p).symm.continuousAt hy
  have hcoord (i : ι) : ContDiffOn ℝ ∞ (b i ∘ (e p).symm) (e p).target :=
    ((hb i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (he p))).contDiffOn
  exact hbound ι K (zero_le_one.trans hK) b (e p).symm (e p).target
    (e p).open_target hcoord y hy hc (hmult _) (fun i hi l ↦ hactive p i l y hy hi) j

end ManifoldEndpoint

#print axioms eventually_nonzero_mem_activeCutoffIndices
#print axioms eventually_nonzero_card_le
#print axioms iteratedFDeriv_comp_eq_zero_off_tsupport
#print axioms norm_iteratedFDeriv_sq_le
#print axioms exists_squareCutoffSum_bounds_of_multiplicity
#print axioms exists_uniform_squareCutoffSum_bounds

end GlobalEmbedding.Offline
