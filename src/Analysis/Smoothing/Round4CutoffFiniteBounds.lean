import Smoothing.ParameterTotalFiniteGeometry
import Smoothing.TensorLocalNormalizationBounds

/-!
# Explicit finite raw-geometry costs for the actual cutoff normalization

The earlier normalization providers chose an entire numerical profile from an
existence theorem. That does not prove that their selected low-order entries
ignore the high-order input entries. Here every profile is an explicit finite
expression; the only scalar choice is a bound for a fixed scalar function on
a compact interval determined by the zeroth-order input. The estimates remain
about the literal cutoffs and their literal chart representatives.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Explicit own-chart to receiving-chart cost at one derivative order. -/
def round4ChartTransferProfile (B T : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * (∑ k ∈ Finset.range (j + 1), B k) *
    bufferedTransitionPrefix T j ^ j

theorem round4ChartTransferProfile_nonneg {B T : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (j : ℕ) :
    0 ≤ round4ChartTransferProfile B T j :=
  mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hB k))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT j)) j)

theorem round4ChartTransferProfile_congr_prefix {B₁ B₂ T₁ T₂ : ℕ → ℝ} (j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) (hT : ∀ a ≤ j, T₁ a = T₂ a) :
    round4ChartTransferProfile B₁ T₁ j = round4ChartTransferProfile B₂ T₂ j := by
  unfold round4ChartTransferProfile
  rw [parameterTransitionPrefix_congr j hT]
  congr 2
  exact Finset.sum_congr rfl fun a ha => hB a (by simpa using ha)

/-- The local support multiplicity, never the cardinality of the atlas. -/
def round4SquareSumProfile (D : ℕ) (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  (D : ℝ) * bufferedCutoffSquareConstant B j

theorem round4SquareSumProfile_nonneg (D : ℕ) {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (j : ℕ) : 0 ≤ round4SquareSumProfile D B j :=
  mul_nonneg (Nat.cast_nonneg _) (bufferedCutoffSquareConstant_nonneg hB j)

theorem round4SquareSumProfile_congr_prefix (D j : ℕ) {B₁ B₂ : ℕ → ℝ}
    (hB : ∀ a ≤ j, B₁ a = B₂ a) :
    round4SquareSumProfile D B₁ j = round4SquareSumProfile D B₂ j := by
  unfold round4SquareSumProfile
  rw [parameterCutoffSquareConstant_congr_prefix j hB]

/-- This scalar choice reads exactly C0, not an infinite input profile. -/
def round4ReciprocalScalarBound (C0 : ℝ) : ℕ → ℝ :=
  Classical.choose (exists_reciprocalSquareRoot_derivative_bounds C0)

theorem round4ReciprocalScalarBound_nonneg (C0 : ℝ) (j : ℕ) :
    0 ≤ round4ReciprocalScalarBound C0 j :=
  (Classical.choose_spec (exists_reciprocalSquareRoot_derivative_bounds C0)).1 j

theorem round4ReciprocalScalarBound_spec (C0 : ℝ) (j k : ℕ) (hkj : k ≤ j)
    (s : ℝ) (hs : s ∈ Icc 1 (max 1 C0)) :
    ‖iteratedFDeriv ℝ k reciprocalSquareRoot s‖ ≤ round4ReciprocalScalarBound C0 j :=
  (Classical.choose_spec (exists_reciprocalSquareRoot_derivative_bounds C0)).2 j k hkj s hs

def round4ReciprocalProfile (C : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * round4ReciprocalScalarBound (C 0) j *
    bufferedTransitionPrefix C j ^ j

theorem round4ReciprocalProfile_nonneg {C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (j : ℕ) : 0 ≤ round4ReciprocalProfile C j :=
  mul_nonneg (mul_nonneg (by positivity) (round4ReciprocalScalarBound_nonneg _ _))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hC j)) j)

theorem round4ReciprocalProfile_congr_prefix {C₁ C₂ : ℕ → ℝ} (j : ℕ)
    (hC : ∀ a ≤ j, C₁ a = C₂ a) :
    round4ReciprocalProfile C₁ j = round4ReciprocalProfile C₂ j := by
  unfold round4ReciprocalProfile
  rw [hC 0 (Nat.zero_le j), parameterTransitionPrefix_congr j hC]

def round4NormalizationProfile (B C : ℕ → ℝ) : ℕ → ℝ :=
  tensorProductJetConstant B (round4ReciprocalProfile C)

theorem round4NormalizationProfile_nonneg {B C : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (hC : ∀ j, 0 ≤ C j) (j : ℕ) :
    0 ≤ round4NormalizationProfile B C j :=
  tensorProductJetConstant_nonneg hB (round4ReciprocalProfile_nonneg hC) j

theorem round4NormalizationProfile_congr_prefix {B₁ B₂ C₁ C₂ : ℕ → ℝ} (j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) (hC : ∀ a ≤ j, C₁ a = C₂ a) :
    round4NormalizationProfile B₁ C₁ j = round4NormalizationProfile B₂ C₂ j := by
  apply parameterTensorProductConstant_congr_prefix j hB
  intro a ha
  exact round4ReciprocalProfile_congr_prefix a fun k hk => hC k (hk.trans ha)

section ActualCharts
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]

/-- The actual chart germ supplies the explicit finite transfer cost. -/
theorem round4_actual_chart_pullback_jet_bound
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (b : X → ℝ) (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (p q : OpenPartialHomeomorph X E)
    (hp : p ∈ maximalAtlas 𝓘(ℝ, E) ∞ X) (hq : q ∈ maximalAtlas 𝓘(ℝ, E) ∞ X)
    (y : E) (hy : y ∈ (p.symm.trans q).source)
    (hown : ∀ k, ‖iteratedFDeriv ℝ k (b ∘ q.symm) (q (p.symm y))‖ ≤ B k)
    (htrans : ∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k (q ∘ p.symm) y‖ ≤ T k)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (b ∘ p.symm) y‖ ≤ round4ChartTransferProfile B T j := by
  have hg : ContDiffOn ℝ ∞ (b ∘ q.symm) q.target :=
    (hb.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hq)).contDiffOn
  rw [(actualChartPullback_eventuallyEq_transition b p q y hy).iteratedFDeriv ℝ j |>.eq_of_nhds]
  exact parameter_general_composition_jet_le T hT
    (p.symm.trans q).open_source q.open_target
    (contDiffOn_actualChartTransition p q hp hq) hg (fun _ hz => q.map_source hz.2)
    hy j (∑ k ∈ Finset.range (j + 1), B k)
    (fun k hk => (hown k).trans (Finset.single_le_sum (fun a _ => hB a) (by simpa using hk)))
    (fun k hk _ => htrans k hk)
end ActualCharts

section NativeBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A direct bound for the literal reciprocal-square-root composition. -/
theorem round4_reciprocal_composition_jet_bound
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (S : E → ℝ) (O : Set E) (hO : IsOpen O) (hS : ContDiffOn ℝ ∞ S O)
    (hpos : ∀ x ∈ O, 1 ≤ S x)
    (hbound : ∀ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ k S x‖ ≤ C k)
    (j : ℕ) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (reciprocalSquareRoot ∘ S) x‖ ≤ round4ReciprocalProfile C j := by
  have hupper : S x ≤ max 1 (C 0) := by
    have hzero := hbound 0 x hx
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le zero_lt_one (hpos x hx))] at hzero
    exact hzero.trans (le_max_right _ _)
  exact parameter_general_composition_jet_le C hC hO isOpen_Ioi hS
    reciprocalSquareRoot_contDiffOn (fun y hy => lt_of_lt_of_le zero_lt_one (hpos y hy))
    hx j (round4ReciprocalScalarBound (C 0) j)
    (fun k hk => round4ReciprocalScalarBound_spec (C 0) j k hk (S x) ⟨hpos x hx,hupper⟩)
    (fun k _ _ => hbound k x hx)

variable {X : Type*} [TopologicalSpace X]

/-- Native square-sum jets with the explicit multiplicity-only cost. -/
theorem round4_square_sum_jet_bound
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (D : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → X → ℝ) (c : E → X) (O : Set E)
    (hO : IsOpen O) (hb : ∀ i, ContDiffOn ℝ ∞ (b i ∘ c) O)
    (x : E) (hx : x ∈ O) (hc : ContinuousAt c x)
    (hD : (activeCutoffIndices b (c x)).card ≤ D)
    (hbound : ∀ i, c x ∈ tsupport (b i) → ∀ k,
      ‖iteratedFDeriv ℝ k (b i ∘ c) x‖ ≤ B k) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ c) x‖ ≤ round4SquareSumProfile D B j := by
  classical
  let A := activeCutoffIndices b (c x)
  have hsum : iteratedFDeriv ℝ j (squareCutoffSum b ∘ c) x =
      ∑ i, iteratedFDeriv ℝ j (fun y => b i (c y)^2) x := by
    apply iteratedFDeriv_fun_sum_apply
    intro i _
    exact (((hb i).pow 2).contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have hinactive (i : ι) (hi : i ∉ A) :
      iteratedFDeriv ℝ j (fun y => b i (c y)^2) x = 0 := by
    have hi' : c x ∉ tsupport (b i) := by simpa [A] using hi
    have hz : (fun y => b i (c y)^2) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hi').comp_tendsto hc] with y hy
      change b i (c y) = 0 at hy
      simp only [hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simpa using (hz.iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (fun y => b i (c y)^2) x) =
      ∑ i ∈ A, iteratedFDeriv ℝ j (fun y => b i (c y)^2) x :=
    (Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => hinactive i hi)).symm
  rw [hsum,hfiltered]
  calc
    ‖∑ i ∈ A, iteratedFDeriv ℝ j (fun y => b i (c y)^2) x‖ ≤
        ∑ i ∈ A, ‖iteratedFDeriv ℝ j (fun y => b i (c y)^2) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ A, bufferedCutoffSquareConstant B j := by
      apply Finset.sum_le_sum
      intro i hi
      have hbi (k : ℕ) : ‖iteratedFDeriv ℝ k (b i ∘ c) x‖ ≤ B k * (1 : ℝ)^k := by
        simpa only [one_pow,mul_one] using
          hbound i ((mem_activeCutoffIndices b (c x) i).1 hi) k
      simpa only [one_pow,mul_one,bufferedCutoffSquareConstant,Function.comp_apply] using
        norm_iteratedFDeriv_sq_le B hB 1 zero_le_one (b i ∘ c) O hO (hb i) x hx hbi j
    _ = (A.card : ℝ) * bufferedCutoffSquareConstant B j := by simp
    _ ≤ round4SquareSumProfile D B j :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (bufferedCutoffSquareConstant_nonneg hB j)

/-- Normalize the same native numerator and denominator, with a finite cost. -/
theorem round4_normalized_cutoff_jet_bound
    (B C : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hC : ∀ j, 0 ≤ C j)
    {ι : Type*} [Fintype ι] (b : ι → E → ℝ) (O : Set E) (hO : IsOpen O)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) O)
    (hpos : ∀ x ∈ O, 1 ≤ squareCutoffSum b x)
    (hden : ∀ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ k (squareCutoffSum b) x‖ ≤ C k)
    (i : ι) (hnum : ∀ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ k (b i) x‖ ≤ B k)
    (j : ℕ) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (squareNormalizedCutoff b i) x‖ ≤ round4NormalizationProfile B C j := by
  have hS : ContDiffOn ℝ ∞ (squareCutoffSum b) O := ContDiffOn.sum (fun a _ => (hb a).pow 2)
  have hrec : ContDiffOn ℝ ∞ (reciprocalSquareRoot ∘ squareCutoffSum b) O :=
    reciprocalSquareRoot_contDiffOn.comp hS (fun y hy => lt_of_lt_of_le zero_lt_one (hpos y hy))
  exact tensor_scalar_product_jet_le B (round4ReciprocalProfile C) hB
    (round4ReciprocalProfile_nonneg hC) hO (hb i) hrec hx j
    (fun k => hnum k x hx)
    (fun k => round4_reciprocal_composition_jet_bound C hC (squareCutoffSum b) O hO hS hpos hden k x hx)

end NativeBounds

#print axioms round4_actual_chart_pullback_jet_bound
#print axioms round4_square_sum_jet_bound
#print axioms round4_normalized_cutoff_jet_bound
#print axioms round4NormalizationProfile_congr_prefix
end
end GlobalEmbedding.Continuation
