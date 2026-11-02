import Smoothing.ParameterRound2InitialNative

/-!
# Original 440/442 repair initialization on actual compact parameter domains

The reference-induced metric h0 is derived from the actual F0. Genuine
compact coordinate domains prove reference norm finiteness; native joint
smoothness proves h0 regularity. The initial scale is chosen BEFORE hstar,
using only reference derivatives through map442 and tensor440. One positive
C440 target-error threshold then gives the literal G0,H0 initialization with
the original full-joint S440 budget and a C0 neighborhood reserve.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

/-- True fixed-order norm finiteness from compact control, without an added
numerical high-order hypothesis. -/
theorem parameterRound2_paperAtlasCj_finite_of_compact
    {ι : Type*} [Fintype ι] {a q : ℕ}
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ O i) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (j : ℕ) :
    paperAtlasCj j f O S ≠ ⊤ :=
  (paperAtlasCj_ne_top_iff j f O S hO hSO hf).2
    (fun i k _ => parameterRound2_coordinate_jets_bounded_of_compact
      (f i) (O i) (S i) (S i) (hO i) (hS i) Subset.rfl (hSO i) (hf i) k)

variable {n d N pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterRound2InitialCompactChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterRound2InitialCompactIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- A concrete initialization of the original repair data. The target enters
only after t0 and epsilon have been fixed, with its literal C440 error. -/
theorem parameterRound2_exists_original_440_initialization
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (F0 : P × M → Ey) (hF0 : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ F0)
    (budget radius cap : ℝ) (hradius : 0 < radius) (hcap : 0 < cap)
    (hbudget : 4 *
      ((paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart F0)
          (incrementsOriginalDifferentiation A B.chart)
          (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal +
       (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart
          (fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x))
          (incrementsOriginalDifferentiation A B.chart)
          (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal) < budget) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ (1/2 : ℝ) ∧ t0 ≤ cap ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (hstar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart hstar i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
      paperAtlasCj 440 (incrementsOriginalTensorCoordinates A B.chart (fun p x => hstar p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart)
        (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal epsilon →
      let delta := t0 ^ 10
      let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
      let H0 := fun p x => (delta^2)⁻¹ •
        (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G0 (p,y)) x)
      (∀ p x, H0 p x = h0 p x + (delta^2)⁻¹ • (hstar p x-h0 p x)) ∧
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ G0 ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H0 i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B G0 H0 440 t0
        (incrementsOriginalEvaluation A B.chart Omega Q univ) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B G0 H0 440 t0
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ 3 * budget / 4 ∧
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H0 p x-h0 p x))
        (incrementsOriginalDifferentiation A B.chart)
        (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal (radius/2) := by
  let O := incrementsOriginalDifferentiation A B.chart
  let S := incrementsOriginalEvaluation A B.chart Omega Q univ
  let h0 := fun p x => inducedMetric (I := 𝓘(ℝ, Es)) (fun y => F0 (p,y)) x
  let f := incrementsOriginalMapCoordinates A B.chart F0
  let g := incrementsOriginalTensorCoordinates A B.chart h0
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B.chart
  have hS : ∀ i, IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact
    A B.chart Omega Q hOmega hQ hOmegaTarget hQTarget
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    parameterRound2_originalMapCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i) :=
    parameterRound2_inducedMetric_originalCoordinates_contDiffOn A B.chart hA hB F0 hF0
  have hf442 := parameterRound2_paperAtlasCj_finite_of_compact f O S hO hS hSO hf 442
  have hg440 := parameterRound2_paperAtlasCj_finite_of_compact g O S hO hS hSO hg 440
  obtain ⟨t0, ht0, ht01, htcap, href⟩ := parameterRound2_exists_reference_pair_scale
    440 f g O S hf442 hg440 budget (min cap (1/2)) (lt_min hcap (by norm_num)) hbudget
  have ht02 : t0 ≤ 1/2 := htcap.trans (min_le_right _ _)
  have hbudget0 : 0 < budget := lt_of_le_of_lt
    (mul_nonneg (by norm_num) (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) hbudget
  let delta := t0^10
  have hdelta : 0 < delta := pow_pos ht0 _
  have hd2 : 0 < delta^2 := sq_pos_of_pos hdelta
  have hdsmall : delta^2 ≤ 1 := pow_le_one₀ hdelta.le (pow_le_one₀ ht0.le ht01)
  let epsilon := min (delta^2 * (budget/(4*441))) (delta^2 * (radius/2))
  have heps : 0 < epsilon := lt_min (mul_pos hd2 (div_pos hbudget0 (by norm_num)))
    (mul_pos hd2 (div_pos hradius (by norm_num)))
  refine ⟨t0, ht0, ht02, htcap.trans (min_le_left _ _), epsilon, heps, ?_⟩
  intro hstar hstarSmooth
  dsimp only
  intro heBound
  let e := incrementsOriginalTensorCoordinates A B.chart (fun p x => hstar p x-h0 p x)
  have he440 : paperAtlasCj 440 e O S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heBound
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) := fun i => (hstarSmooth i).sub (hg i)
  have hinit := parameterRound2_initial_native_pair A B hA hB S hSO F0 hF0 hstar hstarSmooth
    440 t0 delta ht0.le ht01 hdelta.ne' hdsmall hf442 hg440 he440
  dsimp only at hinit
  refine ⟨hinit.1, hinit.2.1, hinit.2.2.1, hinit.2.2.2.1, ?_, ?_⟩
  · have href0 := href t0 ht0.le le_rfl
    have hWf := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 440 t0 f O S hf442
    have hWg := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 440 t0 g O S (by simpa using hg440)
    have hrefPair : (parameterLocalOriginalTotalPairWeighted A B F0 h0 440 t0 S).toReal ≤ budget/2 := by
      change (paperAtlasWeighted 2 440 t0 f O S + paperAtlasWeighted 0 440 t0 g O S).toReal ≤ _
      rw [ENNReal.toReal_add hWf hWg]
      exact href0
    have heReal : (paperAtlasCj 440 e O S).toReal ≤ epsilon := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top heBound
      simpa only [ENNReal.toReal_ofReal heps.le] using hh
    have hscale : (delta^2)⁻¹ * (441 : ℝ) * epsilon ≤ budget/4 := by
      calc
        _ ≤ (delta^2)⁻¹ * 441 * (delta^2 * (budget/(4*441))) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ = _ := by field_simp
    have herror : (delta^2)⁻¹ * (441 : ℝ) * (paperAtlasCj 440 e O S).toReal ≤ budget/4 :=
      (mul_le_mul_of_nonneg_left heReal (by positivity)).trans hscale
    have hb := hinit.2.2.2.2
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hb
    exact hb.trans (by linarith)
  · let G0 := fun z => Real.sqrt (1-delta^2) • F0 z
    let H0 := fun p x => (delta^2)⁻¹ •
      (hstar p x-inducedMetric (I := 𝓘(ℝ, Es)) (fun y => G0 (p,y)) x)
    have hn : ∀ p x, H0 p x = h0 p x + (delta^2)⁻¹ • (hstar p x-h0 p x) := hinit.1
    have hfieldEq : (fun p x => H0 p x-h0 p x) =
        fun p x => (delta^2)⁻¹ • (hstar p x-h0 p x) := by
      funext p x
      rw [hn]
      abel
    have heq : incrementsOriginalTensorCoordinates A B.chart (fun p x => H0 p x-h0 p x) =
        fun i y => (delta^2)⁻¹ • e i y := by
      rw [hfieldEq]
      rfl
    change paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart (fun p x => H0 p x-h0 p x)) O S ≤ _
    rw [heq]
    have he0 := parameterRound2_paperAtlasCj_mono_order (show 0 ≤ 440 by omega) e O S
    have hes := parameterRound2_paperAtlasCj_smul_le 0 e O S hO hSO he
      (ne_top_of_le_ne_top he440 he0) ((delta^2)⁻¹)
    rw [abs_of_nonneg (inv_nonneg.mpr hd2.le)] at hes
    have hsmall : (delta^2)⁻¹ * epsilon ≤ radius/2 := by
      calc
        _ ≤ (delta^2)⁻¹ * (delta^2 * (radius/2)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
        _ = _ := by field_simp
    calc
      _ ≤ ENNReal.ofReal ((delta^2)⁻¹) * paperAtlasCj 0 e O S := hes
      _ ≤ ENNReal.ofReal ((delta^2)⁻¹) * ENNReal.ofReal epsilon :=
        mul_le_mul_right (he0.trans heBound) _
      _ = ENNReal.ofReal ((delta^2)⁻¹ * epsilon) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsmall

#print axioms parameterRound2_exists_original_440_initialization
end
end GlobalEmbedding.Continuation
