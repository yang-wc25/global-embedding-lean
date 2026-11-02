import Repair.SourceCollarNovParentNormalizedJets
import Repair.SourceCollarNovParentProduct

/-!
# The same source parents controlled by fixed primitive budgets

The original raw functions are retained literally.  Their derivative and
transition proofs are enlarged to the already fixed input budgets before
the existing parent producer is called.  This avoids any monotonicity
assumption about the noncomputably selected scalar derivative constants.
The resulting parent functions, domains and carriers are unchanged.

The collar radius below reads only the original buffer lower bound and the
first raw derivative upper bound.  Its construction needs no compactness
assumption on an original norm domain.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.SourceCollarsBridge

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Only the proofs of numerical upper bounds change. -/
def rawPreparationWithBounds
    {A : BufferedAtlas M E} {B T C U : ℕ → ℝ} {D Dmax : ℕ}
    (R : TensorRawCutoffPreparation A B T D)
    (hB : ∀ j, B j ≤ C j) (hT : ∀ j, T j ≤ U j) (hD : D ≤ Dmax) :
    TensorRawCutoffPreparation A C U Dmax where
  raw := R.raw
  smooth := R.smooth
  plateau_cover := R.plateau_cover
  inner_support := R.inner_support
  enlarged_support := R.enlarged_support
  degree := R.degree.trans hD
  own_jets := fun i j y hy => (R.own_jets i j y hy).trans (hB j)
  transition_jets := fun p i j hj y hy hs =>
    (R.transition_jets p i j hj y hy hs).trans (hT j)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem rawPreparationWithBounds_same_functions
    {A : BufferedAtlas M E} {B T C U : ℕ → ℝ} {D Dmax : ℕ}
    (R : TensorRawCutoffPreparation A B T D)
    (hB : ∀ j, B j ≤ C j) (hT : ∀ j, T j ≤ U j) (hD : D ≤ Dmax) :
    (rawPreparationWithBounds R hB hT hD).raw = R.raw ∧
    sourceCollarNovParentRaw (rawPreparationWithBounds R hB hT hD) =
      sourceCollarNovParentRaw R ∧
    sourceCollarNovParent (rawPreparationWithBounds R hB hT hD) =
      sourceCollarNovParent R ∧
    sourceCollarNovParentDomain (rawPreparationWithBounds R hB hT hD) =
      sourceCollarNovParentDomain R ∧
    sourceCollarNovParentCarrier (rawPreparationWithBounds R hB hT hD) =
      sourceCollarNovParentCarrier R :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The actual old parent producer, fed the fixed primitive upper budgets. -/
def parentPreparationFromPrimitiveBounds
    {A : BufferedAtlas M E} {B T C U : ℕ → ℝ} {D Dmax : ℕ}
    (hA : IsSmoothBufferedAtlas A) (R : TensorRawCutoffPreparation A B T D)
    (hC : ∀ j, 0 ≤ C j)
    (hB : ∀ j, B j ≤ C j) (hT : ∀ j, T j ≤ U j) (hD : D ≤ Dmax) :
    TensorRawCutoffPreparation A (sourceCollarNovParentRawProfile C) U Dmax :=
  sourceCollarNovParentRawPreparation hA (rawPreparationWithBounds R hB hT hD) hC

theorem parentPreparationFromPrimitiveBounds_raw
    {A : BufferedAtlas M E} {B T C U : ℕ → ℝ} {D Dmax : ℕ}
    (hA : IsSmoothBufferedAtlas A) (R : TensorRawCutoffPreparation A B T D)
    (hC : ∀ j, 0 ≤ C j)
    (hB : ∀ j, B j ≤ C j) (hT : ∀ j, T j ≤ U j) (hD : D ≤ Dmax) :
    (parentPreparationFromPrimitiveBounds hA R hC hB hT hD).raw =
      sourceCollarNovParentRaw R := rfl

/-- All orders of the unchanged parent raw function are paid by the fixed
original upper-budget sequence, without comparing two chosen profiles. -/
theorem parent_raw_jets_from_primitive_bounds
    {A : BufferedAtlas M E} {B T C U : ℕ → ℝ} {D Dmax : ℕ}
    (hA : IsSmoothBufferedAtlas A) (R : TensorRawCutoffPreparation A B T D)
    (hC : ∀ j, 0 ≤ C j)
    (hB : ∀ j, B j ≤ C j) (hT : ∀ j, T j ≤ U j) (hD : D ≤ Dmax)
    (i : Fin A.count) (j : ℕ) (y : E) (hy : y ∈ (A.chart i).target) :
    ‖iteratedFDeriv ℝ j (sourceCollarNovParentRaw R i ∘ (A.chart i).symm) y‖ ≤
      sourceCollarNovParentRawProfile C j :=
  (parentPreparationFromPrimitiveBounds hA R hC hB hT hD).own_jets i j y hy

/-- Constants are selected before the atlas, its count, and the original
raw family; the output controls the same actual normalized parent. -/
theorem uniform_parent_jets_from_primitive_bounds
    (C U : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hU : ∀ j, 0 ≤ U j) (Dmax : ℕ) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
        (B T : ℕ → ℝ) (D : ℕ) (R : TensorRawCutoffPreparation A B T D),
        (∀ j, B j ≤ C j) → (∀ j, T j ≤ U j) → D ≤ Dmax →
        ∀ p i j y, y ∈ (A.chart p).target →
          ‖iteratedFDeriv ℝ j (sourceCollarNovParent R i ∘ (A.chart p).symm) y‖ ≤ K j := by
  obtain ⟨K,hK,hProvider⟩ := sourceCollarNov_parent_uniform_normalized_jets
    (E := E) (M := M) C U hC hU Dmax
  refine ⟨K,hK,?_⟩
  intro A hA B T D R hB hT hD p i j y hy
  exact hProvider A hA (rawPreparationWithBounds R hB hT hD) p i j y hy

/-- A numerical radius chosen from the original buffer and C1 budgets. -/
def primitiveRadius (buffer rawC1 : ℝ) : ℝ := min buffer (1/(8*(rawC1+1)))

theorem primitiveRadius_pos {buffer rawC1 : ℝ}
    (hbuffer : 0 < buffer) (hraw : 0 ≤ rawC1) : 0 < primitiveRadius buffer rawC1 := by
  exact lt_min hbuffer (by positivity)

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem primitiveRadius_le_original
    (A : BufferedAtlas M E) (B : ℕ → ℝ) {buffer rawC1 : ℝ}
    (hbuffer : buffer ≤ A.buffer) (hB : 0 ≤ B 1) (hraw : B 1 ≤ rawC1) :
    primitiveRadius buffer rawC1 ≤ sourceCollarNovParentRadius A B := by
  apply min_le_min hbuffer
  have hdenB : 0 < 8*(B 1+1) := by positivity
  have hdenC : 0 < 8*(rawC1+1) := by nlinarith
  exact (div_le_div_iff₀ hdenC hdenB).2 (by nlinarith)

/-- No produced collar is an input: this is the actual old parent collar
with a radius fixed solely by the original primitive budgets. -/
theorem parent_buffer_from_primitive_bounds
    {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}
    (hA : IsSmoothBufferedAtlas A) (R : TensorRawCutoffPreparation A B T D)
    {buffer rawC1 : ℝ} (hbuffer : buffer ≤ A.buffer)
    (hB : 0 ≤ B 1) (hraw : B 1 ≤ rawC1)
    (i : Fin A.count) (c : E) (hc : c ∈ sourceCollarNovParentCarrier R i) :
    ball c (primitiveRadius buffer rawC1) ⊆ sourceCollarNovParentDomain R i :=
  (ball_subset_ball (primitiveRadius_le_original A B hbuffer hB hraw)).trans
    (sourceCollarNovParent_buffer hA R hB i c hc)

/-- The numerical radius never reads a derivative beyond order one. -/
theorem primitiveRadius_prefix {buffer : ℝ} {B C : ℕ → ℝ}
    (h : ∀ k, k ≤ 1 → B k = C k) :
    primitiveRadius buffer (B 1) = primitiveRadius buffer (C 1) := by
  rw [h 1 le_rfl]

end GlobalEmbedding.Continuation.SourceCollarsBridge

#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.uniform_parent_jets_from_primitive_bounds
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.parent_buffer_from_primitive_bounds
