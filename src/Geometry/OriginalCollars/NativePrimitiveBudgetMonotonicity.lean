import OriginalCollars.NativePrimitiveSignedRegion

/-!
# One genuine primitive region survives common numerical aggregation

Only numerical bounds are enlarged or reduced. The original functions,
open domain, carrier, center and phase are untouched. Finite aggregation
uses actual minima and maxima; it introduces no multiplication by a chart
or phase count. Existence of a common budget across a varying class remains
a separate quantified input, rather than a consequence of finiteness.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance primitiveBudgetRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance primitiveBudgetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))

/-- Monotone replacement of primitive numbers preserves the exact region. -/
def NativePrimitiveSignedRegion.weaken
    {Ref : IncrementsOriginalNativeData (m+1) d N M P}
    {i : Fin Ref.atlas.count × Fin Ref.parameterCount}
    {r : ActualSecondarySignedRecord (Fin Ref.primaryCount)}
    {W : Set (Ep × M)} {theta : Ep × M → ℝ}
    {mu R buffer coordinateBound kernel lower nativeTwo : ℝ} {Phase : ℕ → ℝ}
    (region : NativePrimitiveSignedRegion Ref i r W theta mu R buffer coordinateBound kernel lower nativeTwo Phase)
    (mu' R' buffer' coordinateBound' kernel' lower' nativeTwo' : ℝ) (Phase' : ℕ → ℝ)
    (hmu : mu' ≤ mu) (hR : R ≤ R') (hBuffer : buffer' ≤ buffer)
    (hCoordinate : coordinateBound ≤ coordinateBound') (hKernel : kernel' ≤ kernel)
    (hLower : lower' ≤ lower) (hNative : nativeTwo ≤ nativeTwo')
    (hPhase : ∀ j, Phase j ≤ Phase' j) :
    NativePrimitiveSignedRegion Ref i r W theta mu' R' buffer' coordinateBound' kernel' lower' nativeTwo' Phase' where
  domain := region.domain
  center := region.center
  isOpen := region.isOpen
  carrier_radius := region.carrier_radius.trans (closedBall_subset_closedBall hR)
  carrier_buffer := fun z hz => (ball_subset_ball hBuffer).trans (region.carrier_buffer z hz)
  target := region.target
  parent := region.parent
  active := region.active
  inner := region.inner
  native_first := fun z hz v =>
    (mul_le_mul_of_nonneg_right hLower (sq_nonneg ‖v‖)).trans (region.native_first z hz v)
  native_jets := fun k hk z hz => (region.native_jets k hk z hz).trans hNative
  coordinates := fun z hz => (region.coordinates z hz).trans hCoordinate
  phase_smooth := region.phase_smooth
  phase_noncritical := fun z hz => hmu.trans (region.phase_noncritical z hz)
  phase_jets := fun j z hz => (region.phase_jets j z hz).trans (hPhase j)
  original_kernel := fun z hz v =>
    (mul_le_mul_of_nonneg_right hKernel (norm_nonneg v)).trans (region.original_kernel z hz v)

section FiniteBounds
variable {ι : Type*} [Fintype ι]

/-- A strictly positive lower bound for a finite family of positive inputs,
including the empty family. -/
def finitePrimitiveLower (f : ι → ℝ) : ℝ :=
  (insert 1 (Finset.univ.image f)).min' (by simp)

/-- A nonnegative upper bound selected by maximum, without a count factor. -/
def finitePrimitiveUpper (f : ι → ℝ) : ℝ :=
  (insert 0 (Finset.univ.image f)).max' (by simp)

theorem finitePrimitiveLower_le (f : ι → ℝ) (i : ι) : finitePrimitiveLower f ≤ f i := by
  exact Finset.min'_le _ _ (by simp)

theorem finitePrimitiveLower_pos (f : ι → ℝ) (hf : ∀ i, 0 < f i) : 0 < finitePrimitiveLower f := by
  have hmem := Finset.min'_mem (insert 1 (Finset.univ.image f)) (by simp)
  rcases Finset.mem_insert.mp hmem with h | h
  · change 0 < (insert 1 (Finset.univ.image f)).min' _
    rw [h]
    exact zero_lt_one
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    change 0 < (insert 1 (Finset.univ.image f)).min' _
    rw [← hi]
    exact hf i

theorem le_finitePrimitiveUpper (f : ι → ℝ) (i : ι) : f i ≤ finitePrimitiveUpper f := by
  exact Finset.le_max' _ _ (by simp)

theorem finitePrimitiveUpper_nonneg (f : ι → ℝ) : 0 ≤ finitePrimitiveUpper f := by
  exact Finset.le_max' _ _ (by simp)

end FiniteBounds
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.NativePrimitiveSignedRegion.weaken
#print axioms GlobalEmbedding.Continuation.finitePrimitiveLower_pos
#print axioms GlobalEmbedding.Continuation.le_finitePrimitiveUpper
