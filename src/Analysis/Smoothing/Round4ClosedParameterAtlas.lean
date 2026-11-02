import Smoothing.Round4TensorFiniteProviders
import Smoothing.ParameterOriginalABI
import Smoothing.ParameterLocalMap

/-!
# Genuine global atlas and exact operator identity for closed parameters

The already supplied plateau cover of all P supplies the missing cover field.
Charts, buffers, local normalization and integral values are not changed.
The only difference is the finite chart-index equivalence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

/-- No new parameter chart is selected. -/
def round4ClosedParameterAtlas
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i) : BufferedAtlas P Ep where
  count := pcount
  chart := B.chart
  inner := B.inner
  inner_open := B.inner_open
  inner_subset := B.inner_subset
  cover := hcover
  buffer := B.buffer
  buffer_pos := B.buffer_pos
  buffered := B.buffered
  support := B.inner

theorem round4ClosedParameterAtlas_smooth
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P) :
    IsSmoothBufferedAtlas (round4ClosedParameterAtlas B hcover) :=
  ⟨hB, B.inner_subset⟩

theorem round4ClosedParameterRaw_cover
    (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    {BP TP : ℕ → ℝ} {Dp : ℕ} (RP : TensorLocalRawPreparation B univ BP TP Dp) :
    ∀ p, ∃ i, p ∈ B.inner i := by
  intro p
  obtain ⟨i, hi⟩ := RP.plateau_on p (mem_univ p)
  refine ⟨i, RP.inner_support i (subset_tsupport (RP.raw i) ?_)⟩
  rw [mem_support, hi]
  exact one_ne_zero

@[simp] theorem round4ClosedParameterProduct_chart
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i) (i : Fin A.count × Fin pcount) :
    (parameterProductAtlas A (round4ClosedParameterAtlas B hcover)).chart
      (parameterTensorAtlasIndex A (round4ClosedParameterAtlas B hcover) i) =
      (parameterLocalProductFamily A B).chart i := by
  simp only [parameterProductAtlas, parameterTensorAtlasIndex, parameterProductIndex,
    Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem round4ClosedParameterProduct_inner
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i) (i : Fin A.count × Fin pcount) :
    (parameterProductAtlas A (round4ClosedParameterAtlas B hcover)).inner
      (parameterTensorAtlasIndex A (round4ClosedParameterAtlas B hcover) i) =
      (parameterLocalProductFamily A B).inner i := by
  simp only [parameterProductAtlas, parameterTensorAtlasIndex, parameterProductIndex,
    Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply]
  rfl

/-- The spatial-tail proof uses exactly the pre-existing integral, not a new map. -/
theorem round4ClosedParameter_actual_map_eq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (mu : Measure (Ep × Es)) (K : Ep × Es → ℝ) (ell : ℝ)
    (chi : Fin A.count × Fin pcount → P × M → ℝ) (u : P × M → Y) :
    bufferedSmoothing (parameterProductAtlas A (round4ClosedParameterAtlas B hcover))
      mu K ell (fun k => chi ((parameterTensorAtlasIndex A
        (round4ClosedParameterAtlas B hcover)).symm k)) u =
    parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u := by
  funext x
  unfold bufferedSmoothing parameterLocalMapSmoothing
  rw [← Equiv.sum_comp (parameterTensorAtlasIndex A (round4ClosedParameterAtlas B hcover))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bufferedSmoothingTerm, bufferedChartSmoothing, bufferedLocalSmoothing,
    bufferedCoordinateExtension, Equiv.symm_apply_apply, round4ClosedParameterProduct_chart]
  rfl

/-- Active multiplicity is preserved exactly, without using either chart count. -/
theorem round4ActiveCutoff_reindex_card
    {ι κ X : Type*} [Fintype ι] [Fintype κ] [TopologicalSpace X]
    (e : ι ≃ κ) (chi : ι → X → ℝ) (x : X) :
    (activeCutoffIndices (fun k => chi (e.symm k)) x).card =
      (activeCutoffIndices chi x).card := by
  classical
  have he : (activeCutoffIndices chi x).map e.toEmbedding =
      activeCutoffIndices (fun k => chi (e.symm k)) x := by
    ext k
    simp [activeCutoffIndices]
  rw [← he, Finset.card_map]

#print axioms round4ClosedParameter_actual_map_eq
#print axioms round4ClosedParameterRaw_cover
end GlobalEmbedding.Continuation
