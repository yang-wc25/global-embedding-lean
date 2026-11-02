import FaithfulCollars.OriginalBufferedRawPair
import Repair.EndpointSourceCompactness
import Repair.SourceCollarNovParentCollars

/-!
# Compact internal carriers inside the original open norm domains

The original norm sets need not be compact.  A finite union of closed
center balls of radius `b/2` contains every sampling point of the actual
refined working family and still lies inside the original `b` buffer.
These are internal carriers, never replacement norm domains.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulCollars

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]
  (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
  (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ A.buffer)
  (s : SourceCollarNovFamily A Omega R b hb)

def sourceRefinedSamplingCarrier (i : Fin A.count) : Set E :=
  ⋃ c : s.centers i, closedBall c.val (b/2)

theorem sourceRefinedSamplingCarrier_compact (i : Fin A.count) :
    IsCompact (sourceRefinedSamplingCarrier A Omega R b hb s i) :=
  isCompact_iUnion fun c => isCompact_closedBall c.val (b/2)

include hbuffer in
theorem sourceRefinedSamplingCarrier_original
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    sourceRefinedSamplingCarrier A Omega R b hb s i ⊆ Omega i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply hSampling i
  apply mem_iUnion.mpr
  refine ⟨c.val, mem_iUnion.mpr ⟨s.center_inner i c.property, ?_⟩⟩
  change dist y c.val < A.buffer
  have hc' : dist y c.val ≤ b/2 := hc
  linarith

theorem refinedWorkingAtlas_sampling_subset_carrier (i : Fin A.count) :
    bufferedSamplingCoordinates (originalRefinedWorkingAtlas A Omega R b hb hbuffer s) i ⊆
      sourceRefinedSamplingCarrier A Omega R b hb s i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzdom := hzInner.2.2
  change A.chart i ((A.chart i).symm z) ∈ refinedWorkingDomain A Omega R b hb s i at hzdom
  rw [(A.chart i).right_inv hzInner.1] at hzdom
  obtain ⟨c, hc⟩ := mem_iUnion.mp hzdom
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  have hc' : dist z c.val < 3*b/8 := hc
  have hy' : dist y z < b/8 := hyball
  change dist y c.val ≤ b/2
  linarith [dist_triangle y z c.val]

include R b hb hbuffer s in
/-- Finite buffered geometry itself proves compactness of the source;
compactness of the original open norm sets is not required. -/
theorem sourceCompact_of_refined_carriers
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target) : CompactSpace M :=
  repair_source_compact_of_original_sampling
    (originalRefinedWorkingAtlas A Omega R b hb hbuffer s)
    (sourceRefinedSamplingCarrier A Omega R b hb s)
    (sourceRefinedSamplingCarrier_compact A Omega R b hb s)
    (fun i => (sourceRefinedSamplingCarrier_original A Omega R b hb hbuffer s hSampling i).trans
      (hTarget i))
    (refinedWorkingAtlas_sampling_subset_carrier A Omega R b hb hbuffer s)

variable {ι P : Type*} [Fintype ι] [TopologicalSpace P]
  (B : TensorBufferedChartFamily ι P E)
  (t : OriginalLocalBufferedCenters B R b hb)

def localRefinedSamplingCarrier (i : ι) : Set E :=
  ⋃ c : t.centers i, closedBall c.val (b/2)

theorem localRefinedSamplingCarrier_compact (i : ι) :
    IsCompact (localRefinedSamplingCarrier R b hb B t i) :=
  isCompact_iUnion fun c => isCompact_closedBall c.val (b/2)

theorem localRefinedSamplingCarrier_sampling (hbuffer : b ≤ B.buffer) (i : ι) :
    localRefinedSamplingCarrier R b hb B t i ⊆ tensorLocalSamplingCoordinates B i := by
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  apply mem_iUnion.mpr
  refine ⟨c.val, mem_iUnion.mpr ⟨t.center_inner i c.property, ?_⟩⟩
  change dist y c.val < B.buffer
  have hc' : dist y c.val ≤ b/2 := hc
  linarith

theorem refinedLocalFamily_sampling_subset_carrier (hbuffer : b ≤ B.buffer) (i : ι) :
    tensorLocalSamplingCoordinates (originalRefinedLocalFamily B R b hb hbuffer t) i ⊆
      localRefinedSamplingCarrier R b hb B t i := by
  intro y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  obtain ⟨hzInner, hyball⟩ := mem_iUnion.mp hz
  have hzdom := hzInner.2.2
  change B.chart i ((B.chart i).symm z) ∈ localRefinedWorkingDomain B R b hb t i at hzdom
  rw [(B.chart i).right_inv hzInner.1] at hzdom
  obtain ⟨c, hc⟩ := mem_iUnion.mp hzdom
  apply mem_iUnion.mpr
  refine ⟨c, ?_⟩
  have hc' : dist z c.val < 3*b/8 := hc
  have hy' : dist y z < b/8 := hyball
  change dist y c.val ≤ b/2
  linarith [dist_triangle y z c.val]

/-- Compactness is required of an internal carrier only.  The original
function and its whole topological support are retained. -/
theorem compactSupport_of_internal_carrier [T2Space M]
    (e : OpenPartialHomeomorph M E) (f : M → ℝ) (C : Set E)
    (hC : IsCompact C) (hTarget : C ⊆ e.target)
    (hSupport : tsupport f ⊆ e.source ∩ e ⁻¹' C) : HasCompactSupport f := by
  have hImage : IsCompact (e.symm '' C) :=
    hC.image_of_continuousOn (e.continuousOn_symm.mono hTarget)
  apply hImage.of_isClosed_subset (isClosed_tsupport f)
  intro x hx
  exact ⟨e x, (hSupport hx).2, e.left_inv (hSupport hx).1⟩

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.sourceCompact_of_refined_carriers
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.refinedLocalFamily_sampling_subset_carrier
