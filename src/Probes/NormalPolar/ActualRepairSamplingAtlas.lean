import Upgrade.CompactAtlasSupport
import GlobalEmbedding.Offline.BufferedSamplingDomains

/-!
# A genuine probe atlas supplied by the actual repair sampling domains

The independent `support` field of a `BufferedAtlas` need not lie in the
repair's norm samples.  Consequently a tail estimate on those samples
cannot be applied to arbitrary old supports without a domain argument.

Here the compact sets Omega already present in the repair packet supply
an atlas with the SAME charts, inner cover and buffer.  Its supports are
the inverse images of Omega under those actual charts.  They are compact,
cover the source, and their coordinate images are exactly Omega.  Thus the
original probe gauge is exactly the repair's spatial sampling gauge.
The existing atlas-transport theorem can subsequently recover a prescribed
compact-support atlas without changing the family, Q, or parameter domain.
-/

noncomputable section
open Set Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

def actualRepairSamplingAtlas (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E) : BufferedAtlas M E :=
  enlargeBufferedAtlasSupport A (fun i ↦ (A.chart i).symm '' Omega i)

@[simp] theorem actualRepairSamplingAtlas_chart (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E) :
    (actualRepairSamplingAtlas A Omega).chart = A.chart := rfl

@[simp] theorem actualRepairSamplingAtlas_inner (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E) :
    (actualRepairSamplingAtlas A Omega).inner = A.inner := rfl

@[simp] theorem actualRepairSamplingAtlas_buffer (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E) :
    (actualRepairSamplingAtlas A Omega).buffer = A.buffer := rfl

theorem actualRepairSamplingAtlas_support_subset (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target) (i : Fin A.count) :
    (actualRepairSamplingAtlas A Omega).support i ⊆ (A.chart i).source := by
  rintro x ⟨y, hy, rfl⟩
  exact (A.chart i).map_target (hOmega i hy)

theorem actualRepairSamplingAtlas_smooth (A : BufferedAtlas M E)
    (hA : IsSmoothBufferedAtlas A) (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target) :
    IsSmoothBufferedAtlas (actualRepairSamplingAtlas A Omega) :=
  ⟨hA.chart_mem, actualRepairSamplingAtlas_support_subset A Omega hOmega⟩

theorem actualRepairSamplingAtlas_support_compact (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hcompact : ∀ i, IsCompact (Omega i))
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target) (i : Fin A.count) :
    IsCompact ((actualRepairSamplingAtlas A Omega).support i) := by
  exact (hcompact i).image_of_continuousOn
    ((A.chart i).continuousOn_symm.mono (hOmega i))

theorem actualRepairSamplingAtlas_inner_subset_support (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hsampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    A.inner i ⊆ (actualRepairSamplingAtlas A Omega).support i := by
  intro x hx
  have hsource := A.inner_subset i hx
  have hinner : A.chart i x ∈ bufferedInnerCoordinates A i := by
    refine ⟨(A.chart i).map_source hsource, ?_⟩
    change (A.chart i).symm (A.chart i x) ∈ A.inner i
    simpa only [(A.chart i).left_inv hsource] using hx
  exact ⟨A.chart i x, hsampling i (bufferedInner_subset_sampling A i hinner),
    (A.chart i).left_inv hsource⟩

theorem actualRepairSamplingAtlas_support_cover (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hsampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) :
    ∀ x, ∃ i, x ∈ (actualRepairSamplingAtlas A Omega).support i := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  exact ⟨i, actualRepairSamplingAtlas_inner_subset_support A Omega hsampling i hi⟩

theorem actualRepairSamplingAtlas_coordinate_support (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target) (i : Fin A.count) :
    (A.chart i) '' (actualRepairSamplingAtlas A Omega).support i = Omega i := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa only [(A.chart i).right_inv (hOmega i hy)] using hy
  · intro y hy
    exact ⟨(A.chart i).symm y, ⟨y, hy, rfl⟩, (A.chart i).right_inv (hOmega i hy)⟩

/-- Exact equality, with the same open differentiation domains and actual
coordinate conversions; no equivalence constant or enlarged norm is used. -/
theorem actualRepairSamplingAtlas_probeAtlasCj (A : BufferedAtlas M E)
    (Omega : Fin A.count → Set E)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target) (j : ℕ) (f : M → V) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j f =
      paperAtlasCj j
        (fun i x ↦ (EuclideanSpace.equiv (Fin N) ℝ)
          (f ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))))
        (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target)
        (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) '' Omega i) := by
  unfold probeAtlasCj
  have hsupport :
      (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) ''
        ((A.chart i) '' (actualRepairSamplingAtlas A Omega).support i)) =
      (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) '' Omega i) := by
    funext i
    rw [actualRepairSamplingAtlas_coordinate_support A Omega hOmega i]
  exact congrArg (fun S ↦ paperAtlasCj j
    (fun i x ↦ (EuclideanSpace.equiv (Fin N) ℝ)
      (f ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))))
    (fun i ↦ (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target) S) hsupport

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairSamplingAtlas_support_cover
#print axioms GlobalEmbedding.NormalPolar.actualRepairSamplingAtlas_probeAtlasCj
