import NormalPolar.JointSecondarySignedObserver
import Probes.ActualSecondaryQuadraticConstruction

/-! The actual observation sample is a compact image of the original atlas
support, intersected with the real subordinate cutoff support. Restricting a
raw sample keeps the full map, support, phase, chart, and all original budgets.
This lets finite original-coordinate bounds feed the new adapted charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

namespace ActualSecondaryRawGeometry
variable {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {n j : ℕ} {ell Mg : ℝ} {W : Set (Ep × M)}

def restrictSample (raw : ActualSecondaryRawGeometry F hF n j ell Mg W)
    (S : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))) (hS : S ⊆ raw.sample) :
    ActualSecondaryRawGeometry F hF n j ell Mg W :=
  { raw with
    sample := S
    sample_subset := hS.trans raw.sample_subset
    brows_bound := fun k hk z hz => raw.brows_bound k hk z (hS hz)
    transverse_bound := fun k hk z hz => raw.transverse_bound k hk z (hS hz)
    inverse_bound := fun k hk z hz => raw.inverse_bound k hk z (hS hz)
    value_bound := fun k hk z hz => raw.value_bound k hk z (hS hz)
    coefficientA_bound := fun k hk z hz => raw.coefficientA_bound k hk z (hS hz)
    coefficientB_bound := fun k hk z hz => raw.coefficientB_bound k hk z (hS hz) }

theorem restrictSample_literal (raw : ActualSecondaryRawGeometry F hF n j ell Mg W)
    (S : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))) (hS : S ⊆ raw.sample) :
    (raw.restrictSample S hS).c = raw.c ∧
    (raw.restrictSample S hS).chart = raw.chart ∧
    (raw.restrictSample S hS).phase = raw.phase ∧
    (raw.restrictSample S hS).support = raw.support ∧
    (raw.restrictSample S hS).spatialChart = raw.spatialChart ∧
    (raw.restrictSample S hS).sample = S :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end ActualSecondaryRawGeometry

variable [T2Space M] [CompactSpace M]
  {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer

def adaptedActiveSample (b : JointSecondarySignedBuffer d i) (S : Set M) : Set D :=
  b.chart '' (S ∩ tsupport (d.cutoff i))

theorem adaptedActiveSample_compact (b : JointSecondarySignedBuffer d i)
    (S : Set M) (hS : IsCompact S) : IsCompact (b.adaptedActiveSample S) :=
  (hS.inter_right (isClosed_tsupport _)).image_of_continuousOn
    (b.chart.continuousOn.mono (fun _ hx => b.support_source hx.2))

theorem adaptedActiveSample_target (b : JointSecondarySignedBuffer d i) (S : Set M) :
    b.adaptedActiveSample S ⊆ b.chart.target := by
  rintro _ ⟨x,hx,rfl⟩
  exact b.chart.map_source (b.support_source hx.2)

theorem adaptedActiveSample_active (b : JointSecondarySignedBuffer d i)
    (e : OpenPartialHomeomorph M D) (S : Set M) (hSe : S ⊆ e.source)
    (y : D) (hy : y ∈ e '' S) (hactive : e.symm y ∈ tsupport (d.cutoff i)) :
    b.chart (e.symm y) ∈ b.adaptedActiveSample S := by
  obtain ⟨x,hx,rfl⟩ := hy
  rw [e.left_inv (hSe hx)] at hactive ⊢
  exact ⟨x,⟨hx,hactive⟩,rfl⟩

theorem adaptedActiveSample_inverse (b : JointSecondarySignedBuffer d i)
    (S : Set M) (y : D) (hy : y ∈ b.adaptedActiveSample S) :
    b.chart.symm y ∈ S ∩ tsupport (d.cutoff i) := by
  obtain ⟨x,hx,rfl⟩ := hy
  rwa [b.chart.left_inv (b.support_source hx.2)]

theorem jointAdaptedActiveSample_compact (b : JointSecondarySignedBuffer d i)
    (Q : Set Ep) (S : Set M) (hQ : IsCompact Q) (hS : IsCompact S) :
    IsCompact (Q ×ˢ b.adaptedActiveSample S) :=
  hQ.prod (b.adaptedActiveSample_compact S hS)

theorem jointAdaptedActiveSample_target (b : JointSecondarySignedBuffer d i)
    (Q : Set Ep) (S : Set M) :
    Q ×ˢ b.adaptedActiveSample S ⊆ ((OpenPartialHomeomorph.refl Ep).prod b.chart).target :=
  fun _ hz => ⟨mem_univ _,b.adaptedActiveSample_target S hz.2⟩

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ActualSecondaryRawGeometry.restrictSample
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.adaptedActiveSample_compact
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.adaptedActiveSample_active
