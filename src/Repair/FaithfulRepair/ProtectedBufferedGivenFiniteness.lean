import FaithfulRepair.ProtectedGivenFiniteness
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Keep a common original buffer while manufacturing all-order finiteness

The compact protected sets are produced here as closed half-thickenings
of the actual original native carriers. The original numerical buffer
proves that these sets lie in the original primary domains. The protected
localization then keeps them and gives the same all-order finite datum.
The radius in the conclusion is exactly `buffer / 2`, chosen before the
actual datum, its chart count, and every observation order.

This is the original-coordinate internal supplier. A common original
buffer is an original-domain geometric fact, to be produced by the actual
template/carrier construction; no bound on an adapted inverse or final
increment is assumed or manufactured by renaming a packet field.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.FaithfulRepair
open FaithfulIncrements FaithfulIntegration

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

/-- A common original native buffer survives both the primary-domain and
parameter-domain restrictions. Compact carriers and all-order finiteness
are manufactured in the proof; the original norm domains remain literal. -/
theorem original_buffer_preserving_given_finite_neighborhoods
    (buffer : ℝ) (hbuffer : 0 < buffer)
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (Parameter Spatial : ℕ → ℝ)
    (hParameter : ∀ k, 0 ≤ Parameter k) (hSpatial : ∀ k, 0 ≤ Spatial k)
    (hGeometry : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (K : Fin Data.primaryCount →
      Fin Data.atlas.count × Fin Data.parameterCount → Set X)
    (hK : ∀ nu i, IsCompact (K nu i))
    (hBuffer : ∀ nu i x, x ∈ K nu i →
      ball x buffer ⊆ actualOriginalPrimaryNativeOpen Data nu i) :
    ∃ (V : Set P) (domain : Fin Data.primaryCount → Set (P × M)),
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ closure V ⊆ Data.parameterOpen ∧
      IsCompact (closure V) ∧
      (∀ nu, IsOpen (domain nu)) ∧
      (∀ nu, IsCompact (closure (domain nu))) ∧
      (∀ nu, closure (domain nu) ⊆
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      (∀ nu, incrementsOriginalRelativeCutoffSupport
        (localPrimaryData Data V domain) nu ⊆ domain nu) ∧
      (∀ nu i, cthickening (buffer/2) (K nu i) ⊆
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) ∧
      (∀ nu i x, x ∈ K nu i → ball x (buffer/2) ⊆
        actualOriginalPrimaryNativeOpen (localPrimaryData Data V domain) nu i) ∧
      ∀ j ell, actualOriginalGivenInputProfile (localPrimaryData Data V domain) j ell ≠ ⊤ := by
  let C := fun nu i => cthickening (buffer/2) (K nu i)
  have hC : ∀ nu i, IsCompact (C nu i) := fun nu i => (hK nu i).cthickening
  have hNative : ∀ nu i, C nu i ⊆ actualOriginalPrimaryNativeOpen Data nu i := by
    intro nu i z hz
    change z ∈ cthickening (buffer/2) (K nu i) at hz
    rw [(hK nu i).cthickening_eq_biUnion_closedBall (by positivity)] at hz
    obtain ⟨x, hx, hxz⟩ := mem_iUnion₂.mp hz
    exact hBuffer nu i x hx ((closedBall_subset_ball (half_lt_self hbuffer)) hxz)
  obtain ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport,
      hProtected, hFinite⟩ :=
    original_protected_given_finite_neighborhoods Data hd hs hLinear
      Parameter Spatial hParameter hSpatial hGeometry C hC hNative
  refine ⟨V, domain, hV, hKV, hVU, hVC, hOpen, hCompact, hClosure, hSupport,
    hProtected, ?_, hFinite⟩
  intro nu i x hx
  exact (ball_subset_closedBall.trans (closedBall_subset_cthickening hx (buffer/2))).trans
    (hProtected nu i)

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_buffer_preserving_given_finite_neighborhoods
