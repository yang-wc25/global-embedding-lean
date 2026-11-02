import CompletionIntegration.NativeCompactCutoffProfiles
import Repair.FullIncrementNovOpenSecondaryPieces

/-!
# Internally supplied native secondary profiles

The one actual signed packet supplies its native forward and inverse jets.
Its actual compact cutoffs supply whole-host-target jets, so this step needs
no compactness of the original observation domains. The profiles are chosen
before all scales and derivative orders. This is an internal geometric
supplier; numerical finite-prefix uniformity of the adapted-chart selection
is not asserted here.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem prepared_secondary_native_chart_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta) :
    ∃ Forward Inverse : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧
      (∀ r i (a : packet.s r i) k z,
        z ∈ (packet.piece r i a).native.source →
        ‖iteratedFDeriv ℝ k (packet.piece r i a).native z‖ ≤ Forward k) ∧
      (∀ r i (a : packet.s r i) k z,
        z ∈ (packet.piece r i a).native.target →
        ‖iteratedFDeriv ℝ k (packet.piece r i a).native.symm z‖ ≤ Inverse k) := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i)))
  let F := fun k => round3PreparedFiniteMaximum
    (fun a : A => (packet.piece a.1 a.2.1 a.2.2).Forward k)
  let I := fun k => round3PreparedFiniteMaximum
    (fun a : A => (packet.piece a.1 a.2.1 a.2.2).Tinv k)
  refine ⟨F, I, fun _ => round3PreparedFiniteMaximum_nonneg _,
    fun _ => round3PreparedFiniteMaximum_nonneg _, ?_, ?_⟩
  · intro r i a k z hz
    exact ((packet.piece r i a).forward_jets k z hz).trans
      (round3PreparedFiniteMaximum_bound
        (fun b : A => (packet.piece b.1 b.2.1 b.2.2).Forward k) ⟨r,i,a⟩)
  · intro r i a k z hz
    exact ((packet.piece r i a).inverse_jets k z hz).trans
      (round3PreparedFiniteMaximum_bound
        (fun b : A => (packet.piece b.1 b.2.1 b.2.2).Tinv k) ⟨r,i,a⟩)

variable [T2Space M]

theorem prepared_secondary_whole_host_cutoff_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) (k : ℕ) (z : X),
        z.2 ∈ (Data.atlas.chart i.1).target →
        ell^k * ‖iteratedFDeriv ℝ k
          (fun y : X => (packet.piece r i a).cutoff
            (y.1,(Data.atlas.chart i.1).symm y.2)) z‖ ≤ C k := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Data.primaryCount) =>
    Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i)))
  have hNative (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i)
      (fun z hz => ⟨(hSupport i hz).1, mem_univ _⟩)
  have hCut (r) (i) (a : packet.s r i) :
      tsupport (packet.piece r i a).cutoff ⊆
        (univ : Set Ep) ×ˢ (Data.atlas.chart i.1).source := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (hNative i).2.2 (packet.native_parent r i a hy)
    exact ⟨mem_univ _, Data.atlas.inner_subset i.1 (hSupport i hz).2⟩
  have hOne (a : A) := native_compact_cutoff_whole_host_profiles
    (Data.atlas.chart a.2.1.1) (hd.atlas_smooth.chart_mem a.2.1.1)
    (packet.piece a.1 a.2.1 a.2.2).cutoff
    (packet.piece a.1 a.2.1 a.2.2).cutoff_smooth
    (packet.piece a.1 a.2.1 a.2.2).cutoff_compact (hCut a.1 a.2.1 a.2.2)
  choose C hC hBound using hOne
  refine ⟨fun k => round3PreparedFiniteMaximum (fun a : A => C a k),
    fun _ => round3PreparedFiniteMaximum_nonneg _, ?_⟩
  intro ell hell hell1 r i a k z hz
  exact (hBound ⟨r,i,a⟩ ell hell hell1 k z hz).trans
    (round3PreparedFiniteMaximum_bound (fun b : A => C b k) ⟨r,i,a⟩)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.prepared_secondary_native_chart_profiles
#print axioms GlobalEmbedding.Continuation.prepared_secondary_whole_host_cutoff_profiles
