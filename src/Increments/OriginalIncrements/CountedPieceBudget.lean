import OriginalIncrements.CountedLowPrimarySupply
import OriginalCollars.OriginalHostTotalPieceBudget

/-!
# One total per-phase/owner budget for the actual counted packet

This is the supremum of the primitive's model numerical budgets, not a
supremum of actual cardinalities. It is selected with the actual low
geometry, before q, allowed, every scale and observation order. Summing
across primary labels needs the original bounded labels-per-host geometry;
the bound here deliberately does not multiply by total primaryCount.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

/-- A shared bound made only from model radius, spatial margin, low jets
and the actual buffer. The finite set of centers is not read here. -/
def OriginalCountedPrimarySupply.totalPieceBudget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalCountedPrimarySupply Data theta) : ℕ :=
  Finset.univ.sup (fun a : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
    originalPhaseTotalPieceBudget («Ep» := EuclideanSpace ℝ (Fin d)) (m := m)
      (supply.mu a.1 a.2) (supply.Mb a.1 a.2) (supply.radius a.1 a.2) (supply.buffer a.1 a.2)
      (supply.mu_pos a.1 a.2) (supply.Mb_nonneg a.1 a.2) (supply.buffer_pos a.1 a.2))

theorem OriginalCountedPrimarySupply.card_le_totalPieceBudget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalCountedPrimarySupply Data theta)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    (supply.packet.s nu i).card ≤ supply.totalPieceBudget Data theta := by
  apply (supply.total_card nu i).trans
  unfold OriginalCountedPrimarySupply.totalPieceBudget
  exact Finset.le_sup (f := fun a : Fin Data.primaryCount ×
      (Fin Data.atlas.count × Fin Data.parameterCount) =>
    originalPhaseTotalPieceBudget («Ep» := EuclideanSpace ℝ (Fin d)) (m := m)
      (supply.mu a.1 a.2) (supply.Mb a.1 a.2) (supply.radius a.1 a.2) (supply.buffer a.1 a.2)
      (supply.mu_pos a.1 a.2) (supply.Mb_nonneg a.1 a.2) (supply.buffer_pos a.1 a.2))
    (Finset.mem_univ (nu,i))

/-- Any existing common model budget controls this aggregate. In particular
there is no factor equal to the number of owner charts in this implication. -/
theorem OriginalCountedPrimarySupply.totalPieceBudget_le
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalCountedPrimarySupply Data theta) (L : ℕ)
    (hL : ∀ nu i, originalPhaseTotalPieceBudget («Ep» := EuclideanSpace ℝ (Fin d)) (m := m)
      (supply.mu nu i) (supply.Mb nu i) (supply.radius nu i) (supply.buffer nu i)
      (supply.mu_pos nu i) (supply.Mb_nonneg nu i) (supply.buffer_pos nu i) ≤ L) :
    supply.totalPieceBudget Data theta ≤ L := by
  apply Finset.sup_le
  intro a _
  exact hL a.1 a.2

/-- A genuine original parent/label support count bounds the total number
of refined pieces over that owner. The hypothesis counts original labels,
not constructed pieces; every nonempty actual piece set has an original
support witness supplied by center_active. -/
theorem OriginalCountedPrimarySupply.total_card_per_owner
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalCountedPrimarySupply Data theta)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (B : ℕ)
    (hLabels : (Finset.univ.filter (fun nu : Fin Data.primaryCount =>
      (tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu).Nonempty)).card ≤ B) :
    (∑ nu, (supply.packet.s nu i).card) ≤ B * supply.totalPieceBudget Data theta := by
  let L := supply.totalPieceBudget Data theta
  have hEach (nu : Fin Data.primaryCount) : (supply.packet.s nu i).card ≤
      if (tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu).Nonempty
        then L else 0 := by
    split_ifs with h
    · exact supply.card_le_totalPieceBudget Data theta nu i
    · have he : supply.packet.s nu i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact h ⟨((Data.parameterChart i.2).symm a.1,(Data.atlas.chart i.1).symm a.2),
          supply.center_active nu i ⟨a,ha⟩⟩
      simp only [he,Finset.card_empty,le_refl]
  calc
    _ ≤ ∑ nu : Fin Data.primaryCount,
        if (tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu).Nonempty
          then L else 0 := Finset.sum_le_sum (fun nu _ => hEach nu)
    _ = (Finset.univ.filter (fun nu : Fin Data.primaryCount =>
        (tsupport (theta i) ∩ incrementsOriginalRelativeCutoffSupport Data nu).Nonempty)).card * L := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,smul_eq_mul]
    _ ≤ B * L := Nat.mul_le_mul_right L hLabels

/-- The same actual packet has a total per-owner bound from the paper's
original host degree and bounded label fibers. All hypotheses concern
original host/label supports; no count of constructed pieces is assumed. -/
theorem OriginalCountedPrimarySupply.total_card_from_original_hosts
    {Host Y : Type*} [Fintype Host] [TopologicalSpace Y]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (supply : OriginalCountedPrimarySupply Data theta)
    (W : Host → Set Y) (pull : P × M → Y) (degree B : ℕ)
    (hDegree : ∀ i, tensorEnlargedSupportDegree W i ≤ degree)
    (host : Fin Data.primaryCount → Host)
    (hFiber : ∀ i, Fintype.card {nu : Fin Data.primaryCount // host nu = i} ≤ B)
    (hSupport : ∀ nu, incrementsOriginalRelativeCutoffSupport Data nu ⊆ pull ⁻¹' W (host nu))
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (owner : Host)
    (hParent : tsupport (theta i) ⊆ pull ⁻¹' W owner) :
    (∑ nu, (supply.packet.s nu i).card) ≤
      ((degree+1)*B) * supply.totalPieceBudget Data theta := by
  apply supply.total_card_per_owner Data theta i ((degree+1)*B)
  simpa only [Set.inter_comm] using originalLabelFiber_host_intersection_count W
    (incrementsOriginalRelativeCutoffSupport Data) pull degree B hDegree host hFiber hSupport
    owner (tsupport (theta i)) hParent

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalCountedPrimarySupply.card_le_totalPieceBudget

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalCountedPrimarySupply.total_card_per_owner

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.OriginalCountedPrimarySupply.total_card_from_original_hosts
