import Upgrade.ProtectionMargins
import Mathlib.Topology.Separation.Hausdorff

/-!
# The actual remaining pair region and the dimension-three stopping case

Both endpoints are excluded from every protected closure. In dimension three
the second protected region may contain surviving supported kernels; only
their coincidences were removed. If the two regions already cover the source,
the remaining pair region is empty and the final value perturbation is skipped.
The final compact-source embedding argument includes cross-component pairs
and empty sources without extra hypotheses.
-/

open Set Topology
namespace GlobalEmbedding.Upgrade

variable {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E]

def remainingPairRegion (P : Set (M × M)) (O S : Set M) : Set (M × M) :=
  P ∩ ((O ∪ S)ᶜ ×ˢ (O ∪ S)ᶜ)

theorem isCompact_remainingPairRegion
    {P : Set (M × M)} (hP : IsCompact P) {O S : Set M} (hO : IsOpen O) (hS : IsOpen S) :
    IsCompact (remainingPairRegion P O S) :=
  hP.inter_right ((hO.union hS).isClosed_compl.prod (hO.union hS).isClosed_compl)

theorem actual_coincidence_mem_remainingPairRegion
    {G : M → E} {P : Set (M × M)} {O S : Set M} {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hO : ∀ z ∈ P, z.1 ∈ closure O ∨ z.2 ∈ closure O → d ≤ ‖G z.1 - G z.2‖)
    (hS : ∀ z ∈ P, z.1 ∈ closure S ∨ z.2 ∈ closure S → e ≤ ‖G z.1 - G z.2‖)
    {z : M × M} (hz : z ∈ P) (hcoincidence : G z.1 = G z.2) :
    z ∈ remainingPairRegion P O S := by
  have hnotO := coincidence_mem_complement_prod_of_protected_gap hd hO z hz hcoincidence
  have hnotS := coincidence_mem_complement_prod_of_protected_gap he hS z hz hcoincidence
  exact ⟨hz, fun h ↦ h.elim hnotO.1 hnotS.1, fun h ↦ h.elim hnotO.2 hnotS.2⟩

theorem remainingPairRegion_eq_empty_of_protected_cover
    (P : Set (M × M)) {O S : Set M} (hcover : O ∪ S = univ) :
    remainingPairRegion P O S = ∅ := by
  simp only [remainingPairRegion, hcover, compl_univ, empty_prod, inter_empty]

/-- Finishing the remaining actual coincidences suffices because all earlier
protected value gaps and the same diagonal neighborhood still hold. -/
theorem isClosedEmbedding_of_remainingPairRegion_avoidance [CompactSpace M]
    {G : M → E} (hG : Continuous G) {D : Set (M × M)} {O S : Set M}
    (hlocal : ∀ x y, (x, y) ∈ D → G x = G y → x = y)
    {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hO : ∀ z ∈ Dᶜ, z.1 ∈ closure O ∨ z.2 ∈ closure O → d ≤ ‖G z.1 - G z.2‖)
    (hS : ∀ z ∈ Dᶜ, z.1 ∈ closure S ∨ z.2 ∈ closure S → e ≤ ‖G z.1 - G z.2‖)
    (hremaining : ∀ z ∈ remainingPairRegion Dᶜ O S, G z.1 ≠ G z.2) :
    IsClosedEmbedding G := by
  apply hG.isClosedEmbedding
  intro x y hxy
  by_cases hD : (x, y) ∈ D
  · exact hlocal x y hD hxy
  · exact (hremaining (x, y)
      (actual_coincidence_mem_remainingPairRegion hd he hO hS hD hxy) hxy).elim

/-- The n=3 early stopping case: no final value packet or extra perturbation
is needed when the rank and supported protected neighborhoods cover M. -/
theorem isClosedEmbedding_of_protected_cover [CompactSpace M]
    {G : M → E} (hG : Continuous G) {D : Set (M × M)} {O S : Set M}
    (hlocal : ∀ x y, (x, y) ∈ D → G x = G y → x = y)
    {d e : ℝ} (hd : 0 < d) (he : 0 < e)
    (hO : ∀ z ∈ Dᶜ, z.1 ∈ closure O ∨ z.2 ∈ closure O → d ≤ ‖G z.1 - G z.2‖)
    (hS : ∀ z ∈ Dᶜ, z.1 ∈ closure S ∨ z.2 ∈ closure S → e ≤ ‖G z.1 - G z.2‖)
    (hcover : O ∪ S = univ) : IsClosedEmbedding G := by
  apply isClosedEmbedding_of_remainingPairRegion_avoidance hG hlocal hd he hO hS
  rw [remainingPairRegion_eq_empty_of_protected_cover _ hcover]
  exact fun _ h ↦ h.elim

end GlobalEmbedding.Upgrade
