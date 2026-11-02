import Repair.EntranceSpatialNativeProfiles
import Repair.ReferenceSpatialPrimarySupply

/-!
# Every jet of the actual shared primary packet

The native charts are the actual spatial linear coordinates assembled by
the primary factory. Only the original transition jets are supplied.
The reverse transition is sampled at its actual target; membership in
that target and in the original observer region is proved from the same
native partial homeomorphism, including its genuine inverse.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

theorem RepairReferenceSpatialPrimarySupply.native_profiles
    {Data : IncrementsOriginalNativeData (m+1) d N M P}
    {theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ}
    {owner : Fin Data.primaryCount → OpenPartialHomeomorph M D}
    {xi : Fin Data.primaryCount → D →L[ℝ] ℝ}
    {plateau : Fin Data.primaryCount → P × M → ℝ}
    {U : (Fin Data.atlas.count × Fin Data.parameterCount) → Set X}
    {mu bound : ℝ}
    (s : RepairReferenceSpatialPrimarySupply Data theta owner xi plateau U mu bound)
    (hmu : 0 < mu) (hBound : 0 ≤ bound)
    (hUOpen : ∀ i, U i ⊆ actualOriginalNativeOpen Data i)
    (hOwnerSource : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (owner nu).source)
    (V : ℝ) (hV : 0 ≤ V) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hSourceValue : ∀ i z, z ∈ U i → ‖z‖ ≤ V)
    (hOwnerValue : ∀ nu i z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu) z‖ ≤ V)
    (hForwardJet : ∀ nu i j, 1 ≤ j → ∀ z, z ∈ U i →
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).source →
      ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)) z‖ ≤ T j)
    (hInverseJet : ∀ nu i j, 1 ≤ j → ∀ z,
      z ∈ (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).target →
      (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)).symm z ∈ U i →
      ((Data.parameterChart i.2).symm z.1,(owner nu).symm z.2) ∈ Data.primaryDomain nu →
      ‖iteratedFDeriv ℝ j (repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1)
        (owner nu)).symm z‖ ≤ T j) :
    (∀ nu i a j z, z ∈ (s.packet.piece nu i a).native.source →
      ‖iteratedFDeriv ℝ j (s.packet.piece nu i a).native z‖ ≤
        repairEntranceSpatialNativeForward V (2*(1+2*bound)) T j) ∧
    ∀ nu i a j z, z ∈ (s.packet.piece nu i a).native.target →
      ‖iteratedFDeriv ℝ j (s.packet.piece nu i a).native.symm z‖ ≤
        repairEntranceSpatialNativeInverse V (2*actualPhaseInverseConstant mu (2*bound)) T j := by
  have hB : 1 ≤ 2*(1+2*bound) := by linarith
  have hInv := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*bound by positivity)
  have hI : 1 ≤ 2*actualPhaseInverseConstant mu (2*bound) := by linarith
  have hBoth (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (a : ↥(s.packet.s nu i)) :
      (∀ j z, z ∈ (s.packet.piece nu i a).native.source →
        ‖iteratedFDeriv ℝ j (s.packet.piece nu i a).native z‖ ≤
          repairEntranceSpatialNativeForward V (2*(1+2*bound)) T j) ∧
      ∀ j z, z ∈ (s.packet.piece nu i a).native.target →
        ‖iteratedFDeriv ℝ j (s.packet.piece nu i a).native.symm z‖ ≤
          repairEntranceSpatialNativeInverse V (2*actualPhaseInverseConstant mu (2*bound)) T j := by
    let b := (s.packet.piece nu i a).native
    let f := repairReferenceHostTransition («Ep» := Ep) (Data.atlas.chart i.1) (owner nu)
    let L := (ContinuousLinearEquiv.refl ℝ Ep).prodCongr (s.spatial nu)
    have hForward (z : X) : b z=L (f z) := s.forward nu i a z
    have hInverse (z : X) : b.symm z=f.symm (L.symm z) := s.inverse nu i a z
    have hSource (z : X) (hz : z ∈ b.source) : z ∈ f.source := by
      have h := (s.source nu i a z).mp hz
      have ho := (round3Parameter_originalNativeOpen_iff Data i z).mp (hUOpen i h.1)
      exact ⟨mem_univ _,ho.1,hOwnerSource nu _ h.2⟩
    have hTarget (z : X) (hz : z ∈ b.target) : L.symm z ∈ f.target := by
      have hEq : f (b.symm z)=L.symm z := by
        apply L.injective
        rw [← hForward,b.right_inv hz,L.apply_symm_apply]
      rw [← hEq]
      exact f.map_source (hSource _ (b.map_target hz))
    apply repairEntrance_actual_spatial_linear_profiles b f L hForward hInverse V
      (2*(1+2*bound)) (2*actualPhaseInverseConstant mu (2*bound)) hV
      (zero_le_one.trans hB) (zero_le_one.trans hI)
      (repairEntrance_identity_prod_linear_norm (s.spatial nu) _ hB (s.spatial_bound nu))
      (repairEntrance_identity_prod_linear_norm (s.spatial nu).symm _ hI (s.spatial_inverse_bound nu))
      T hT
    · intro z hz
      exact hSourceValue i z ((s.source nu i a z).mp hz).1
    · intro z hz
      exact hOwnerValue nu i z ((s.source nu i a z).mp hz).1 (hSource z hz)
        ((s.source nu i a z).mp hz).2
    · intro j hj z hz
      exact hForwardJet nu i j hj z ((s.source nu i a z).mp hz).1 (hSource z hz)
        ((s.source nu i a z).mp hz).2
    · intro j hj z hz
      apply hInverseJet nu i j hj (L.symm z) (hTarget z hz)
      · rw [← hInverse]
        exact ((s.source nu i a _).mp (b.map_target hz)).1
      · have hs := ((s.source nu i a _).mp (b.map_target hz)).2
        have ht := hTarget z hz
        rw [hInverse] at hs
        change ((Data.parameterChart i.2).symm (L.symm z).1,
          (Data.atlas.chart i.1).symm (Data.atlas.chart i.1 ((owner nu).symm (L.symm z).2))) ∈ _ at hs
        simpa only [(Data.atlas.chart i.1).left_inv ht.2.2] using hs
  exact ⟨fun nu i a => (hBoth nu i a).1,fun nu i a => (hBoth nu i a).2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.RepairReferenceSpatialPrimarySupply.native_profiles
