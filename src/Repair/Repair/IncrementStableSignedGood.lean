import Probes.Round3PreparedParameterSecondaryStablePiece
import Probes.Round3PreparedParameterSecondaryGood
import Probes.Round3PreparedParameterSecondaryFactory

/-!
# The same stable secondary family proves all original signed phases good

The actual partition selects a carrier containing the physical point.
The already constructed stable piece supplies its positive transverse
reserve there, hence the original physical signed Good predicate. No
second signed-family selection or extra per-piece C2 tolerance is needed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem increment_stable_secondary_signed_good
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hPart : ∀ z, ∑ i, theta i z = 1)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : ∀ r i (a : packet.s r i),
      Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (z : P × M)
    (hz : z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2)) :
    GoodCovector (F z.1) (hF z.1) z.2
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2)) := by
  have hExistsI : ∃ i, theta i z ≠ 0 := by
    by_contra! hzero
    have hh := hPart z
    simp only [hzero,Finset.sum_const_zero,zero_ne_one] at hh
  obtain ⟨i,hi⟩ := hExistsI
  have hExistsA : ∃ a : packet.s r i,
      (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)).cutoff z ≠ 0 := by
    by_contra! hzero
    have hh := packet.partition r i z hz
    simp only [hzero,Finset.sum_const_zero] at hh
    exact hi hh.symm
  obtain ⟨a,ha⟩ := hExistsA
  have hPhysical : z ∈ round3PreparedParameterSecondaryCarrier Ref r
      (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)) :=
    ⟨subset_tsupport _ ha,hz⟩
  have hCarrier := (round3_prepared_parameter_secondary_carrier_source Ref hd hs i r
    (packet.piece r i a) (theta i) (hSupport i) (packet.parent r i a)).2 hPhysical
  let current := (stable r i a).piece
  let y := ((Ref.parameterChart i.2) z.1,z.2)
  have hCarrierCurrent : y ∈ current.carrier := by
    change y ∈ (stable r i a).piece.carrier
    rw [(stable r i a).carrier]
    exact hCarrier
  let point := actualHostAdaptedChart (Ref.atlas.chart i.1) current.native y
  have hTarget : point ∈ current.native.target := by
    rw [← current.data.1]
    exact (actualHostAdaptedChart (Ref.atlas.chart i.1) current.native).map_source
      (current.carrier_source hCarrierCurrent)
  have hGood := round3_prepared_parameter_secondary_good_on_carrier Ref hd hs i r _
    current F hF y hCarrierCurrent
    ((packet.piece r i a).cT/16) (div_pos (packet.piece r i a).cT_pos (by norm_num))
    ((stable r i a).transverse point hTarget)
  have hzsource : z.1 ∈ (Ref.parameterChart i.2).source := (hSupport i (subset_tsupport _ hi)).1
  dsimp only at hGood
  rw [(Ref.parameterChart i.2).left_inv hzsource] at hGood
  exact hGood

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_stable_secondary_signed_good
