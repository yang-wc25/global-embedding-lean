import Upgrade.CompactNormalizedTensors
import Upgrade.SupportedProbePackets

/-!
# Actual value-frame neighborhoods for the final coincidence operation

The n+1 legal values supplied by saturation are independent actual normal
vectors. Their positive finite-frame margin, source variation and old-normal
projection error are fixed before probes. The original paired-value consumer
then needs only the genuine new normal and two-endpoint response errors.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Upgrade
variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

structure ValuePreparedNeighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : LegalValueWavePacket F hF x y (n + 1))
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) where
  margin : ℝ
  margin_pos : 0 < margin
  frame_lower : ∀ c : Fin (n + 1) → ℝ,
    margin * ‖c‖ ≤ ‖∑ l, c l • (packet.waves l).value x‖
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  rank_budget : (n + 1 : ℝ) * (tolerance + 4 * tolerance) < margin
  neighborhood : Set (M × M)
  neighborhood_open : IsOpen neighborhood
  center_mem : (x, y) ∈ neighborhood
  support : ∀ z ∈ neighborhood, z.1 ∈ interior (A.support i)
  cutoff : ∀ z ∈ neighborhood, ∀ l,
    (packet.waves l).cutoff z.1 = 1 ∧ (packet.waves l).cutoff z.2 = 0
  value_variation : ∀ z ∈ neighborhood, ∀ l,
    ‖(packet.waves l).value z.1 - (packet.waves l).value x‖ < tolerance / 4
  old_normal_variation : ∀ z ∈ neighborhood, ∀ l,
    ‖(normalSpace (I := IM) F z.1).starProjection ((packet.waves l).value x) -
      (packet.waves l).value x‖ < tolerance / 4

theorem LegalValueWavePacket.exists_prepared_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : LegalValueWavePacket F hF x y (n + 1))
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) :
    Nonempty (ValuePreparedNeighborhood A hA packet i hx) := by
  classical
  have hli : LinearIndependent ℝ (fun l ↦ (packet.waves l).value x) :=
    LinearIndependent.of_comp (normalSpace (I := IM) F x).orthogonalProjectionOnto.toLinearMap
      packet.value_columns
  obtain ⟨margin, hm, hframe⟩ := exists_positive_finite_frame_margin _ hli
  let eps := margin / (10 * ((n + 1 : ℝ) + 1))
  have heps : 0 < eps := div_pos hm (by positivity)
  have hidentity : (10 * ((n + 1 : ℝ) + 1)) * eps = margin := by
    dsimp only [eps]
    field_simp
  have hbudget : (n + 1 : ℝ) * (eps + 4 * eps) < margin := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hvalue (l : Fin (n + 1)) : ∀ᶠ z in 𝓝 x,
      ‖(packet.waves l).value z - (packet.waves l).value x‖ < eps / 4 := by
    have hc := (packet.waves l).value_contMDiff.continuous.continuousAt (x := x)
    have h := (hc.sub continuousAt_const).norm.eventually_lt_const (by
      change ‖(packet.waves l).value x - (packet.waves l).value x‖ < eps / 4
      simpa only [sub_self, norm_zero] using (show 0 < eps / 4 by positivity))
    exact h
  have hprojection (l : Fin (n + 1)) : ∀ᶠ z in 𝓝 x,
      ‖(normalSpace (I := IM) F z).starProjection ((packet.waves l).value x) -
        (packet.waves l).value x‖ < eps / 4 := by
    have hp := (smooth_immersion_normal_projection F hF himm).continuous.continuousAt (x := x)
    have hc : ContinuousAt (fun z ↦
        (normalSpace (I := IM) F z).starProjection ((packet.waves l).value x) -
          (packet.waves l).value x) x :=
      (hp.clm_apply continuousAt_const).sub continuousAt_const
    apply hc.norm.eventually_lt_const
    change ‖(normalSpace (I := IM) F x).starProjection ((packet.waves l).value x) -
      (packet.waves l).value x‖ < eps / 4
    rw [Submodule.starProjection_eq_self_iff.mpr ((packet.waves l).value_mem_normal x),
      sub_self, norm_zero]
    positivity
  have hall := (Filter.eventually_all.mpr hvalue).and
    ((Filter.eventually_all.mpr hprojection).and
      (packet.one_near.and (isOpen_interior.mem_nhds hx)))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hall
  obtain ⟨W, hWsub, hW, hyW⟩ := mem_nhds_iff.mp packet.zero_near
  exact ⟨{
    margin := margin
    margin_pos := hm
    frame_lower := hframe
    tolerance := eps
    tolerance_pos := heps
    rank_budget := hbudget
    neighborhood := U ×ˢ W
    neighborhood_open := hU.prod hW
    center_mem := ⟨hxU, hyW⟩
    support := fun z hz ↦ (hUsub hz.1).2.2.2
    cutoff := fun z hz l ↦ ⟨(hUsub hz.1).2.2.1 l, hWsub hz.2 l⟩
    value_variation := fun z hz l ↦ (hUsub hz.1).1 l
    old_normal_variation := fun z hz l ↦ (hUsub hz.1).2.1 l }⟩

end GlobalEmbedding.Upgrade
