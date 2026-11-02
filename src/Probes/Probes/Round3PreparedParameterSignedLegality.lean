import Probes.Round3PreparedParameterSecondaryGood
import Probes.Round3PreparedParameterSecondaryFactory

/-! Fixed original signed preparation supplies one C2 entrance tolerance for
ALL physical signed/doubled support pairs on an arbitrary parameter manifold.
The new map has no assumed phase-goodness certificate. -/
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

private theorem round3_secondary_finite_positive {A : Type*} [Fintype A]
    (f : A → ℝ) (hf : ∀ a, 0 < f a) : ∃ e : ℝ, 0 < e ∧ ∀ a, e ≤ f a := by
  let s := insert 1 (Finset.univ.image f)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  refine ⟨s.min' hs,?_,fun a => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ a)))⟩
  have hm := Finset.min'_mem s hs
  rcases Finset.mem_insert.mp hm with h | h
  · rw [h]; norm_num
  · obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    exact hf a

 theorem round3_prepared_parameter_packet_signed_good
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hPart : ∀ z, ∑ i, theta i z = 1)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hParam : ∀ r i a y, y ∈ (packet.piece r i a).carrier → y.1 ∈ Ref.parameterNormDomain i.2)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) z,
      z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2) →
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2)) := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Ref.primaryCount) =>
    Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i)))
  have hEach (a : A) := round3_prepared_parameter_secondary_C2_pointwise Ref hd hs a.2.1 a.1 _
    (packet.piece a.1 a.2.1 a.2.2) hAll (hParam a.1 a.2.1 a.2.2) hF0joint
  choose eps hEps hPoint using hEach
  obtain ⟨epsilon,hepsilon,hEpsilon⟩ := round3_secondary_finite_positive eps hEps
  refine ⟨epsilon,hepsilon,?_⟩
  intro F hFjoint hF S hFinite hBound r z hz
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
  have hNew := hPoint ⟨r,⟨i,a⟩⟩ F hFjoint hF hFinite
    (hBound.trans (hEpsilon ⟨r,⟨i,a⟩⟩))
    ((Ref.parameterChart i.2) z.1,z.2) hCarrier
  have hGood := round3_prepared_parameter_secondary_good_on_carrier Ref hd hs i r _
    (packet.piece r i a) F hF ((Ref.parameterChart i.2) z.1,z.2) hCarrier
    ((packet.piece r i a).cT/4) (div_pos (packet.piece r i a).cT_pos (by norm_num)) hNew.2
  have hzsource : z.1 ∈ (Ref.parameterChart i.2).source := (hSupport i (subset_tsupport _ hi)).1
  dsimp only at hGood
  rw [(Ref.parameterChart i.2).left_inv hzsource] at hGood
  exact hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_packet_signed_good
