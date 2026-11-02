import NormalPolar.JointSecondaryOriginalMixedGood
import NormalPolar.JointSecondaryProfiles

/-! The full actual mixed secondary seed family is manufactured from original
Data and original legal waves. Weights, finite partitions, true source charts,
compact buffers and complete geometric budgets are all selected before scales.
Every active signed phase is exactly the full original-label mixed phase. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
variable (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (p : P) (hpO : p ∈ Data.parameterOpen)
  (waves : Fin r → LocalLegalWave (n := m+1) (fun x => Data.F (p,x))
    (incrementsOriginal_slice_contMDiff Data hd hs p hpO))

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

structure JointSecondaryOriginalMixedSeedFamily where
  base : ℝ
  base_gt_one : 1 < base
  domain : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r) → Set M
  domain_open : ∀ rec, IsOpen (domain rec)
  carrier_subset : ∀ rec,
    jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.1 ∩
      jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.2 ⊆ domain rec
  domain_original : ∀ rec, domain rec ⊆
    jointSecondaryOriginalMixedDomain Data hd hs p hpO waves rec.val.1.1 ∩
      jointSecondaryOriginalMixedDomain Data hd hs p hpO waves rec.val.1.2
  seed : ∀ rec, JointSecondarySignedSeed (Ep := Ep)
    (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO)
    (jointSecondarySpatialSignedPhase (jointSecondaryOriginalMixedPhase Data hd hs p hpO waves base) rec.val)
    (jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.1 ∩
      jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves rec.val.1.2)
    (domain rec)

theorem jointSecondary_exists_original_mixed_seed_family
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) :
    Nonempty (JointSecondaryOriginalMixedSeedFamily (Ep := Ep) Data hd hs p hpO waves) := by
  obtain ⟨A,hA,hgood⟩ := jointSecondary_original_mixed_signed_good Data hd hs p hpO waves hp hImm
  let K := jointSecondaryOriginalMixedCarrier Data hd hs p hpO waves
  let O := jointSecondaryOriginalMixedDomain Data hd hs p hpO waves
  let phase := jointSecondaryOriginalMixedPhase Data hd hs p hpO waves A
  have hex (rec : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r)) :=
    jointSecondary_exists_signed_seed_of_carrier_good (Ep := Ep)
      (fun y => Data.F (p,y)) (incrementsOriginal_slice_contMDiff Data hd hs p hpO)
      (hImm.immersion p hpO) (jointSecondarySpatialSignedPhase phase rec.val)
      (K rec.val.1.1 ∩ K rec.val.1.2) (O rec.val.1.1 ∩ O rec.val.1.2)
      ((jointSecondaryOriginalMixedCarrier_closed Data hd hs p hpO waves rec.val.1.1).inter
        (jointSecondaryOriginalMixedCarrier_closed Data hd hs p hpO waves rec.val.1.2))
      ((jointSecondaryOriginalMixedDomain_open Data hd hs p hpO waves rec.val.1.1).inter
        (jointSecondaryOriginalMixedDomain_open Data hd hs p hpO waves rec.val.1.2))
      (fun _ hx =>
        ⟨jointSecondaryOriginalMixedCarrier_domain Data hd hs p hpO waves rec.val.1.1 hx.1,
          jointSecondaryOriginalMixedCarrier_domain Data hd hs p hpO waves rec.val.1.2 hx.2⟩)
      (jointSecondarySpatialSignedPhase_smooth phase O
        (jointSecondaryOriginalMixedPhase_smooth Data hd hs p hpO waves A) rec.val)
      (hgood rec)
  choose U hU hKU hUO hseed using hex
  exact ⟨{
    base := A
    base_gt_one := hA
    domain := U
    domain_open := hU
    carrier_subset := hKU
    domain_original := hUO
    seed := fun rec => Classical.choice (hseed rec) }⟩

namespace JointSecondaryOriginalMixedSeedFamily
variable {Data hd hs p hpO waves}

def probeWeight (family : JointSecondaryOriginalMixedSeedFamily (Ep := Ep) Data hd hs p hpO waves)
    (l : Fin r) : ℝ := family.base^(l.val+1)

theorem probeWeight_pos (family : JointSecondaryOriginalMixedSeedFamily (Ep := Ep) Data hd hs p hpO waves)
    (l : Fin r) : 0 < family.probeWeight l :=
  pow_pos (zero_lt_one.trans family.base_gt_one) _

theorem phase_identity {Y : Type*}
    (family : JointSecondaryOriginalMixedSeedFamily (Ep := Ep) Data hd hs p hpO waves)
    (rec : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r)) :
    (fun z : Y × M => jointSecondarySpatialSignedPhase
      (jointSecondaryOriginalMixedPhase Data hd hs p hpO waves family.base) rec.val z.2) =
      jointSecondarySignedPhase
        (Sum.elim (fun l (z : Y × M) => Data.phase l (p,z.2))
          (fun l (z : Y × M) => family.probeWeight l * (waves l).phase z.2)) rec.val := by
  funext z
  rcases rec with ⟨⟨⟨l,l'⟩,q⟩,hr⟩
  cases l <;> cases l' <;> rfl

end JointSecondaryOriginalMixedSeedFamily
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_original_mixed_seed_family
#print axioms GlobalEmbedding.Continuation.JointSecondaryOriginalMixedSeedFamily.phase_identity
