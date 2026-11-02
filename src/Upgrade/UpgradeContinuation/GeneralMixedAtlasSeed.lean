import UpgradeContinuation.GeneralMixedSeed
import Main.GeneralLegalWaveRawFamily
import NormalPolar.JointSecondaryOriginalMixedSupport

/-!
# One mixed source and raw wave family from the original arbitrary cutoffs

The same hierarchy base selects injective positive weights for every
original probe label. All actual mixed signed-phase seeds and the general
raw prescribed family are then manufactured under these fixed weights.
The zero-dimensional reference carrier is transported by the already
proved exact support identity, without selecting any geometry again.

Source: `PassiveOriginalMixedInjective` and
`JointSecondaryOriginalMixedAtlasSeed`, with only their old wave-family
constructor replaced by the general raw-family constructor. This is an
actual upstream producer, not an assumption of a q440 supplier or response.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open GlobalEmbedding.NormalPolar Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {m N r : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- The actual mixed hierarchy has distinct weights, before any prescribed
refinement or signed-source reconstruction is chosen. -/
theorem generalMixed_probeWeight_injective
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd : IncrementsOriginalDomainConditions seed)
    (hs : IncrementsOriginalSmoothInputs seed)
    (hzero : (0 : Z) ∈ seed.parameterOpen)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x))
      (incrementsOriginal_slice_contMDiff seed hd hs 0 hzero))
    (mixed : JointSecondaryGeneralMixedSeedFamily (Ep := Ep) seed hd hs 0 hzero waves) :
    Function.Injective mixed.probeWeight := by
  intro i j hij
  change mixed.base^(i.val+1) = mixed.base^(j.val+1) at hij
  have hpow := (pow_right_strictMono₀ mixed.base_gt_one).injective hij
  apply Fin.ext
  omega

theorem jointSecondaryGeneralMixedCarrier_eq_slice_tsupports
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd : IncrementsOriginalDomainConditions seed)
    (hs : IncrementsOriginalSmoothInputs seed)
    (hzero : (0 : Z) ∈ seed.parameterOpen)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x))
      (incrementsOriginal_slice_contMDiff seed hd hs 0 hzero)) :
    jointSecondaryGeneralMixedCarrier seed hd hs (0 : Z) hzero waves =
      Sum.elim (fun l => tsupport (fun x : M => seed.cutoff l (0,x)))
        (fun l => tsupport (waves l).cutoff) := by
  funext l
  cases l with
  | inl l => exact jointSecondaryOriginalPrimaryCarrier_eq_slice_tsupport seed hd 0 hzero l
  | inr l => rfl

/-- Original data and original arbitrary-cutoff waves manufacture all
actual signed-phase seeds and the actual general raw family. The same
positive injective weights are retained everywhere. Empty supports and the
empty probe label list need no additional premise. -/
theorem generalOriginal_exists_injective_mixed_atlas_seed
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd : IncrementsOriginalDomainConditions seed)
    (hs : IncrementsOriginalSmoothInputs seed)
    (hp : IncrementsOriginalPhaseConditions seed hd hs)
    (hi : IncrementsOriginalSliceImmersionInputs seed)
    (hzero : (0 : Z) ∈ seed.parameterOpen)
    (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => seed.F (0,x)))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x)) hF0) :
    let K : (Fin seed.primaryCount ⊕ Fin r) → Set M :=
      Sum.elim (fun l => tsupport (fun x => seed.cutoff l (0,x)))
        (fun l => tsupport (waves l).cutoff)
    ∃ (weight : Fin r → ℝ), (∀ l, 0 < weight l) ∧ Function.Injective weight ∧
      ∃ (family : GeneralLegalWaveRawFamily (fun x => seed.F (0,x)) hF0 waves weight)
        (O : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r) → Set M),
        (∀ rec, IsOpen (O rec)) ∧
        (∀ rec, K rec.val.1.1 ∩ K rec.val.1.2 ⊆ O rec) ∧
        Nonempty ((rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) →
          JointSecondarySignedSeed (Ep := Ep) (fun x => seed.F (0,x)) hF0
            (fun x => jointSecondarySignedPhase
              (Sum.elim (fun l (z : Ep × M) => seed.phase l (0,z.2))
                (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val (0,x))
            (K rec.val.1.1 ∩ K rec.val.1.2) (O rec)) := by
  intro K
  obtain ⟨mixed⟩ := jointSecondary_exists_general_mixed_seed_family
    (Ep := Ep) seed hd hs (0 : Z) hzero waves hp hi
  obtain ⟨family⟩ := exists_generalLegalWaveRawFamily (fun x => seed.F (0,x)) hF0
    (hi.immersion 0 hzero) waves mixed.probeWeight mixed.probeWeight_pos
  have hK : jointSecondaryGeneralMixedCarrier seed hd hs (0 : Z) hzero waves = K :=
    jointSecondaryGeneralMixedCarrier_eq_slice_tsupports seed hd hs hzero waves
  have hphase (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) :
      jointSecondarySpatialSignedPhase
        (jointSecondaryGeneralMixedPhase seed hd hs (0 : Z) hzero waves mixed.base) rec.val =
      (fun x => jointSecondarySignedPhase
        (Sum.elim (fun l (z : Ep × M) => seed.phase l (0,z.2))
          (fun l (z : Ep × M) => mixed.probeWeight l*(waves l).phase z.2)) rec.val (0,x)) := by
    funext x
    exact congrFun (mixed.phase_identity (Y := Ep) rec) (0,x)
  refine ⟨mixed.probeWeight,mixed.probeWeight_pos,
    generalMixed_probeWeight_injective seed hd hs hzero waves mixed,
    family,mixed.domain,mixed.domain_open,?_,?_⟩
  · intro rec
    simpa only [hK] using mixed.carrier_subset rec
  · refine ⟨fun rec => ?_⟩
    simpa only [hK,hphase rec] using mixed.seed rec

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.generalMixed_probeWeight_injective
#print axioms GlobalEmbedding.Continuation.jointSecondaryGeneralMixedCarrier_eq_slice_tsupports
#print axioms GlobalEmbedding.Continuation.generalOriginal_exists_injective_mixed_atlas_seed
