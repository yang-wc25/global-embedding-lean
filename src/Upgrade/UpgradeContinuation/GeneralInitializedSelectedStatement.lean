import UpgradeContinuation.GeneralOriginalSelectedQ440
import NormalPolar.ActualProbeInitialSupplySecondaryInitialization
import NormalPolar.PassiveOriginalPacketRawBridge
import UpgradeContinuation.GeneralMixedAtlasSeed
import NormalPolar.ActualProbeInitialSupplyPacket
import NormalPolar.PassiveOriginalSmooth
import Probes.Round3RepairReferenceEnvelope
import NormalPolar.PassiveOriginalPhysicalInitialized
import NormalPolar.JointMixedParameterInitializationProfiles

/-! The original initialized closed state and its actual secondary now retain
both the same original source profiles and the same canonical primary supply.
The fixed Tp/Pphase/rho select the buffer exactly as in the original producer;
no later source choice or parameter-ball restriction is hidden here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical BigOperators
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
universe uM uP uSub
variable {m d N r : ℕ} {M : Type uM} {P : Type uP} {Sub : Type uSub}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
private local instance probesSelectedInitializedStatementSignedFintype
    {Label : Type*} [Fintype Label] [DecidableEq Label] : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance
variable {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {referenceCost Given : ℕ → ℝ}

abbrev ProbesSelectedGeneralInitializedSecondaryStatement
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hp₀ : IncrementsOriginalPhaseConditions seed hd₀ hs₀)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl Z)
    (Rsub : ℕ) (primaryPacket : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub Rsub)
    (cF reserve0 : ℝ) (he₀ : IncrementsOriginalCoordinateEllipticityInputs seed cF)
    (hl₀ : IncrementsOriginalLinearSmoothInputs seed)
    (hc₀ : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hr₀ : IncrementsOriginalDecompositionReserveInputs seed reserve0)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => seed.F (0,x)))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x)) hF0)
    (b : Fin B.count) (p₀ : P) (hpP : p₀ ∈ B.inner b) : Prop :=
    let Data := passiveOriginalData (0 : Z) seed B Q
    let F0 := fun x => seed.F (0,x)
    let g0 := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base Rsub primaryPacket
    let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => seed.F (p,x)) g0
    let K : (Fin seed.primaryCount ⊕ Fin r) → Set M :=
      Sum.elim (fun l => tsupport (fun x => seed.cutoff l (0,x)))
        (fun l => tsupport ((waves l).cutoff : M → ℝ))
    ∃ weight : Fin r → ℝ, (∀ l, 0 < weight l) ∧ Function.Injective weight ∧
    ∃ family : GeneralLegalWaveRawFamily F0 hF0 waves weight,
    let signedPhase := fun (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) x =>
      jointSecondarySignedPhase
        (Sum.elim (fun l (z : Ep × M) => seed.phase l (0,z.2))
          (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val (0,x)
    ∃ (O : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r) → Set M)
      (seeds : (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) →
        JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (signedPhase rec)
          (K rec.val.1.1 ∩ K rec.val.1.2) (O rec)),
    ∃ rho : ℝ, ∃ hrho : 0 < rho, ∃ Tp Pphase : ℕ → ℝ,
      (∀ k, 0 < Tp k ∧ 0 < Pphase k) ∧
    let Samples := incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ
    ∃ hSamples : ∀ i, IsCompact (Samples i),
    ∃ numbers : Round3RepairMeanPrimitiveProfiles,
      rho = numbers.rho/2 ∧
      ProbesSelectedPrimarySupplier seed.atlas B Samples hSamples (fun _ _ hy => hy.1)
        F0 hF0 gp Data.primaryDomain Data.H numbers ∧
      ProbesSelectedGeneralProfiles F0 hF0 waves weight family seed.atlas B Samples Tp Pphase ∧
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ radius : ℝ, ∃ hradius : 0 < radius,
    ∃ packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Initialized.supportDegree radius hradius
      (passiveOriginalPhysicalReferenceBudget Data) (passiveOriginalPhysicalFixedBudget Data),
    packet.parameterFamily = tensorChartFamilyOfAtlas Initialized ∧
    packet.referenceMap = (fun z => seed.F (0,z.2)) ∧
    packet.Omega = seed.sourceNormDomain ∧ packet.Q = Q ∧ packet.metric = Data.H ∧
    (∀ v : Fin d → ℝ, ‖v‖ < actualRepairParameterRadius packet.parameterFamily →
      u (actualRepairParameterMap packet.parameterFamily b p₀ v) = v) ∧
    ∃ CU CS : ℝ, 0 ≤ CU ∧ 0 ≤ CS ∧
    (∀ t, 0 ≤ actualProbeSecondaryModulus CS t) ∧
    Filter.Tendsto (actualProbeSecondaryModulus CS) (𝓝[>] 0) (𝓝 0) ∧
    ∀ epsilonRepair eta capRepair : ℝ,
      0 < epsilonRepair → 0 < eta → 0 < capRepair →
    ∀ budget : ℝ, 4*round3RepairReferenceLowBase packet < budget →
    ∃ t0 : ℝ, ∃ ht0 : 0 < t0, ∃ ht0Half : t0 ≤ 1/2,
      t0 ≤ capRepair ∧ ∀ (t : ℝ) (ht : 0 < t) (htt : t ≤ t0)
        (label : (Fin r × Bool) ↪ Fin d),
    let tau := t^((6 : ℝ)/5)
    let ell := t^((11 : ℝ)/10)
    let delta := t^10
    let scale := Real.sqrt (1-delta^2)
    let hscale := actual_probe_contraction_mem_Icc t ht (htt.trans ht0Half)
    let F := fun _ : P => scale • F0
    let hF := fun _ : P => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : P => F0) (fun _ => hF0) gp scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    let target := (1-(tau^10/delta)^2) • Data.H
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P → D → M := fun l s (_ : P) =>
      (family.piece l).seed.coordinate s 0
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P × D → ℝ := fun l s z =>
      (family.piece l).seed.cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s (_ : P) x => actualRescaledNormal F0 hF0 scale
        (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
        ((waves l).normal ((family.piece l).seed.coordinate s 0 x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count → OpenPartialHomeomorph (P × M) (P × D) :=
      fun l s => passiveParameterChart (P := P) (0 : Z) ((family.piece l).seed.physicalChart s)
    let phase := fun l (z : P × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s p x =>
      (-(delta*tau)/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let meanProbe := fun p x => jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase
      tau 442 a (u p) p x
    let background := fun i => actualParameterBackgroundMeanIterate F hF g 442
      tau delta target (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    let U := actualProbeInitialGroupedIncrement F hF g label c vf phase tau delta
      442 442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
      (jointSecondarySeedPaddedChoice_preserves seeds)
    let secondary := actualParameterSecondarySourceSum F hF
      (actualProbeInitialGroupedSource F hF g label c vf phase tau delta
        442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
        (jointSecondarySeedPaddedChoice_preserves seeds)) tau 442
    ∃ initial : Round3RepairClosedState packet budget epsilonRepair eta 10 tau,
      initial.map = actualRepairModelFirstDefectFirstMap packet.referenceMap U delta ∧
      actualProbeInitialSecondaryBallBounds seed.atlas seed.sourceNormDomain Initialized CS t secondary ∧
      (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
        (incrementsOriginalDifferentiation seed.atlas B.chart) Samples ≠ ⊤ ∧
        (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
          (incrementsOriginalDifferentiation seed.atlas B.chart) Samples).toReal ≤ CU*delta/tau) ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
        (incrementsOriginalDifferentiation seed.atlas B.chart) Samples ≠ ⊤ ∧
        (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
          (incrementsOriginalDifferentiation seed.atlas B.chart) Samples).toReal ≤ CU*delta/tau)

end GlobalEmbedding.Continuation
