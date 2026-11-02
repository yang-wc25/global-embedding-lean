import UpgradeContinuation.OriginalReferenceSupply
import UpgradeContinuation.GeneralProbeMapSplit
import NormalPolar.JointMixedParameterInitialization
import NormalPolar.PassiveOriginalReferenceGeometry
import NormalPolar.JointSecondaryGroupedMeanCost

/-!
# Literal component identity for the same selected first map

The selected passive primary, contracted zero-parameter primary, global
parameter, target and grouped background recurrence are identified here.
The whole source slice on the full selected parameter ball therefore is
exactly the background/prescribed/secondary sum used by the original
response estimates.  The original physical packet and signed choice are
retained throughout.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
open scoped ContDiff Topology Classical ENNReal

namespace GlobalEmbedding.Continuation.UpgradeContinuation

variable {m N r : ℕ} {M P Sub : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]
  [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "d" => Fintype.card (Fin r × Bool)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

private local instance signedFinite {Label : Type*} [Fintype Label] [DecidableEq Label] :
    Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- Whole-ball, whole-source identity for the literal map selected by
`OriginalSelectedTailStatement`.  The signed secondary choice is supplied
unchanged from that selection, and both packet identities are explicit. -/
def GeneralSelectedMapSplitStatement
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (Tp Pphase : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (choice : ActualSecondarySignedRecord (Fin s.seed.primaryCount ⊕ Fin r) → Sub →
      Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec a, Round3ParameterChartPreserves (choice rec a).chart) : Prop :=
    let Data := passiveOriginalData (0 : Z) s.seed B Q
    let g0 : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin s.seed.primaryCount)
        (Β := s.subdivisionIndex) (fun _ : Z => F0) :=
      passiveOriginalReferencePrimary s.seed s.domain s.smooth s.freeNormal
      s.baseIndex s.refinementMultiplicity s.primary
    let gp : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin s.seed.primaryCount)
        (Β := s.subdivisionIndex) (fun _ : P => F0) :=
      passiveParameterPrimary (P := P) (0 : Z) (fun p x => s.seed.F (p,x)) g0
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let ha := passiveOriginalReserveAmplitude_pos Csrc rho hrho
    let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
    let u := passiveOriginalSmallParameter B amplitude ha b p₀
    ∀ {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
      {reference Given : ℕ → ℝ}
      (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given),
    packet.parameterFamily = tensorChartFamilyOfAtlas Initialized →
    packet.referenceMap = (fun z => s.seed.F (0,z.2)) →
    ∀ (t : ℝ) (ht : 0 < t) (htHalf : t ≤ 1/2),
    let label := (round4PairedParameterIndex r).toEmbedding
    let tau := t^((6 : ℝ)/5)
    let delta := t^10
    let scale := Real.sqrt (1-delta^2)
    let hscale := actual_probe_contraction_mem_Icc t ht htHalf
    let F : P → M → V := fun _ : P => scale • F0
    let hF : ∀ p : P, ContMDiff IM 𝓘(ℝ,V) ∞ (F p) :=
      fun _ : P => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : P => F0) (fun _ => hF0) gp scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    let target : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      (1-(tau^10/delta)^2) • Data.H
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P → D → M := fun l a (_ : P) =>
      ((family.piece l).seed.outer a).chart.symm
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P × D → ℝ :=
      fun l a (z : P × D) => (family.piece l).seed.cutoffCoordinates a (0,z.2)
    let nu : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
        normalSpace (I := IM) (F p) (c l a p x) := fun l a (_ : P) x => actualRescaledNormal F0 hF0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) (((family.piece l).seed.outer a).chart.symm x)
      ((waves l).normal (((family.piece l).seed.outer a).chart.symm x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count →
        OpenPartialHomeomorph (P × M) (P × D) :=
      fun l a => passiveParameterChart (P := P) (0 : Z) ((family.piece l).seed.physicalChart a)
    let phase : Fin r → P × M → ℝ := fun l (z : P × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
        normalSpace (I := IM) (F p) (c l a p x) :=
      fun l a p x => (-(delta*tau)/(weight l)^2) • (chi l a (p,x) • nu l a p x)
    let meanProbe : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      fun p x => jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase
      tau 442 a (u p) p x
    let background : ℕ → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      fun i => actualParameterBackgroundMeanIterate F hF g 442 tau delta target
      (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    let U : P × M → V := actualProbeInitialGroupedIncrement F hF g label c vf phase tau delta
      442 442 442 a (background 441) u choice hc
    let secondary : P × M → V := actualParameterSecondarySourceSum F hF
      (actualProbeInitialGroupedSource F hF g label c vf phase tau delta
        442 442 a (background 441) u choice hc) tau 442
    let Fz : Z → M → V := fun _ : Z => scale • F0
    let hFz : ∀ z : Z, ContMDiff IM 𝓘(ℝ,V) ∞ (Fz z) :=
      fun _ : Z => contMDiff_const_rescale F0 hF0 scale
    let gz := passiveRescaledPrimary (fun _ : Z => F0) (fun _ => hF0) g0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    let targetz : (z : Z) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      (1-(tau^10/delta)^2) • s.seed.H
    let cz : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z → D → M :=
      fun l a (_ : Z) => ((family.piece l).seed.outer a).chart.symm
    let vfz : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (Fz z) (cz l a z x) := fun l a (_ : Z) x => (-(delta*tau)/(weight l)^2) •
      ((family.piece l).seed.cutoffCoordinates a (0,x) •
        actualRescaledNormal F0 hF0 scale (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
          (((family.piece l).seed.outer a).chart.symm x)
          ((waves l).normal (((family.piece l).seed.outer a).chart.symm x)))
    let phasez : Fin r → Z × M → ℝ := fun l (z : Z × M) => weight l*(waves l).phase z.2
    let az : (l : Fin r) → Fin (family.piece l).seed.refinement.count →
        OpenPartialHomeomorph (Z × M) (Z × D) := fun l a => (family.piece l).seed.physicalChart a
    let probez : (Fin d → ℝ) → (z : Z) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
      jointGroupedParameterPrescribedMean (I := IM) label Fz hFz cz vfz phasez tau 442 az
    let backgroundz : (Fin d → ℝ) → M → V :=
      jointMixedSeedBackgroundWave (0 : Z) Fz hFz gz 442 tau delta targetz probez 441
    ∀ v : ProbeParameters r, ‖v‖ < actualRepairParameterRadius packet.parameterFamily → ∀ x : M,
      actualRepairModelFirstDefectFirstMap packet.referenceMap U delta
        (actualRepairParameterMap packet.parameterFamily b p₀ (round4PairedParameterReindex r v),x) =
      scale • F0 x + delta • backgroundz (round4PairedParameterReindex r v) x +
        family.centeredPhysicalPairMap scale hscale delta tau 442 Initialized amplitude ha b p₀ v x +
        secondary (actualRepairParameterMap packet.parameterFamily b p₀
          (round4PairedParameterReindex r v),x)

/-- The exact same selected packet and increment have the stated component identity. -/
theorem generalReference_selected_packet_first_map_split
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (Tp Pphase : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (choice : ActualSecondarySignedRecord (Fin s.seed.primaryCount ⊕ Fin r) → Sub →
      Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec a, Round3ParameterChartPreserves (choice rec a).chart) :
    GeneralSelectedMapSplitStatement F0 hF0 s waves weight family B Q b p₀ hp₀
      Tp Pphase rho hrho choice hc := by
  unfold GeneralSelectedMapSplitStatement
  intro Data g0 gp Mgp Bchi Bnu Mphase Csrc amplitude ha Initialized u
    BS TS BP TP Ds Dp radius hradius reference Given packet hFamily hReference
    t ht htHalf label tau delta scale hscale F hF g target c chi nu a phase vf
    meanProbe background U secondary Fz hFz gz targetz cz vfz phasez az probez backgroundz
  have hSplit := probes_general_centered_first_map_split F0 hF0 waves weight family scale hscale
    gz tau delta 442 442 442 441 targetz Initialized amplitude ha
    (jointMixedParameterInitializedAtlas_buffer B Csrc rho hrho) b p₀ hp₀ choice hc
  have hParameter : passiveOriginalSmallParameter Initialized amplitude ha b p₀ = u :=
    jointMixedParameterInitializedAtlas_parameter B Csrc rho hrho b p₀
  have hPrimary : passiveParameterPrimary (P := P) (0 : Z) Fz gz = g := by
    exact (jointMixed_passive_rescaled_primary_binding (P := P) (0 : Z)
      (fun _ : Z => F0) (fun _ : Z => hF0) g0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)).symm
  have hTarget : (fun _ : P => targetz 0) = target := rfl
  dsimp only at hSplit
  rw [hParameter,hPrimary,hTarget] at hSplit
  simpa only [hFamily,hReference,s.map_eq,passiveGroupedFamilyJointBackground,
    U,secondary,background,meanProbe,backgroundz,probez] using hSplit

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.GeneralSelectedMapSplitStatement
#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalReference_selected_packet_first_map_split
