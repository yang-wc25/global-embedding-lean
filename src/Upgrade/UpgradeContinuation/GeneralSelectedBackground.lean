import UpgradeContinuation.GeneralSelectedBackgroundSupply
import NormalPolar.PassiveOriginalPacketRawBridge
import Main.OriginalProbeThresholds

/-!
# The same selected general-cutoff packet supplies the sharp background

The reference germ, actual contracted target, every target profile, and the
target-center bound are manufactured from the selected physical packet.
The resulting cap and background constant are chosen before t.  The primary
supplier and prescribed profiles are the witnesses retained by that same
selection; no new source, reserve, or initialized parameter ball is chosen.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold Bundle GlobalEmbedding.Paper GlobalEmbedding.Offline
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
open scoped ContDiff Topology Classical ENNReal

namespace GlobalEmbedding.Continuation.UpgradeContinuation

universe uM uP
variable {m d N r : ℕ} {M : Type uM} {P : Type uP}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
  [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => ZeroParameter
local notation "IM" => 𝓘(ℝ,D)

/-- No targetwise germ, raw supply, geometry record, or profile remains as
an input.  The exact background is evaluated at the original probe scales
and uses the same selected primary and prescribed family. -/
theorem generalReference_selected_packet_background_sharp
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (s : OriginalReferenceSupply (m := m) (N := N) F0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep)
    (hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (Tp Pphase : ℕ → ℝ) (hTp : ∀ k, 0 < Tp k ∧ 0 < Pphase k)
    (numbers : Round3RepairMeanPrimitiveProfiles) (rho : ℝ) (hrho : 0 < rho)
    (hrhoEq : rho = numbers.rho/2) :
    let A := s.seed.atlas
    let Samples := incrementsOriginalEvaluation A B.chart s.seed.sourceNormDomain Q univ
    ∀ (hSamples : ∀ i, IsCompact (Samples i)),
    let hDomain : ∀ i, Samples i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
    let Data := passiveOriginalData (0 : Z) s.seed B Q
    let g0 := passiveOriginalReferencePrimary s.seed s.domain s.smooth s.freeNormal
      s.baseIndex s.refinementMultiplicity s.primary
    let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => s.seed.F (p,x)) g0
    ProbesSelectedPrimarySupplier A B Samples hSamples hDomain F0 hF0 gp Data.primaryDomain Data.H numbers →
    ProbesSelectedGeneralProfiles F0 hF0 waves weight family A B Samples Tp Pphase →
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
    ∀ {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
      {reference Given : ℕ → ℝ}
      (packet : Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hradius reference Given),
    packet.Omega = s.seed.sourceNormDomain → packet.Q = Q → packet.metric = Data.H →
    ∃ tSharp : ℝ, ∃ htSharp : 0 < tSharp, ∃ htSharpHalf : tSharp ≤ 1/2,
    ∃ Cbg : ℝ, 0 ≤ Cbg ∧
    ∀ (t : ℝ) (ht : 0 < t) (htt : t ≤ tSharp) (label : (Fin r × Bool) ↪ Fin d),
    let tau := t^((6 : ℝ)/5)
    let ell := t^((11 : ℝ)/10)
    let delta := t^10
    let scale := Real.sqrt (1-delta^2)
    let hscale := actual_probe_contraction_mem_Icc t ht (htt.trans htSharpHalf)
    let F := fun _ : Z => scale • F0
    let hF := fun _ : Z => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : Z => F0) (fun _ => hF0) g0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    let target := (1-(tau^10/delta)^2) • s.seed.H
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z → D → M :=
      fun l a (_ : Z) => ((family.piece l).seed.outer a).chart.symm
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → Z × D → ℝ :=
      fun l a (z : Z × D) => (family.piece l).seed.cutoffCoordinates a (0,z.2)
    let nu : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l a z x) := fun l a (_ : Z) x => actualRescaledNormal F0 hF0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) (((family.piece l).seed.outer a).chart.symm x)
      ((waves l).normal (((family.piece l).seed.outer a).chart.symm x))
    let charts : (l : Fin r) → Fin (family.piece l).seed.refinement.count →
        OpenPartialHomeomorph (Z × M) (Z × D) := fun l a => (family.piece l).seed.physicalChart a
    let phase : Fin r → Z × M → ℝ := fun l (z : Z × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (a : Fin (family.piece l).seed.refinement.count) → (z : Z) → (x : D) →
        normalSpace (I := IM) (F z) (c l a z x) :=
      fun l a z x => (-(delta*tau)/(weight l)^2) • (chi l a (z,x) • nu l a z x)
    let probe := jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase tau 442 charts
    ProbesBackgroundNativeSharp A Initialized Samples b tau Cbg
      (jointMixedSeedBackgroundWave (0 : Z) F hF g 442 tau delta target probe 441) := by
  intro A Samples hSamples hDomain Data g0 gp hPrimary hProfiles
    Mgp Bchi Bnu Mphase Csrc Initialized BS TS BP TP Ds Dp radius hradius reference Given
    packet hOmega hParameter hMetric
  let HBound := actualProbeInitialReferenceProfile packet hMetric
  let H0 := passiveOriginalPacketReferenceGerm packet rfl hOmega.symm hParameter.symm hMetric
  obtain ⟨cap,Cbg,hcap,hCbg,hSharp⟩ :=
    generalReference_selected_background_sharp F0 hF0 s waves weight family B hB Q hQ
      b p₀ hp₀ Tp Pphase hTp numbers rho hrho hrhoEq hSamples hPrimary hProfiles HBound
  obtain ⟨centerCap,hCenterCap,hCenterOne,hCenter⟩ :=
    passiveOriginalPacket_target_center_threshold packet rfl hOmega.symm hParameter.symm hMetric
      hSamples (2*rho) (mul_pos (by norm_num) hrho)
  let common := probesCommonThreshold 1 centerCap cap
  have hCommon : 0 < common := probesCommonThreshold_pos (by norm_num) hCenterCap hcap
  let tSharp := common/2
  have htSharp : 0 < tSharp := div_pos hCommon (by norm_num)
  have htSharpCommon : tSharp < common := by dsimp only [tSharp]; linarith
  have htSharpHalf : tSharp ≤ 1/2 :=
    (probesCommonThreshold_conditions hcap tSharp htSharp htSharpCommon).2.2.1
  refine ⟨tSharp,htSharp,htSharpHalf,Cbg,hCbg,?_⟩
  intro t ht htt label tau ell delta scale hscale F hF g target c chi nu charts phase vf probe
  have hConditions := probesCommonThreshold_conditions hcap t ht (htt.trans_lt htSharpCommon)
  have ht1 : t ≤ 1 := hConditions.1
  have hell : 0 < ell := Real.rpow_pos_of_pos ht _
  have hell1 : ell ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have htau : 0 < tau := Real.rpow_pos_of_pos ht _
  have hdelta : 0 < delta := pow_pos ht _
  let epsilon := tau/ell
  have hepsilon : 0 < epsilon := div_pos htau hell
  have hepsilonCap : epsilon < cap := hConditions.2.2.2
  have heq : epsilon*ell = tau := div_mul_cancel₀ tau hell.ne'
  let H := passiveOriginalPacketTargetGerm packet rfl hOmega.symm hParameter.symm hMetric t
  have hH : ∀ j, parameterRound2_originalTensorGermSeminorm A B.chart Samples univ
      hSamples hDomain ell j H ≤ HBound j := fun j =>
    passiveOriginalPacket_target_profile packet rfl hOmega.symm hParameter.symm hMetric
      hSamples t ht ht1 ell hell1 j
  have hNear : parameterRound2_originalTensorGermSeminorm A B.chart Samples univ
      hSamples hDomain ell 0 (H-H0) ≤ rho := by
    simpa only [H,H0,Data,A,Samples,hDomain,passiveOriginalData,
      mul_div_cancel_left₀ rho (by norm_num : (2 : ℝ) ≠ 0)] using
      hCenter t ht hConditions.2.1 ell hell1
  have hTarget : H.val = (fun _ : P => target 0) := rfl
  have hResult := hSharp scale hscale ell hell hell1 H0 H rfl hNear hH target hTarget
    label epsilon hepsilon hepsilonCap delta hdelta
  rw [heq] at hResult
  exact hResult

end GlobalEmbedding.Continuation.UpgradeContinuation

#print axioms GlobalEmbedding.Continuation.UpgradeContinuation.generalReference_selected_packet_background_sharp
