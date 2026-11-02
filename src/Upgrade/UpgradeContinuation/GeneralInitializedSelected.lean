import UpgradeContinuation.GeneralInitializedSelectedStatement

/-!
# Same initialized first state with its original source and primary witnesses

This follows the existing initialized-secondary construction with the same
single q440 choice and literal original parameter buffer. The additional
outputs retain the source raw-profile witness and the numerical canonical
supplier selected inside that construction. They make the background sharp
consumer applicable without any new wave family, source cost or reserve
choice. Closed-state normalization, metric identities and secondary responses
are all produced by the already established same-map chain.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical BigOperators
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
private theorem probes_general_initialized_selected_ratio_threshold (cap : ℝ) (hcap : 0 < cap) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1/2 ∧ ∀ t : ℝ, 0 < t → t ≤ s →
      t^((6 : ℝ)/5)/t^((11 : ℝ)/10) < cap := by
  let a := min cap 1
  have ha : 0 < a := lt_min hcap (by norm_num)
  have haCap : a/2 < cap := (by linarith : a/2 < a).trans_le (min_le_left _ _)
  let s := min (1/2) ((a/2)^10)
  have hs : 0 < s := lt_min (by norm_num) (pow_pos (by positivity) _)
  refine ⟨s,hs,min_le_left _ _,?_⟩
  intro t ht hts
  have htPower : t ≤ (a/2)^10 := hts.trans (min_le_right _ _)
  have hpower : ((a/2)^10)^((1 : ℝ)/10) = a/2 := by
    rw [← Real.rpow_natCast (a/2) 10,← Real.rpow_mul (by positivity : 0 ≤ a/2)]
    norm_num
  have he := Real.rpow_le_rpow ht.le htPower (by norm_num : (0 : ℝ) ≤ 1/10)
  rw [hpower] at he
  have hid : t^((6 : ℝ)/5)/t^((11 : ℝ)/10) = t^((1 : ℝ)/10) := by
    rw [← Real.rpow_sub ht]
    norm_num
  rw [hid]
  exact he.trans_lt haCap

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
private local instance probesSelectedGeneralInitializedSignedFintype
    {Label : Type*} [Fintype Label] [DecidableEq Label] : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance
variable {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {referenceCost Given : ℕ → ℝ}

theorem probes_exists_general_initialized_closed_state_with_source_and_secondary
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
    {BP0 TP0 : ℕ → ℝ} {Dp0 : ℕ} {radius0 : ℝ} {hradius0 : 0 < radius0}
    {reference0 Given0 : ℕ → ℝ}
    (fixed : Round3RepairFixedSmoothingPacket seed BS TS BP0 TP0 Ds Dp0 radius0 hradius0 reference0 Given0)
    (hReference0 : seed.F = fixed.referenceMap)
    (hOmega0 : seed.sourceNormDomain = fixed.Omega) (hQ0 : seed.parameterNormDomain = fixed.Q)
    (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => seed.F (0,x)))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x)) hF0) :
    ∃ B : BufferedAtlas P Ep, ∃ hB : IsSmoothBufferedAtlas B,
    ∃ hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i),
    ∃ Q : Fin B.count → Set Ep,
    ∃ hQ : ∀ i, IsCompact (Q i) ∧ Q i ⊆ (B.chart i).target ∧
      closure (bufferedSamplingCoordinates B i) ⊆ Q i,
    ∃ BP TP : ℕ → ℝ, (∀ k, 0 ≤ BP k) ∧ (∀ k, 0 ≤ TP k) ∧
    ∀ (b : Fin B.count) (p₀ : P) (hpP : p₀ ∈ B.inner b),
      ProbesSelectedGeneralInitializedSecondaryStatement (BS := BS) (TS := TS) (BP := BP) (TP := TP) (Ds := Ds)
        seed hd₀ hs₀ hp₀ hn₀ hi₀ hAll base hId Rsub primaryPacket cF reserve0 he₀ hl₀ hc₀ hr₀
        B hB hforward Q (fun i => (hQ i).1) (fun i => (hQ i).2.1)
        hF0 waves b p₀ hpP := by
  have hseed : (0 : Z) ∈ seed.parameterSet := by rw [hAll]; trivial
  have hzero : (0 : Z) ∈ seed.parameterOpen := hd₀.parameter_subset hseed
  let SeedPacket := fun j => (actualOriginalGivenInputProfile seed j 1).toReal
  have hSeed := passiveOriginal_fixed_reference_given_budget seed fixed hReference0 hAll hOmega0 hQ0
  obtain ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,hPackets⟩ :=
    passiveOriginal_exists_initialized_physical_fixed_packet (P := P) (d := d)
      seed hs₀ fixed hseed hReference0 hOmega0 hQ0
  refine ⟨B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,?_⟩
  intro b p₀ hpP
  unfold ProbesSelectedGeneralInitializedSecondaryStatement
  intro Data F0 g0 gp K
  obtain ⟨weight,hweight,hInjective,family,O,hO,hKO,⟨seeds⟩⟩ :=
    generalOriginal_exists_injective_mixed_atlas_seed («Ep» := Ep) seed hd₀ hs₀ hp₀ hi₀ hzero hF0 waves
  have hInner (i : Fin B.count) (p : P) (hp : p ∈ B.inner i) : B.chart i p ∈ Q i := by
    apply (hQ i).2.2
    apply subset_closure
    apply bufferedInner_subset_sampling B i
    refine ⟨(B.chart i).map_source (B.inner_subset i hp),?_⟩
    change (B.chart i).symm (B.chart i p) ∈ B.inner i
    simpa only [(B.chart i).left_inv (B.inner_subset i hp)] using hp
  let hd := passiveOriginalData_domain (0 : Z) seed hd₀ hzero B hB Q
    (fun i => (hQ i).2.1) hInner
  have hb0 : (0 : Z) ∈ (seed.parameterChart base.2).target := by rw [hId]; trivial
  let hs := passiveOriginalData_smooth (0 : Z) seed hs₀ hzero base.2 hb0 B Q
  have hOmegaCompact i : IsCompact (seed.sourceNormDomain i) := by
    rw [hOmega0]
    exact fixed.source_compact i
  have hSamples : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ i) :=
    parameterRound2_originalEvaluation_univ_compact seed.atlas B.chart seed.sourceNormDomain Q
      hOmegaCompact (fun i => (hQ i).1) hd₀.source_norm_subset (fun i => (hQ i).2.1)
  have hSampling (i : Fin B.count) :
      tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i := by
    change bufferedSamplingCoordinates B i ⊆ Q i
    exact subset_trans subset_closure (hQ i).2.2
  obtain ⟨rho,hrho,Tp,Pphase,hpCost,numbers,hRhoNumbers,hPrimarySupply,hPrescribed,hcomplete⟩ := probes_selected_general_original_q440_with_secondary
    seed hd₀ hs₀ hp₀ hn₀ hi₀ hAll base hId Rsub primaryPacket cF reserve0 he₀ hl₀ hc₀ hr₀
    B hB hforward Q (fun i => (hQ i).1) (fun i => (hQ i).2.1) hSampling hd hs hOmegaCompact
    SeedPacket hSeed hF0 waves weight hweight family b p₀ hpP O seeds
  refine ⟨weight,hweight,hInjective,family,O,seeds,rho,hrho,Tp,Pphase,hpCost,
    hSamples,numbers,hRhoNumbers,hPrimarySupply,hPrescribed,?_⟩
  intro Mgp Bchi Bnu Mphase Csrc amplitude Initialized u
  let parameterCap := amplitude/(‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1)
  have hParameterCap : 0 < parameterCap := div_pos
    (passiveOriginalReserveAmplitude_pos Csrc rho hrho) (by positivity)
  obtain ⟨radius,hradius,packet,hFamily,hReference,hOmegaReverse,hQReverse,hmetric,hRaw⟩ :=
    hPackets parameterCap hParameterCap
  have hOmega : seed.sourceNormDomain = packet.Omega := hOmegaReverse.symm
  have hQpacket : Q = packet.Q := hQReverse.symm
  refine ⟨radius,hradius,packet,hFamily,hReference,hOmegaReverse,hQReverse,hmetric,?_,?_⟩
  · intro v hv
    rw [hFamily] at hv ⊢
    exact ((jointMixed_parameter_initialized_original_germ B Csrc rho hrho b p₀ hpP v hv).eq_of_nhds)
  let H0 := passiveOriginalPacketReferenceGerm packet rfl hOmega hQpacket hmetric
  let HBound := actualProbeInitialReferenceProfile packet hmetric
  obtain ⟨cap,CU,CE,CS,hcap,hCU,hCE,hCS,hSecondaryNonneg,hSecondaryLimit,hresult⟩ :=
    hcomplete H0 rfl HBound
  refine ⟨CU,CS,hCU,hCS,hSecondaryNonneg,hSecondaryLimit,?_⟩
  intro epsilonRepair eta capRepair hepsilonRepair heta hcapRepair budget hbudget
  obtain ⟨centerCap,hCenterCap,hCenterOne,hcenter⟩ :=
    passiveOriginalPacket_target_center_threshold packet rfl hOmega hQpacket hmetric
      hSamples (2*rho) (mul_pos (by norm_num) hrho)
  obtain ⟨forcedCap,hForcedCap,hForcedHalf,hforced⟩ := probes_general_initialized_selected_ratio_threshold cap hcap
  obtain ⟨t0,ht0,ht0Cap,hstate⟩ := actualRepairModelFirstDefect_exists_closed_state_scale
    packet rfl hmetric CU CE budget epsilonRepair eta (min capRepair (min forcedCap centerCap)) hCU
    hepsilonRepair heta (lt_min hcapRepair (lt_min hForcedCap hCenterCap)) hbudget
  have ht0Repair : t0 ≤ capRepair := ht0Cap.trans (min_le_left _ _)
  have ht0Forced : t0 ≤ forcedCap := (ht0Cap.trans (min_le_right _ _)).trans (min_le_left _ _)
  have ht0Center : t0 ≤ centerCap := (ht0Cap.trans (min_le_right _ _)).trans (min_le_right _ _)
  have ht0Half : t0 ≤ 1/2 := ht0Forced.trans hForcedHalf
  refine ⟨t0,ht0,ht0Half,ht0Repair,?_⟩
  intro t ht htt label tau ell delta scale hscale F hF g target c chi nu a phase vf meanProbe background U secondary
  have htHalf : t ≤ 1/2 := htt.trans ht0Half
  have ht1 : t ≤ 1 := htHalf.trans (by norm_num)
  have hell : 0 < ell := Real.rpow_pos_of_pos ht _
  have hell1 : ell ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have htau : 0 < tau := Real.rpow_pos_of_pos ht _
  have htaul : tau ≤ ell := Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hdelta : 0 < delta := pow_pos ht _
  have hdeltatau : delta ≤ tau := by
    change t^10 ≤ t^((6 : ℝ)/5)
    rw [← Real.rpow_natCast t 10]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  let epsilon := tau/ell
  have he : 0 < epsilon := div_pos htau hell
  have hecap : epsilon < cap := hforced t ht (htt.trans ht0Forced)
  have heq : epsilon*ell = tau := div_mul_cancel₀ tau hell.ne'
  let H := passiveOriginalPacketTargetGerm packet rfl hOmega hQpacket hmetric t
  have hH j : parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) univ hSamples (fun _ _ hy => hy.1) ell j H ≤ HBound j :=
    passiveOriginalPacket_target_profile packet rfl hOmega hQpacket hmetric hSamples t ht ht1 ell hell1 j
  have hCenter : parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) univ hSamples (fun _ _ hy => hy.1) ell 0 (H-H0) ≤ rho := by
    simpa only [H,H0,Data,passiveOriginalSmallBuffer_data,
      mul_div_cancel_left₀ rho (by norm_num : (2 : ℝ) ≠ 0)] using
      hcenter t ht (htt.trans ht0Center) ell hell1
  have hcpl := hresult scale hscale ell hell hell1 H hH hCenter label epsilon he hecap delta hdelta
  rw [heq] at hcpl
  obtain ⟨hmain,hSecondary⟩ := hcpl hdeltatau
  obtain ⟨hcoord,hUW,hU2,error,hvalue,herror⟩ := hmain
  have hSecondaryB := hSecondary t ht ht1 rfl rfl rfl
  change actualProbeInitialSecondaryBallBounds seed.atlas seed.sourceNormDomain B CS t secondary at hSecondaryB
  have hSecondaryInitialized := actualProbeInitialSecondaryBallBounds_initialized
    seed.atlas seed.sourceNormDomain B CS t secondary Csrc rho hrho hSecondaryB
  change (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧
    incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ i ⊆ G ∧
    G ⊆ incrementsOriginalDifferentiation seed.atlas B.chart i ∧
    ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates seed.atlas B.chart U i) G) at hcoord
  change (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
    (incrementsOriginalDifferentiation seed.atlas B.chart)
    (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ) ≠ ⊤ ∧
    (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates seed.atlas B.chart U)
      (incrementsOriginalDifferentiation seed.atlas B.chart)
      (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ)).toReal ≤ CU*delta/tau) at hUW
  change (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
    (incrementsOriginalDifferentiation seed.atlas B.chart)
    (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ) ≠ ⊤ ∧
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates seed.atlas B.chart U)
      (incrementsOriginalDifferentiation seed.atlas B.chart)
      (incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ)).toReal ≤ CU*delta/tau) at hU2
  let packetError := (passiveOriginalPacketGermEquiv packet rfl hOmega hQpacket).symm error
  have hPacketValue : packetError.val = incrementsOriginalMetricError
      (fun z => Real.sqrt (1-(t^10)^2) • packet.referenceMap z) U
      (actualProbeInitialTargetGerm packet hmetric t).val (t^10) := by
    change error.val = _
    rw [hReference]
    exact hvalue
  have hPacketBound : parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart
      packet.closedSamples univ packet.closedSamples_compact (fun _ _ hy => hy.1) tau 440 packetError ≤
      CE*(delta*(tau/ell)^440+delta^3/tau) := by
    exact (passiveOriginalPacketGermEquiv_symm_seminorm packet rfl hOmega hQpacket hSamples
      tau 440 error).le.trans herror
  obtain ⟨normalized,hNormalized,hNorm⟩ := actualProbeInitialSupply_normalize_packet_error
    packet hmetric U CE t ht ht1 packetError hPacketValue hPacketBound
  have hS := packet.originalSamples_eq_closed rfl hOmega hQpacket
  have hchart : packet.parameterFamily.chart = B.chart := packet.chart_eq
  have hcoordPacket : ∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ packet.closedSamples i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U i) G := by
    rw [hchart,← hS]
    exact hcoord
  have hU2Packet : (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
      CU*delta/tau := by
    rw [hchart,← hS]
    exact hU2.2
  have hUWPacket : (paperAtlasWeighted 2 440 tau (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart U)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples).toReal ≤
      CU*delta/tau := by
    rw [hchart,← hS]
    exact hUW.2
  obtain ⟨initial,hInitial⟩ :=
    hstate t ht htt U hcoordPacket hU2Packet hUWPacket univ normalized hNormalized hNorm
  exact ⟨initial,hInitial,hSecondaryInitialized,hUW,hU2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_exists_general_initialized_closed_state_with_source_and_secondary
