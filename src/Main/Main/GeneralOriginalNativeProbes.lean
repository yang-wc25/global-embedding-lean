import UpgradeContinuation.GeneralCompactTail
import UpgradeContinuation.GeneralSelectedBackground
import UpgradeContinuation.GeneralSelectedMapSplit
import ProbesClosure.GeneralComponentAssembly
import Main.GeneralFirstFields
import Main.OriginalProbeSpatial
import Main.GeneralEmptyNativeProbes
import ProbesClosure.InitializedIncrementSmooth
import ProbesClosure.CenteredInitialMap
import Main.GeneralActualProbeRepairConstruction
import Main.GeneralNativeProbeSpecialization

/-!
# Native probe data from the original immersion and the actual legal waves

All geometric, source, compact parameter, initial-state and repair choices
are constructed internally. The same initial state supplies both the
weighted first-map bounds and the starting map of its actual repair run.
The chosen family is totalized only outside the admitted scale interval.

The wave input allows an arbitrary smooth cutoff supported in a legal open
set. Its phase and normal field need be smooth only on that open set. Every
original label keeps one weight and all cross terms of its finite pieces.
The stronger open-set entrance specializes to the paper's chart-supported
entrance without changing the actual value, tensor or parameter family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold IsManifold Bundle
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal Classical

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade UpgradeContinuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

private local instance signedFinite {Label : Type*} [Fintype Label] [DecidableEq Label] :
    Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

/-- The qualitative immersion and its actual finite legal-wave list produce
the complete native analytic family. There is no initial map, repair plan,
raw supplier, quantitative geometry, or completed response among the inputs. -/
theorem general_probes_native_data_from_original [Nonempty M]
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N)
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (hPhase : PhaseRegular F0 hF0)
    (waves : Fin r → OpenSupportedLegalWave F0 hF0) :
    ∃ (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
      (hcompact : ∀ i, IsCompact (A.support i))
      (hcover : ∀ x, ∃ i, x ∈ A.support i),
      Nonempty (GeneralNativeProbeData F0 hF0 A hA hcompact hcover hImm waves) := by
  letI := referenceRiemannianBundle (n := m+1) (M := M)
  let d := Fintype.card (Fin r × Bool)
  let P := ActualRepairCompactParameter d
  let Ep := EuclideanSpace ℝ (Fin d)
  let Z := ZeroParameter
  let p0 := actualRepairCompactParameterBase d
  letI : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
  letI : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IM) (n := ∞) P M
  obtain ⟨s,B,hB,hforward,Q,hQ,BP,TP,hBP,hTP,b,hp0,hSelected⟩ :=
    generalMap_exists_compact_tail_supply hdim hambient F0 hF0 hImm hPhase waves
  let seed := s.seed
  let Data := passiveOriginalData (0 : Z) seed B Q
  let g0 := passiveOriginalReferencePrimary seed s.domain s.smooth s.freeNormal
    s.baseIndex s.refinementMultiplicity s.primary
  let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => seed.F (p,x)) g0
  obtain ⟨weight,hweight,hInjective,family,O,seeds,rho,hrho,Tp,Pphase,hTp,
    hSamples,numbers,hRho,hPrimary,hProfiles,hPacket⟩ := hSelected
  let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
  let Bchi := fun j => family.cutoffBudget (j+444)
  let Bnu := fun j => family.normalBudget (j+444)
  let Mphase := fun j => Pphase (j+1)
  let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
    m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
  let amplitude := passiveOriginalReserveAmplitude Csrc rho
  let ha := passiveOriginalReserveAmplitude_pos Csrc rho hrho
  let Initialized := jointMixedParameterInitializedAtlas B Csrc rho hrho
  let Samples := incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ
  obtain ⟨smoothingRadius,hSmoothingRadius,packet,hFamily,hReference,hOmega,hParameter,hMetric,hLocal,
    CU,CS,hCU,hCS,hSecondaryNonneg,hSecondaryLimit,
    ΒRepair,SubRepair,iΒRepair,iSubRepair,plan,t0,ht0,ht0Half,ht0Cap,hAt⟩ := hPacket
  letI := iΒRepair
  letI := iSubRepair
  obtain ⟨tSharp,htSharp,htSharpHalf,CB,hCB,hSharp⟩ :=
    generalReference_selected_packet_background_sharp F0 hF0 s waves weight family B hB Q hQ
      b p0 hp0 Tp Pphase hTp numbers rho hrho hRho hSamples hPrimary hProfiles
      packet hOmega hParameter hMetric
  let T := min t0 tSharp
  have hT : 0 < T := lt_min ht0 htSharp
  have hT0 : T ≤ t0 := min_le_left _ _
  have hTSharp : T ≤ tSharp := min_le_right _ _
  let Aout := actualRepairSamplingAtlas seed.atlas seed.sourceNormDomain
  have hAout : IsSmoothBufferedAtlas Aout :=
    actualRepairSamplingAtlas_smooth seed.atlas s.domain.atlas_smooth
      seed.sourceNormDomain s.domain.source_norm_subset
  have hOmegaCompact : ∀ i, IsCompact (seed.sourceNormDomain i) := by
    simpa only [hOmega,seed,passiveOriginalData,passiveOriginalSmallBuffer_data]
      using packet.source_compact
  have hCompact : ∀ i, IsCompact (Aout.support i) :=
    actualRepairSamplingAtlas_support_compact seed.atlas seed.sourceNormDomain
      hOmegaCompact s.domain.source_norm_subset
  have hCover : ∀ x, ∃ i, x ∈ Aout.support i := by
    have hcov := actualRepairSamplingAtlas_support_cover Data.atlas packet.Omega packet.source_sampling
    change ∀ x, ∃ i, x ∈ (actualRepairSamplingAtlas s.seed.atlas packet.Omega).support i at hcov
    rw [hOmega] at hcov
    exact hcov
  have hpQ : B.chart b p0 ∈ Q b :=
    (hQ b).2.2 (subset_closure
      (bufferedInner_subset_sampling B b (bufferedInnerCoordinates_mem B b hp0)))
  have hSampleCover := probes_background_original_samples_cover seed.atlas seed.sourceNormDomain
    s.domain.source_norm_subset B Q (fun i => (hQ i).2.1) b (B.chart b p0) hpQ
  let R := actualRepairParameterRadius (tensorChartFamilyOfAtlas Initialized)
  obtain ⟨Cparam,hCparam,etaH,etaV,hEtaH,hEtaV,hEtaHlim,hEtaVlim,hFourComponents⟩ :=
    general_probes_actual_selected_components_first_four F0 hF0 hImm waves weight hweight family
      seed.atlas s.domain.atlas_smooth seed.sourceNormDomain hOmegaCompact
      s.domain.source_norm_subset hCover B Csrc rho hrho b p0 hp0 Samples hSampleCover CB CS hCB hCS
  let Cspatial := actualProbeFirstSpatialConstant Aout hAout hCompact F0 hF0 T CU CU
  have hCspatial : 0 ≤ Cspatial :=
    actualProbeFirstSpatialConstant_nonneg Aout hAout hCompact F0 hF0 T CU CU hCU hCU
  let label := (round4PairedParameterIndex r).toEmbedding
  let Admitted := {t : ℝ // 0 < t ∧ t < T}
  choose hTau initial hMap hSecondary hWeighted hTwo hRuns using
    (fun z : Admitted => hAt z.1 z.2.1 (z.2.2.le.trans hT0) label)
  let run (z : Admitted) := Classical.choice (hRuns z)
  let F : ℝ → ProbeParameters r → M → V := fun t =>
    if h : 0 < t ∧ t < T then
      (run ⟨t,h⟩).actualRepairModelPairedFamily packet b p0 else fun _ => F0
  let G : ℝ → ProbeParameters r → M → V := fun t =>
    if h : 0 < t ∧ t < T then
      fun u => actualRepairCenteredFamily packet.parameterFamily b p0 (initial ⟨t,h⟩).map
        (round4PairedParameterReindex r u) else fun _ => F0
  have realization : ActualProbeRepairRealization (Tr := ℝ) (Λ := Fin Data.primaryCount)
      (Β := ΒRepair) (SubSecondary := SubRepair) packet plan.cost plan.Cs plan.sigma
      plan.budget plan.epsilon plan.eta T b p0 F G := by
    constructor
    intro t ht htt
    let z : Admitted := ⟨t,ht,htt⟩
    refine ⟨hTau z,initial z,run z,?_,?_⟩
    · simp only [F,z,dite_eq_left (show 0 < t ∧ t < T from ⟨ht,htt⟩)]
    · simp only [G,z,dite_eq_left (show 0 < t ∧ t < T from ⟨ht,htt⟩)]
  have hpPacket : p0 ∈ packet.parameterFamily.inner b := by
    rw [hFamily]
    exact hp0
  have hBcharts : ∀ j, (tensorChartFamilyOfAtlas Initialized).chart j ∈
      maximalAtlas 𝓘(ℝ,Ep) ∞ P := hB.chart_mem
  have hQsampling : ∀ j, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas Initialized) j ⊆ Q j := by
    intro j
    exact subset_trans subset_closure
      ((jointMixedParameterInitializedAtlas_samples B Csrc rho hrho Q hQ j).2.2)
  have hSpatial : ∀ t, 0 < t → t < T → ∀ u, ‖u‖ < R →
      probeAtlasCj Aout 2 (G t u-F0) ≤ ENNReal.ofReal (Cspatial*t^((44:ℝ)/5)) ∧
      probeAtlasCj Aout 3 (G t u) ≤ ENNReal.ofReal Cspatial := by
    intro t ht htt u hu
    let z : Admitted := ⟨t,ht,htt⟩
    have hU := probes_initialized_increment_smooth packet (initial z) _ _ (hMap z)
    have huPair : ‖round4PairedParameterReindex r u‖ < R := by
      simpa only [LinearIsometryEquiv.norm_map] using hu
    have hSpatial := probes_original_centered_first_spatial seed.atlas s.domain.atlas_smooth
      (tensorChartFamilyOfAtlas Initialized) hBcharts seed.sourceNormDomain Q
      s.domain.source_norm_subset hOmegaCompact (fun i => (hQ i).2.1) hQsampling
      F0 hF0 _ hU b p0 hp0 (round4PairedParameterReindex r u) huPair T CU t hCU ht htt
      (hWeighted z).1 (hWeighted z).2
    have hCentered := probes_centered_initial_map_of_reference packet.parameterFamily b p0
      packet.referenceMap _ (initial z).map F0 t (hMap z) hReference
      (round4PairedParameterReindex r u)
    dsimp only [G]
    rw [dite_eq_left (show 0 < t ∧ t < T from ⟨ht,htt⟩)]
    rw [hCentered,hFamily]
    exact hSpatial.2
  have hFour : ∀ t, 0 < t → t < T →
      GeneralWaveFirstFourAt F0 hF0 waves Aout weight (G t)
        (Metric.ball 0 R) R t Cparam (etaH t) (etaV t) := by
    intro t ht htt
    let z : Admitted := ⟨t,ht,htt⟩
    have htHalf : t ≤ 1/2 := (htt.le.trans hT0).trans ht0Half
    have htOne : t ≤ 1 := htHalf.trans (by norm_num)
    have hscale := actual_probe_contraction_mem_Icc t ht htHalf
    have hBackground := hSharp t ht (htt.le.trans hTSharp) label
    have hComponents := hFourComponents (Real.sqrt (1-(t^10)^2)) hscale t ht htOne
      _ _ hBackground (hSecondary z)
    have hSplit := generalReference_selected_packet_first_map_split
      F0 hF0 s waves weight family B Q b p0 hp0 Tp Pphase rho hrho
      (jointSecondarySeedPaddedChoice seeds) (jointSecondarySeedPaddedChoice_preserves seeds)
      packet hFamily hReference t ht htHalf
    apply general_probes_first_four_congr_on_open F0 hF0 waves Aout weight (Metric.ball 0 R)
      Metric.isOpen_ball _ (G t) ?_ R t Cparam (etaH t) (etaV t) hComponents
    intro u hu
    funext x
    have hur : ‖u‖ < actualRepairParameterRadius packet.parameterFamily := by
      rw [hFamily]
      simpa only [Metric.mem_ball,dist_zero_right] using hu
    have heq := hSplit u hur x
    have hmap := hMap z
    dsimp only [z] at hmap
    dsimp only [G]
    rw [dite_eq_left (show 0 < t ∧ t < T from ⟨ht,htt⟩)]
    dsimp only [actualRepairCenteredFamily]
    rw [hmap,hFamily]
    simpa only [globalWave_original_parameter_map_eq,hFamily,
      GeneralLegalWaveSeed.coordinate,z,label] using heq.symm
  let firstSeed := general_probes_first_model_of_spatial_and_four F0 hF0 Aout waves G R T
    weight hweight (fun l k hne _ => fun heq => hne (hInjective heq))
    Cspatial Cparam hCspatial etaH etaV hEtaH hEtaV hEtaHlim hEtaVlim hSpatial hFour
  have first : GeneralActualProbeFirstModelBounds F0 hF0
      (actualRepairSamplingAtlas Data.atlas packet.Omega) waves G
      (actualRepairParameterRadius packet.parameterFamily) T := by
    rw [hOmega,hFamily]
    exact firstSeed
  have hMetricOriginal : ∀ p, packet.metric p = inducedMetric (I := IM) F0 := by
    intro p
    rw [hMetric,packet.reference_tensor,hReference]
    rfl
  let native := realization.toGeneralDomainModelData packet rfl plan.epsilon_pos
    plan.small plan.displacement plan.threshold plan.tail_cap hpPacket hT
    F0 hF0 hImm hMetricOriginal waves first
  exact ⟨_,_,_,_,⟨native.toDomainData.toGeneralNativeProbeData⟩⟩

/-- The constructed native provider includes both empty and nonempty closed
sources and every finite list, including the empty list of waves. -/
theorem generalNativeProbeProvider_from_original
    (hdim : 2 ≤ m+1) (hambient : (m+1)*(m+2)/2 < N) :
    GeneralNativeProbeProvider (n := m+1) (N := N) (M := M) := by
  by_cases hM : Nonempty M
  · letI := hM
    intro F0 hF0 hImm hPhase r waves
    exact general_probes_native_data_from_original hdim hambient F0 hF0 hImm hPhase waves
  · letI : IsEmpty M := not_nonempty_iff.mp hM
    intro F hF hi _hphase r waves
    let A := GlobalEmbedding.Main.emptyNativeProbeAtlas (n := m+1) (M := M)
    have hA : IsSmoothBufferedAtlas A := GlobalEmbedding.Main.emptyNativeProbeAtlas_smooth
    have hcompact : ∀ i, IsCompact (A.support i) := fun i => Fin.elim0 i
    have hcover : ∀ x, ∃ i, x ∈ A.support i := fun x => isEmptyElim x
    exact ⟨A,hA,hcompact,hcover,
      ⟨generalNativeProbeData_of_isEmpty F hF A hA hcompact hcover hi waves⟩⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.general_probes_native_data_from_original
#print axioms GlobalEmbedding.Continuation.generalNativeProbeProvider_from_original
