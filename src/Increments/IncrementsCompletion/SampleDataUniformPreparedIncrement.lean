import IncrementsCompletion.SamplePrimaryMeanRealization
import IncrementsCompletion.AtScalePhysicalGeometry
import IncrementsCompletion.AtScaleSecondaryUniformCoherent
import IncrementsCompletion.SamplePrimarySecondaryRaw
import IncrementsCompletion.OriginalFiniteSupportedAssembly

/-!
# Numeric constants before the parameter manifold and original datum

The original Data, parameter manifold, actual scale, neighborhood/parent partition, finite signed packet,
secondary profile certificates, finite primary index, primary family, and
current-scale preparation all occur after the literal threshold and C.
A genuine common secondary frame reserve is a numeric budget; the real
frame bounds are weakened to it before running the actual geometry producer.
No unproved monotonicity of a solver cost or all-scale jet certificate is used.

Every K/E/G/choice/raw/U is manufactured inside the actual scale. Original
finite-budget production of the primitive numbers, supports/collars and
common reserve is still unclosed; this is an internal prepared theorem,
not a replacement original target or a target-count acceptance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open SourceCollarsBridge CollarCompletion
universe uM uP uB
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance incrementsSampleDataUniformExactThresholdSignedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem incrementsCompletion_sample_data_uniform_prepared_increment
    (rho : ℝ) (hrho : 0 < rho) (c : ℝ)
    (L : ℕ)
    (secondaryReserve : ℝ) (hSecondaryReserve : 0 < secondaryReserve)
    (SecondaryInverse SecondaryCutoff SecondaryObserver : ℕ → ℝ)
    (hSecondaryInverse : ∀ k, 0 ≤ SecondaryInverse k)
    (hSecondaryCutoff : ∀ k, 0 ≤ SecondaryCutoff k)
    (hSecondaryObserver : ∀ k, 0 ≤ SecondaryObserver k)
    (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (Rsub Lactive : ℕ)
    (q : ℕ) (hq : 1 ≤ q) (Packet : ℕ → ℝ) (hPacket0 : ∀ k, 0 ≤ Packet k)
    :
    let Theta := finiteOriginalMeanThreshold.{uM,uB} (m := m) (d := d) (N := N) (M := M)
      q Rsub Lactive rho c cT hrho Packet Forward Meta Tinv hPacket0 hForward
    0 < Theta ∧ Theta ≤ 1 ∧
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧
    ∀ (P : Type uP) [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c),
    ∀ (_hPrimaryCount : ∀ z ∈ Data.parameterSet ×ˢ (univ : Set M),
      (Finset.univ.filter (fun nu => z ∈ incrementsOriginalRelativeCutoffSupport Data nu)).card ≤ Lactive),
    ∀ ell, 0 < ell → ell ≤ 1 →
    (∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤) →
    (∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n) →
    ∀ (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (hMargin : ∀ r i (a : secondary.s r i), secondaryReserve ≤ (secondary.piece r i a).cT)
    (secondaryProfiles : IncrementsCompletionAtScaleSecondaryPacketProfiles Data hd hs theta secondary ell
      SecondaryInverse SecondaryCutoff SecondaryObserver),
    ∀ (Β : Type uB) [Fintype Β] (primaryHost : Β → Fin Data.atlas.count)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (hPhase : ∀ nu, g.phase nu = Data.phase nu) (hCutoff : ∀ nu, g.cutoff nu = Data.cutoff nu)
    (prep : ∀ i, IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub ell i),
    ∀ epsilon, 0 < epsilon → epsilon < Theta → ∀ delta, 0 ≤ delta → delta ≤ epsilon*ell →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ incrementsOriginalParameterRegion Data ∧
      Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) G Data.F U Data.H q delta (epsilon*ell) ell Cmap Cmetric ∧
      FullIncrementNovOriginalSupportConclusion Data.cutoff G U := by
  intro Theta
  let Csize := finiteOriginalMeanSizeCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT hrho Packet Forward Meta Tinv hPacket0 hForward
  let Cdiff := finiteOriginalMeanDifferenceCost.{uM,uB} (m := m) (d := d) (N := N) (M := M)
    q Rsub Lactive rho c cT hrho Packet Forward Meta Tinv hPacket0 hForward
  let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*Packet 0+1))
  have hradius : 0 < radius := div_pos hrho (by have hh := hPacket0 0; positivity)
  have hTheta : 0 < Theta ∧ Theta ≤ 1 :=
    parameterRound2_uniformMeanThreshold_pos Packet Csize radius hradius q (q+4)
  let R := parameterRound2_uniformMeanProfile Packet Csize (q+4)
  let Bnd := fun s => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
    c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) (R q (s+(q+4))) Tinv
  let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
    c cT (1+Forward (s+(q+4))) Tinv
  let T := parameterRound2_identityRawTransition m d Packet Forward
  let Cmean := finitePhysicalMeanCost Packet Csize Cdiff q
  have hBnd (s) : 0 ≤ Bnd s := parameterRound2_identityRawBnd_nonneg _ _ _ _ _ _ _ _ _ _ (hPacket0 _) _
  have hT (k) : 0 ≤ T k := parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket0 hForward k
  have hCmean (j) : 0 ≤ Cmean j := finitePhysicalMeanCost_nonneg Packet Csize Cdiff q j
  let Ti := SecondaryInverse
  let To := SecondaryObserver
  let Cut := fun j => SecondaryCutoff (actualSecondarySolveOrder q j)
  let Mrest := incrementsCompletionUniformSecondaryGeometryCost m d N Ti To secondaryReserve q c Packet
  have hTi := hSecondaryInverse
  have hTo := hSecondaryObserver
  have hCut (j) : 0 ≤ Cut j := hSecondaryCutoff _
  have hMrest (j) : 0 ≤ Mrest j := incrementsCompletionUniformSecondaryGeometryCost_nonneg
    m d N Ti To secondaryReserve q c Packet j
  let Msec := fun j => max (Mrest j) (Mg (j+q+4))
  have hMsec (j) : 0 ≤ Msec j := (hMrest j).trans (le_max_left _ _)
  obtain ⟨Cmap,Cmetric,hCmap,hCmetric,hFinish⟩ :=
    incrementsCompletion_original_finite_supported_assembly.{uM,0,uP,uB,0}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      q Rsub Lactive (L*5^Module.finrank ℝ (Ep × D)) hq (rho/4)
      (div_pos hrho (by norm_num)) Cmean hCmean (fun j => Bnd (j+q+4)) Msec Cut
      (fun _ => T) (fun _ => Ti) (fun _ => To)
      (fun j => hBnd (j+q+4)) hMsec hCut (fun _ => hT) (fun _ => hTi) (fun _ => hTo)
  refine ⟨hTheta.1,hTheta.2,Cmap,Cmetric,hCmap,hCmetric,?_⟩
  intro P _ _ _ Data hd hs hn hp hImm hLinear hDecomp hReserve hEll hPrimaryCount ell hell hell1 hGiven hPacket V0 hV0 hKV0 theta secondary hSupport hPart hCount hMargin
    secondaryProfiles Β _ primaryHost g hPreserves hTarget hPhase hCutoff prep
    epsilon he heTheta delta hdelta hdt
  let Sub := fun r => Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(secondary.s r i))
  letI : ∀ r, Fintype (Sub r) := fun _ => inferInstance
  have hSecondary := incrementsCompletion_at_scale_uniform_secondary_coherent_factory Data hd hs hImm
    theta secondary hSupport V0 hPart L hCount SecondaryInverse SecondaryCutoff SecondaryObserver
    hSecondaryInverse hSecondaryCutoff hSecondaryObserver secondaryReserve hSecondaryReserve hMargin
    q c Packet ell hell hell1 secondaryProfiles
  let hActive := active_slices_from_original_data Data hd hs g hPreserves hTarget
  have hReal : Nonempty (IncrementsCompletionFiniteMeanRealization Data hd hs g hTarget hActive V0
      q Rsub rho ell (epsilon*ell) Cmean Bnd Mg T) :=
    incrementsCompletion_sample_finite_mean_realization Data hd hs hn hp g hPreserves hTarget
      V0 hV0 hKV0 hImm ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve Lactive hPrimaryCount q Rsub hq
      Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep epsilon he heTheta
  obtain ⟨realization⟩ := hReal
  let primary := realization.primary
  let G := primary.domain
  let hG := primary.domain_open
  let F := fullIncrementNovOriginalSourceSlice Data
  let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
  let gG := round3Parameter_restrictPrimaryFamily F (fullIncrementNovOriginalOpenFamily Data g hTarget) G hG
  have hCoreFinite (n) : incrementsOriginalCoreInputProfile Data n ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven n) (actualOriginalGivenInputProfile_core_le Data n ell)
  have hCoreBudget (n) : (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ Packet n :=
    (ENNReal.toReal_mono (hGiven n) (actualOriginalGivenInputProfile_core_le Data n ell)).trans (hPacket n)
  have hPhysical (i) := incrementsCompletion_at_scale_physical_geometry Data hd hs hn hImm g hTarget
    V0 cT hcT Tinv Forward Meta Rsub i ell (prep i) G hG
  obtain ⟨choice,hChoice,family,hFamily⟩ := hSecondary Msec (fun _ => le_max_left _ _)
    G hG primary.original_region (fun z hz => (primary.prepared_parameters hz).1)
    hEll hCoreFinite hCoreBudget Β primaryHost gG hPhase hCutoff hPhysical
  have hTau : 0 < epsilon*ell := mul_pos he hell
  have hTaul : epsilon*ell ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (heTheta.le.trans hTheta.2) hell.le
  have hResidual : ∀ z ∈ incrementsOriginalParameterRegion Data,
      realization.residual.val.val z.1 z.2 =
        fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g realization.input hActive (q+2)
          (epsilon*ell) z.1 z.2-Data.H z.1 z.2 := by
    intro z hz
    exact congrFun (congrFun realization.literal z.1) z.2
  have hRaw := incrementsCompletion_sample_secondary_raw_from_actual_primary Data hd hs g hTarget
    V0 realization.input Lactive (funext hCutoff) hPrimaryCount q Rsub rho ell (epsilon*ell)
    Bnd Mg T primary Msec Cut Ti To (fun _ => le_max_right _ _)
    (L*5^Module.finrank ℝ (Ep × D)) choice family hFamily delta
  have hOut := hFinish P Β (Sigma Sub) Data hd hs g hPreserves hTarget hActive (funext hCutoff)
    ell delta (epsilon*ell) hTau hTaul hell1 hdelta hdt realization.input G hG
    primary.original_region primary.original_parameters primary.parameter_cover realization.residual
    hResidual realization.bound choice hChoice hRaw
  let U := round3ParameterIncrementMap F hF gG realization.input (q+2) (epsilon*ell) delta choice
  exact ⟨G,U,hG,primary.original_parameters,primary.original_region,hOut.1,hOut.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_sample_data_uniform_prepared_increment
