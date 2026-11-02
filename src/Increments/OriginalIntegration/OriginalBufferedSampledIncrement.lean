import OriginalIntegration.IncrementOutput
import OriginalIntegration.NormBufferedDataTransport
import OriginalIntegration.OriginalPrimaryInteraction
import FaithfulCollars.OriginalBufferedRawPair
import FaithfulCollars.OverlapOnlyRawSupply
import FaithfulRepair.OriginalGivenFiniteness
import OriginalIncrements.ActualSampledCommonRawOutput
import CollarCompletion.OriginalSourceCompactness

/-!
# Fully original sampled finite entrance with actual common geometry

Every raw, compact carrier, primary/secondary packet and all-order finiteness
certificate is manufactured internally. Both phase families use the same
actual chosen phases and genuine compact-carrier restriction reserves; all
high observer jets are obtained from the original Given samples. One positive four-scalar low
geometry budget is selected before q and every admitted finite prefix.
The displayed threshold uses only common numerical formulas, the fixed M,
and the actual original interaction degree. It has no atlas, chart index,
phase function, actual packet or observation order argument.

The fixed decomposition and original geometry precede this manufactured
low budget. No uniform low geometry over arbitrary unrelated data is claimed.
The original Omega/Q, F/H, supports and the same U at all orders are retained.
Only genuine overlap transitions are required for the original parameter
charts; intersecting an enlarged support with its chart source is internal.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulCollars FaithfulIncrements FaithfulIntegration FaithfulRepair CollarCompletion OriginalIncrements

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem original_buffered_sampled_common_increment
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (RSrc bSrc RPar bPar : ℝ)
    (gS : OriginalSourceNormBuffer Data.atlas Data.sourceNormDomain RSrc bSrc)
    (WParam : Fin Data.parameterCount → Set P)
    (gP : OriginalParameterNormBuffer Data.parameterChart Data.parameterNormDomain
      WParam Data.parameterSet RPar bPar)
    (TS TP Parameter Spatial : ℕ → ℝ)
    (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Ds Dp : ℕ) (hDs : Data.atlas.supportDegree ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree WParam i ≤ Dp)
    (hSTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.atlas.chart p).target,
      (Data.atlas.chart p).symm y ∈ Data.atlas.support i →
      ‖iteratedFDeriv ℝ j (Data.atlas.chart i ∘ (Data.atlas.chart p).symm) y‖ ≤ TS j)
    (hPTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.parameterChart p).target,
      (Data.parameterChart p).symm y ∈ WParam i →
      (Data.parameterChart p).symm y ∈ (Data.parameterChart i).source →
      ‖iteratedFDeriv ℝ j (Data.parameterChart i ∘ (Data.parameterChart p).symm) y‖ ≤ TP j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    : ∃ (BS BP : ℕ → ℝ) (cT Mb BInv HGrid : ℝ),
      (∀ j, 0 ≤ BS j) ∧ (∀ j, 0 ≤ BP j) ∧
      0 < cT ∧ 0 < Mb ∧ 0 < BInv ∧ 0 < HGrid ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ (allowed : ℕ → ℝ)
        (hAllowed : ∀ j, j ≤ (q+1)*(q+4)+2 → 0 ≤ allowed j),
      let J := (q+1)*(q+4)+2
      let Rsub := ((Ds+1)*(Dp+1))*5^Module.finrank ℝ (Ep × D)
      let Theta := commonFiniteThreshold (m := m) (d := d) (N := N) (M := M)
        q Rsub (originalPrimaryInteractionDegree Data+1) rho c cT Mb BInv HGrid hReserve.reserve_pos
        BS TS BP TP Parameter Spatial allowed Ds Dp hAllowed
      0 < Theta ∧ Theta ≤ 1 ∧
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
        ∀ ell, 0 < ell → ell ≤ 1 → OriginalFinitePrefixBudget Data J allowed ell →
        ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
          OriginalIncrementOutput Data q C ell tau delta := by
  letI : CompactSpace M := original_data_source_compact_of_source_radius Data hd RSrc gS.norm_radius
  obtain ⟨V,domain,hV,hKV,hVU,hVC,hOpen,hCompact,hClosure,hSupport,hFinite⟩ :=
    original_local_given_finite_neighborhoods Data hd hs hLinear Parameter Spatial
      hParameter hSpatial transition
  have hVold : V ⊆ Data.parameterOpen := subset_closure.trans hVU
  have hDomain : ∀ nu, domain nu ⊆ Data.primaryDomain nu :=
    fun nu => subset_closure.trans ((hClosure nu).trans inter_subset_left)
  let L := localPrimaryData Data V domain
  let hdL := localPrimaryData_domain_conditions Data hd V domain hV hKV hOpen hSupport
  let hsL := localPrimaryData_smooth_inputs Data hs V domain hVold hDomain
  let hpL := localPrimaryData_phase_conditions Data hd hs hp V domain hVold hDomain hdL hsL
  let hnL := localPrimaryData_free_normal_conditions Data hd hs hn V domain hVold hDomain hdL hsL
  let hImmL := localPrimaryData_slice_immersion Data hImm V domain hVold
  let hLinearL := localPrimaryData_linear_smooth Data hLinear V domain hVold hDomain
  let hDecompL := localPrimaryData_decomposition Data hDecomp V domain hVold
  let hReserveL := localPrimaryData_reserve Data rho hReserve V domain hVold
  let hEllL := localPrimaryData_ellipticity Data c hEll V domain
  have hTransitionL : RepairOriginalTransitionBudgets L Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  obtain ⟨BS,BP,hBS,hBP,hRawPair⟩ := exists_uniform_originalBufferedRawPair
    (M := M) (P := P) (E := D) (F := Ep)
    RSrc bSrc RPar bPar gS.radius_pos gP.radius_pos TS TP Ds Dp
  obtain ⟨s,hChartS,hSupportS,hDegreeS,hSmoothS,hSampleS,hInnerS,
    AP,hChartP,hSampleP,rawS,rawP,hRawS,hRawP⟩ :=
    hRawPair Data.atlas Data.sourceNormDomain gS (Fin Data.parameterCount)
      Data.parameterChart Data.parameterNormDomain
      (fun i => WParam i ∩ (Data.parameterChart i).source) Data.parameterSet gP.inter_chart_source
      hd.atlas_smooth hd.parameter_charts_smooth hDs
      (fun i => (enlargedSupportDegree_mono _ WParam (fun _ => inter_subset_left) i).trans (hDp i))
      hSTrans (fun p i j hj y hy hi => hPTrans p i j hj y hy hi.1 hi.2)
  let BData := normBufferedData L bSrc gS.radius_pos gS.chart_buffer
  let hdB := normBufferedData_domain_conditions L bSrc gS.radius_pos gS.chart_buffer hdL
  let hsB := normBufferedData_smooth_inputs L bSrc gS.radius_pos gS.chart_buffer hsL
  let hpB := normBufferedData_phase_conditions L bSrc gS.radius_pos gS.chart_buffer hdL hsL hpL hdB hsB
  let hnB := normBufferedData_free_normal_conditions L bSrc gS.radius_pos gS.chart_buffer hdL hsL hnL hdB hsB
  let hImmB := normBufferedData_immersion L bSrc gS.radius_pos gS.chart_buffer hImmL
  let hLinearB := normBufferedData_linear_smooth L bSrc gS.radius_pos gS.chart_buffer hLinearL
  let hDecompB := normBufferedData_decomposition L bSrc gS.radius_pos gS.chart_buffer hDecompL
  let hReserveB := normBufferedData_reserve L bSrc gS.radius_pos gS.chart_buffer rho hReserveL
  let hEllB := normBufferedData_ellipticity L bSrc gS.radius_pos gS.chart_buffer c hEllL
  have hSampleB : ∀ i, bufferedSamplingCoordinates BData.atlas i ⊆ BData.sourceNormDomain i :=
    gS.original_sampling
  let Ref := refinedWorkingData BData RSrc bSrc gS.radius_pos le_rfl s
  let hdR := refinedWorkingData_domain_conditions BData RSrc bSrc gS.radius_pos le_rfl s hdB hSampleB
  let hsR := refinedWorkingData_smooth_inputs BData RSrc bSrc gS.radius_pos le_rfl s hsB
  let hpR := refinedWorkingData_phase_conditions BData RSrc bSrc gS.radius_pos le_rfl s hdB hsB hpB hdR hsR
  let hnR := refinedWorkingData_free_normal_conditions BData RSrc bSrc gS.radius_pos le_rfl s hdB hsB hnB hdR hsR
  let hImmR := refinedWorkingData_immersion BData RSrc bSrc gS.radius_pos le_rfl s hImmB
  let hLinearR := refinedWorkingData_linear_smooth BData RSrc bSrc gS.radius_pos le_rfl s hLinearB
  let hDecompR := refinedWorkingData_decomposition BData RSrc bSrc gS.radius_pos le_rfl s hDecompB
  let hReserveR := refinedWorkingData_reserve BData RSrc bSrc gS.radius_pos le_rfl s rho hReserveB
  let hEllR := refinedWorkingData_ellipticity BData RSrc bSrc gS.radius_pos le_rfl s c hEllB
  have hTransitionR : RepairOriginalTransitionBudgets Ref Parameter Spatial :=
    ⟨transition.parameter,transition.spatial⟩
  have hFiniteR : ∀ j, actualOriginalGivenInputProfile Ref j 1 ≠ ⊤ := fun j => hFinite j 1
  obtain ⟨cT,Mb,BInv,HGrid,hcT,hMb,hBInv,hHGrid,hOutput⟩ :=
    actual_sampled_common_raw_output Ref hdR hsR hpR hnR hImmR hLinearR hDecompR
      rho hReserveR c hEllR BS TS BP TP hBS hTS hBP hTP Ds Dp AP hChartP rawS rawP hSampleS hSampleP
      Parameter Spatial hParameter hSpatial hTransitionR (originalPrimaryInteractionDegree Data+1)
      (fun z hz => original_primary_localized_interaction_count Data V domain hVold z hz) hFiniteR
  refine ⟨BS,BP,cT,Mb,BInv,HGrid,hBS,hBP,hcT,hMb,hBInv,hHGrid,?_⟩
  intro q hq allowed hAllowed
  obtain ⟨hTheta,hThetaOne,C,hC,hOutputAt⟩ := hOutput q hq allowed hAllowed
  refine ⟨hTheta,hThetaOne,C,hC,?_⟩
  intro ell hell hellOne hGiven tau delta hdelta hdeltaTau htauEll hRatio
  have hGivenL := localPrimaryData_original_budget Data V domain hd.primary_open hOpen hDomain
    ((q+1)*(q+4)+2) allowed ell hGiven
  have hCurrent : OriginalFinitePrefixBudget Ref ((q+1)*(q+4)+2) allowed ell := hGivenL
  have hout : OriginalIncrementOutput Ref q C ell tau delta :=
    hOutputAt ell hell hellOne hCurrent tau delta hdelta hdeltaTau htauEll hRatio
  exact localPrimaryData_original_output Data V domain hVold q C ell tau delta hout

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_buffered_sampled_common_increment
