import Probes.ActualUniformPreparedPairStatementAllIndex
import Probes.ActualUniformRestrictedPairStepAllIndex
import Probes.ActualSecondaryPreparedRawObservations
import Probes.ActualUniformRestrictedScaledStepAllIndex
import Probes.ActualOriginalIncrementRawBaseTwoAllIndex
import Probes.ActualRepairPairRecurrenceAlgebra

/-! Actual full map/tensor pair recurrence (6.8) for the same finite update.
The base-two displacement bound is produced at one additional observed
order of the SAME map. Every extra reference quantity is a finite norm,
not an increased target entrance assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal Classical BigOperators
namespace GlobalEmbedding.Continuation
universe uM uTr uLabel uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

local instance actualUniformPreparedPairStepRepairChartedSpaceAllIndex : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformPreparedPairStepRepairIsManifoldAllIndex : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

theorem actual_original_uniform_prepared_pair_repair_step_all_index
    (B0 : ℕ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (reserve : ℝ) (hc : 0 < reserve)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Msecondary Kcut : ℕ → ℝ)
    (hBmean : ∀ s R, 0 ≤ Bmean s R) (hMmean : ∀ s, 0 ≤ Mmean s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (hMsecondary : ∀ s, 0 ≤ Msecondary s) (hKcut : ∀ s, 0 ≤ Kcut s)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) :
    ActualUniformPreparedPairRepairStatementAllIndex (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
     
      B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Msecondary Kcut
      hBmean hMmean hDinput hMsecondary hKcut T Tinv Tobs TP hT hTinv hTobs hTP
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius := by
  unfold ActualUniformPreparedPairRepairStatementAllIndex
  intro Csize Rq Brest Mrest
  have hBrest (j) : 0 ≤ Brest j := hBmean _ _
  have hMrest (j) : 0 ≤ Mrest j := (hMmean _).trans (le_max_left _ _)
  have hpair := actual_original_uniform_restricted_pair_repair_step_all_index
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
   
    B0 rho hrho q Rsub Lprimary Rsecondary hq reserve hc Bmean Mmean Dinput Brest Mrest Kcut
    hBmean hMmean hDinput hBrest hMrest hKcut T Tinv Tobs TP hT hTinv hTobs hTP
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius
  unfold ActualUniformRestrictedPairRepairStatementAllIndex at hpair
  obtain ⟨C,hC,epsilon0,he0,he01,hpair⟩ := hpair
  let threshold := parameterRound2_uniformMeanThreshold B0 Csize rho q (q+4)
  have hthreshold := parameterRound2_uniformMeanThreshold_pos B0 Csize rho hrho q (q+4)
  refine ⟨C,hC,min epsilon0 threshold,lt_min he0 hthreshold.1,
    (min_le_left _ _).trans he01,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ c A B hA hB S W Vprep hVprep hS hSO ell hell hell1 H p hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
    t helt ht1 G hG hstar h0 hstarReg h0Reg delta deltaNext hd hn Hold budget hbudget
    mu kernel chi SF SH htarget F hF g primary hStrong
  have hCanonical := parameterRound2_prepared_canonical_supply_to_canonical_supply
    A B.chart S W Vprep p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hStrong
  have hFixed := parameterRound2_canonical_neighborhood_supply_to_fixed_supply
    A B.chart S W p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hCanonical
  have hSupply := parameterRound2_fixed_neighborhood_supply_to_germ_supply
    A B.chart S W p H rho q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g primary ell hFixed
  obtain ⟨hsm,hfinite⟩ := hpair Label SubPrimary SubSecondary c A B hA hB S W hS hSO ell hell hell1 H hH hParam
    parameterSet RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget hsource hparameter hSinner
    t helt ht1 G hG hstar h0 hstarReg h0Reg delta deltaNext hd hn budget hbudget htarget
    F hF g primary hSupply
  refine ⟨hsm,?_⟩
  intro epsilon he heFinal hdeltatau Top K
  have heThreshold : epsilon < threshold := heFinal.trans_le (min_le_right _ _)
  have hprof := parameterRound2_actual_final_prepared_raw_profiles_index
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
    A B.chart hA hB S W Vprep hS hSO ell hell hell1 H rho hrho B0 q Rsub Lprimary hq reserve hc
    Bmean Mmean Dinput hBmean hMmean hDinput T TP hT hTP hParam F hF g primary
    hStrong hsm hH epsilon he heThreshold
  obtain ⟨hreserve,hKprofile,Gdomain,hGdomain,hGW,hGPrep,hSG,hObs,hraw⟩ := hprof
  refine ⟨hreserve,Gdomain,hGdomain,hGW,hGPrep,hSG,?_⟩
  intro gG NativeSamples hBackground choice choiceG U j
    geom hCoordinate hChart hPhase hHost hHostInv hHostSource hSupport hPair hPartition hCut hInv hCutJets hInvJets
    hostIndex hHostIndex hNativeSamples primaryGeometry hOriginal hChartInv hObserverNativeSamples hObserverJets hObserverCount
    geomHigher hCoordinateHigher hChartHigher hPhaseHigher hHostHigher hHostInvHigher hHostSourceHigher hSupportHigher
    hPairHigher hPartitionHigher hCutHigher hInvHigher hCutJetsHigher hInvJetsHigher hostIndexHigher hHostIndexHigher
    hNativeSamplesHigher primaryGeometryHigher hOriginalHigher hChartInvHigher hObserverNativeSamplesHigher hObserverJetsHigher
    hObserverCountHigher Hnext O nextPair
  have hrawFinal (r : ℕ) : Nonempty (∀ i : Fin A.count × Fin c,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (actualSecondaryInputOrder q r) (q+2)
        (actualSecondarySolveOrder q r) Rsub Lprimary reserve (Brest r) (Mrest r) T F hF gG
        (K q).val (K q).val Gdomain primary (A.chart i.1) (actualRawObserverOpen (A.chart i.1) Gdomain)
        (NativeSamples i) (epsilon*ell) ell 0) := by
    let s := actualSecondarySolveOrder q r
    have hnorder : s+(q+4) = actualSecondaryInputOrder q r := by
      dsimp only [s,actualSecondarySolveOrder,actualSecondaryInputOrder]
      omega
    obtain ⟨data⟩ := hraw s
    refine ⟨fun i => ?_⟩
    have hi := actual_raw_profiles_enlarge_budgets
      (s+(q+4)) (q+2) s Rsub Lprimary reserve
      (Bmean s (Rq (s+(q+4)))) (Mmean s) (Brest r) (Mrest r) T
      (by simp only [hnorder,Brest,s]; exact le_rfl)
      (show Mmean s ≤ Mrest r from le_max_left _ _)
      F hF gG (K q).val (K q).val Gdomain primary (A.chart i.1)
      (actualRawObserverOpen (A.chart i.1) Gdomain) (NativeSamples i)
      (epsilon*ell) ell 0 (data i)
    simpa only [hnorder,s] using hi
  obtain ⟨finalRaw⟩ := hrawFinal j
  let raw := actual_secondary_raw_data_from_canonical_prepared
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary
    reserve (Brest j) (Mrest j) (Kcut j) T Tinv F hF gG (K q).val (K q).val
    Vprep Gdomain hVprep hGdomain hGPrep primary ell delta (epsilon*ell) 0 choice geom
    hCoordinate hChart hPhase hHost hHostInv hHostSource hSupport hPair hPartition hCut hInv hCutJets hInvJets
    (fun i : Fin A.count × Fin c => A.chart i.1) NativeSamples finalRaw
    hostIndex hHostIndex hNativeSamples primaryGeometry
  have hobs := actual_secondary_prepared_raw_observations
    (actualSecondaryInputOrder q j) (actualSecondarySolveOrder q j) j q Rsub Lprimary Rsecondary
    (by dsimp only [actualSecondarySolveOrder]; omega)
    reserve (Brest j) (Mrest j) (Kcut j) T Tinv Tobs F hF gG (K q).val (K q).val
    Vprep Gdomain hVprep hGdomain hGPrep primary ell delta (epsilon*ell) 0 choice geom
    hCoordinate hChart hPhase hHost hHostInv hHostSource hSupport hPair hPartition hCut hInv hCutJets hInvJets
    (fun i : Fin A.count × Fin c => A.chart i.1) NativeSamples finalRaw
    hostIndex hHostIndex hNativeSamples primaryGeometry
    (fun i => contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i.1))
    (fun i => contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i.1))
    hOriginal hChartInv hObserverNativeSamples hObserverJets hObserverCount
  obtain ⟨obs⟩ := hobs
  obtain ⟨finalRawHigher⟩ := hrawFinal (j+1)
  let rawHigher := actual_secondary_raw_data_from_canonical_prepared
    (actualSecondaryInputOrder q (j+1)) (actualSecondarySolveOrder q (j+1)) (j+1) q Rsub Lprimary
    reserve (Brest (j+1)) (Mrest (j+1)) (Kcut (j+1)) T Tinv F hF gG (K q).val (K q).val
    Vprep Gdomain hVprep hGdomain hGPrep primary ell delta (epsilon*ell) 0 choice geomHigher
    hCoordinateHigher hChartHigher hPhaseHigher hHostHigher hHostInvHigher hHostSourceHigher hSupportHigher hPairHigher hPartitionHigher hCutHigher hInvHigher hCutJetsHigher hInvJetsHigher
    (fun i : Fin A.count × Fin c => A.chart i.1) NativeSamples finalRawHigher
    hostIndexHigher hHostIndexHigher hNativeSamplesHigher primaryGeometryHigher
  have hobsHigher := actual_secondary_prepared_raw_observations
    (actualSecondaryInputOrder q (j+1)) (actualSecondarySolveOrder q (j+1)) (j+1) q Rsub Lprimary Rsecondary
    (by dsimp only [actualSecondarySolveOrder]; omega)
    reserve (Brest (j+1)) (Mrest (j+1)) (Kcut (j+1)) T Tinv Tobs F hF gG (K q).val (K q).val
    Vprep Gdomain hVprep hGdomain hGPrep primary ell delta (epsilon*ell) 0 choice geomHigher
    hCoordinateHigher hChartHigher hPhaseHigher hHostHigher hHostInvHigher hHostSourceHigher hSupportHigher hPairHigher hPartitionHigher hCutHigher hInvHigher hCutJetsHigher hInvJetsHigher
    (fun i : Fin A.count × Fin c => A.chart i.1) NativeSamples finalRawHigher
    hostIndexHigher hHostIndexHigher hNativeSamplesHigher primaryGeometryHigher
    (fun i => contMDiffOn_of_mem_maximalAtlas (hA.chart_mem i.1))
    (fun i => contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i.1))
    hOriginalHigher hChartInvHigher hObserverNativeSamplesHigher hObserverJetsHigher hObserverCountHigher
  obtain ⟨obsHigher⟩ := hobsHigher
  exact (hfinite epsilon he (heFinal.trans_le (min_le_left _ _)) hdeltatau).2
    Gdomain hGdomain hGW hSG hBackground choiceG j (K q).val 0 raw
    (fun i => actualRawObserverOpen (A.chart i.1) Gdomain) obs
    (K q).val 0 rawHigher (fun i => actualRawObserverOpen (A.chart i.1) Gdomain) obsHigher

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_uniform_prepared_pair_repair_step_all_index
