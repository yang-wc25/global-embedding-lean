import Repair.FullIncrementNovOpenCoherentFactory
import Repair.FullIncrementNovOpenCanonicalRaw
import Repair.FullIncrementNovOpenMeanCommonRaw
import Repair.FullIncrementNovOpenLegacyMeanSupply
import Repair.AuxBridgeNovLocalCoverIncrement
import Repair.AuxBridgeNovOpenGermTransport
import Probes.Round3ParameterSecondaryCommonRawAtlas
import Probes.ActualRawProfileBudgets
import Smoothing.Round3ParameterMeanLocalEstimates
import Smoothing.Round3ParameterMeanUniformThreshold
import Smoothing.ParameterOriginalCoreBounds

/-! Actual finite primary/mean/secondary construction on the unchanged original
Data. Arbitrary q >= 1, all allowed slow scales, one U for every derivative
order, and the original paper norms. Every raw field and every mean estimate
is produced here. The prepared geometry is produced by LocalizedFactories
and OpenPreparedMean. Its uniform reduction to the original numerical input
prefix remains a separate unresolved obligation; no such reduction is claimed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uB
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem fullIncrementNov_actual_finite_increment
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i))
    (H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) (incrementsOriginalParameterRegion Data))
    (hH : H.val = Data.H)
    (Β : Type uB) [Fintype Β] (primaryHost : Β → Fin Data.atlas.count)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (hPhase : ∀ nu, g.phase nu = Data.phase nu) (hCutoff : ∀ nu, g.cutoff nu = Data.cutoff nu)
    (V0 : Set P) (hV0 : IsOpen V0) (hKV0 : Data.parameterSet ⊆ V0)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z : P × M, z.1 ∈ V0 → ∑ i, theta i z = 1)
    (L : ℕ) (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (cT : ℝ) (hcT : 0 < cT) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k)
    (Rsub : ℕ)
    (prep : ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V0 ×ˢ (univ : Set M)) cT Tinv Forward Meta Rsub i)
    (q : ℕ) (hq : 1 ≤ q) (Packet : ℕ → ℝ) (hPacket0 : ∀ k, 0 ≤ Packet k)
    (ML : ℝ) (hML0 : 0 ≤ ML) :
    ∃ Theta : ℝ, 0 < Theta ∧ Theta ≤ 1 ∧
    ∃ Cmap Cmetric : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Cmetric j) ∧
    ∀ ell, 0 < ell → ell ≤ 1 →
    (incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤) →
    ((incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML) →
    (∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤) →
    (∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n) →
    ∀ epsilon, 0 < epsilon → epsilon < Theta → ∀ delta, 0 ≤ delta → delta ≤ epsilon*ell →
    ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
      Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧ G ⊆ incrementsOriginalParameterRegion Data ∧
      Round3ParameterJointIncrementConclusion Data.atlas Data.parameterChart
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) G Data.F U Data.H q delta (epsilon*ell) ell Cmap Cmetric := by
  let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
    Data.parameterNormDomain Data.parameterSet
  let W0 := incrementsOriginalParameterRegion Data
  let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
  have hradius : 0 < radius := div_pos hReserve.reserve_pos (by positivity)
  have hreserve : 0 < rho/4 := div_pos hReserve.reserve_pos (by norm_num)
  let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
    c cT (1+Forward (s+(q+4))) (Meta (s+(q+4))) R Tinv
  let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4)))
    c cT (1+Forward (s+(q+4))) Tinv
  let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
  let T := parameterRound2_identityRawTransition m d Packet Forward
  have hBnd (s R) : 0 ≤ Bnd s R := parameterRound2_identityRawBnd_nonneg _ _ _ _ _ _ _ _ _ _ (hPacket0 _) _
  have hMg (s) : 0 ≤ Mg s := parameterRound2_identityRawMg_nonneg _ _ _ _ _ _ _ _ _
  have hDinput (s) : 0 ≤ Dinput s := parameterRound2_identityRawDinput_nonneg _ _ _ _ (hPacket0 _) _
  have hT (k) : 0 ≤ T k := parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket0 hForward k
  let Csize := round3ParameterMeanSizeCost.{uM,0,uP,0,uB} (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    q Rsub Data.primaryCount hq (rho/4) hreserve Bnd Mg hBnd hMg T hT
  let Theta := parameterRound2_uniformMeanThreshold Packet Csize radius q (q+4)
  obtain ⟨hTheta,hTheta1,Cmean,hCmean,hMean⟩ :=
    round3Parameter_actual_global_mean_uniform_threshold (m := m) (d := d) (N := N) (M := M)
      Packet Csize (fun s R => Csize s R*Dinput s) radius hradius q
  let R := parameterRound2_uniformMeanProfile Packet Csize (q+4)
  let Sub := fun r => Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(secondary.s r i))
  letI : ∀ r, Fintype (Sub r) := fun r => inferInstance
  obtain ⟨Ti,To,Mrest,Cut,hTi,hTo,hMrest,hCut,hSecondary⟩ :=
    fullIncrementNov_original_open_coherent_factory Data hd hs hImm theta secondary hSupport
      V0 hPart L hCount hS q c Packet
  let Bsec := fun j => Bnd (j+q+4) (R q ((j+q+4)+(q+4)))
  let Msec := fun j => max (Mrest j) (Mg (j+q+4))
  have hBsec (j) : 0 ≤ Bsec j := hBnd _ _
  have hMsec (j) : 0 ≤ Msec j := (hMrest j).trans (le_max_left _ _)
  obtain ⟨Cmap,Cmetric,hCmap,hCmetric,hFinish⟩ :=
    auxBridgeNov_all_orders_with_final_domain_cover.{uM,0,uP,0,uB,0}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      radius hradius q Rsub Data.primaryCount (L*5^Module.finrank ℝ (Ep × D)) hq (rho/4) hreserve
      Cmean hCmean Theta hTheta1 Bsec Msec Cut (fun _ => T) (fun _ => Ti) (fun _ => To)
      hBsec hMsec hCut (fun _ => hT) (fun _ => hTi) (fun _ => hTo)
  refine ⟨Theta,hTheta,hTheta1,Cmap,Cmetric,hCmap,hCmetric,?_⟩
  intro ell hell hell1 hProfile hML hGiven hPacket epsilon he heTheta delta hdelta hdt
  let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
    (fun _ _ hy => hy.1) ell
  let F := fullIncrementNovOriginalSourceSlice Data
  let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
  let gOpen := fullIncrementNovOriginalOpenFamily Data g hTarget
  have hgOpen : ∀ nu beta, Round3ParameterChartPreserves (gOpen.chart nu beta) := hPreserves
  have hCoreFinite (n) : incrementsOriginalCoreInputProfile Data n ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hGiven n) (actualOriginalGivenInputProfile_core_le Data n ell)
  have hCoreBudget (n) : (incrementsOriginalCoreInputProfile Data n ell).toReal ≤ Packet n :=
    (ENNReal.toReal_mono (hGiven n) (actualOriginalGivenInputProfile_core_le Data n ell)).trans (hPacket n)
  have hHbudget (s) : p s H ≤ Packet s := by
    change (paperAtlasWeighted 0 s ell
      (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart H.val)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S).toReal ≤ _
    rw [hH]
    exact (ENNReal.toReal_mono (hCoreFinite s) (parameterOriginalCore_tensor_le Data s ell)).trans (hCoreBudget s)
  have supply := (fullIncrementNov_original_open_legacy_mean_supply Data hd hs hn hp g hTarget V0 hV0 hKV0 hImm
    ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
    q Rsub Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep).2 H hH
  obtain ⟨hsm,hsize,hdiff⟩ := round3Parameter_actual_raw_mean_local_estimates
    Data.atlas Data.parameterChart hd.atlas_smooth S W0 hS (fun _ _ hy => hy.1)
    ell hell hell1 H radius q Rsub Data.primaryCount hq (rho/4) hreserve
    Bnd Mg Dinput hBnd hMg hDinput T hT F hF gOpen hgOpen Data.primaryDomain supply
  have hmean := hMean P Data.atlas Data.parameterChart S W0 hS (fun _ _ hy => hy.1)
    ell hell H hHbudget F hF gOpen hsm hsize hdiff
  let Top := round3ParameterMeanReserveOperator Data.atlas Data.parameterChart S W0 p H radius ell F hF gOpen q hsm
  let Kq := (meanReserveStep (p 0) H radius (Top epsilon))^[q] H
  have hIter := parameterRound2_uniform_mean_reserve_profile Packet Csize radius hradius q (q+4)
    p H hHbudget Top hsize epsilon he heTheta
  have hKq : p 0 (Kq-H) < radius := (hIter.1 q le_rfl).trans_lt (by linarith)
  have hKqR (s) : p s Kq ≤ R q s := hIter.2 q le_rfl s
  obtain ⟨G,hG,hGR,hKG,hGV,coverG,hRaw⟩ :=
    (fullIncrementNov_original_open_mean_common_raw_supply Data hd hs hn hp g V0 hV0 hKV0 hImm
      ell c cT hell hell1 hEll hcT hLinear hDecomp rho hReserve hS ML hProfile hML
      q Rsub Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket prep).2 H hH ⟨Kq,hKq⟩ ⟨Kq,hKq⟩
  let gG := round3Parameter_restrictPrimaryFamily F gOpen G hG
  have hPhysical (i) := fullIncrementNov_open_prepared_physical_geometry Data hd hs hn hImm g hTarget
    V0 cT hcT Tinv Forward Meta Rsub i (prep i) G hG
  obtain ⟨choice,hChoice,family,hFamily⟩ := hSecondary Msec (fun j => le_max_left _ _) G hG hGR
    (fun z hz => (hGV hz).1) ell hell hell1 hEll hCoreFinite hCoreBudget Β primaryHost gG hPhase hCutoff hPhysical
  have hTau : 0 < epsilon*ell := mul_pos he hell
  have hTaul : epsilon*ell ≤ ell := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (heTheta.le.trans hTheta1) hell.le
  have hFinalRaw (j : ℕ) : Nonempty (Round3ParameterRawAtlasData (Tr := ℝ) Data.atlas Data.parameterChart
      F hF gG Kq.val Kq.val (j+2*q+8) (j+q+4) j q Rsub Data.primaryCount
      (L*5^Module.finrank ℝ (Ep × D)) (rho/4) (Bsec j) (Msec j) (Cut j)
      T Ti To G Data.primaryDomain S ell delta (epsilon*ell) 0 choice) := by
    let s := j+q+4
    obtain ⟨raw,hO⟩ := fullIncrementNov_open_canonical_raw_physical_atlas Data hd hs hn g hTarget
      V0 cT Tinv Forward Meta Rsub prep G hG Kq.val Kq.val (s+(q+4)) q s (rho/4)
      (Bnd s (R q (s+(q+4)))) (Mg s) T (epsilon*ell) ell (Dinput s*p (s+(q+4)) (Kq-Kq))
      (hRaw (epsilon*ell) hTau hTaul s (R q (s+(q+4))) (hKqR _) (hKqR _))
    have hRaw0 (i) := raw.raw i
    have hEnlarged (i) := actual_raw_profiles_enlarge_budgets (s+(q+4)) (q+2) s Rsub Data.primaryCount
      (rho/4) (Bnd s (R q (s+(q+4)))) (Mg s) (Bsec j) (Msec j) T le_rfl (le_max_right _ _)
      _ _ _ _ _ _ _ _ _ _ _ _ _ (hRaw0 i)
    have hOrder : s+(q+4) = j+2*q+8 := by dsimp [s]; omega
    have hSolve : actualSecondarySolveOrder q j = s := rfl
    have result := round3Parameter_secondary_common_raw_atlas Data hd F hF gG q ell G
      Msec Cut Ti To (L*5^Module.finrank ℝ (Ep × D)) S choice family hFamily
      Kq.val Kq.val (s+(q+4)) j Rsub Data.primaryCount (rho/4) (Bsec j) T Data.primaryDomain
      delta (epsilon*ell) 0 (by
        intro i
        have hi := hEnlarged i
        rw [congrFun hO i] at hi
        simpa only [hSolve,sub_self,map_zero,mul_zero] using hi)
    simpa only [hOrder,hSolve] using result
  have hSG (i) : MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) (S i) G :=
    fun y hy => hKG ⟨hy.2.2.2,mem_univ _⟩
  have hFinish0 := hFinish P (Fin Data.primaryCount) Β (Sigma Sub) Data.parameterCount Data.atlas
    Data.parameterChart hd.atlas_smooth hd.parameter_charts_smooth S W0 (hd.parameter_open.prod isOpen_univ)
    hS (fun _ _ hy => hy.1) p ell hell hell1 H F hF gOpen hgOpen Data.primaryDomain
    hsm hmean epsilon he heTheta delta hdelta hdt G hG hGR hSG coverG choice hChoice hFinalRaw
  let U := round3ParameterIncrementMap F hF gG Kq.val (q+2) (epsilon*ell) delta choice
  refine ⟨G,U,hG,hKG,hGR,?_⟩
  have hInternal := hFinish0.2
  rw [hH] at hInternal
  exact auxBridgeNov_open_joint_increment_conclusion Data hd U G hGR q delta (epsilon*ell) ell Cmap Cmetric hInternal

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_actual_finite_increment
