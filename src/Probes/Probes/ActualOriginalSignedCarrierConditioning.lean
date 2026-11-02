import Probes.ActualOriginalCarrierConditionedHost
import Probes.ActualOriginalSignedPhaseGood
import Probes.ActualIncrementOriginalSignedPhaseJets

/-! Original signed secondary phases produce their own conditioned host charts.
Good is read only on the actual joint support intersection. No chosen numerical
margin or independent Good hypothesis is supplied. The same host functions,
phase, and cutoff survive the restriction, before every later derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem actual_original_signed_carrier_conditioned_chart
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M Es)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (actualOriginalParameterSignedPhase Data i r.val) e)
    (carrier : Set (Ep × M)) (hCompact : IsCompact carrier)
    (hSupport : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hactive : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data)
    (hpair : ∀ w ∈ carrier, ((Data.parameterChart i.2).symm w.1,w.2) ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2) :
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let phase := actualOriginalParameterSignedPhase Data i r.val
    ∃ (cF cT : ℝ) (b' : OpenPartialHomeomorph X X)
        (e' : Ep → OpenPartialHomeomorph M Es),
      0 < cF ∧ 0 < cT ∧ b'.source ⊆ b.source ∧ b'.target ⊆ b.target ∧
      (b' : X → X) = b ∧ (b'.symm : X → X) = b.symm ∧
      ActualOriginalHostSliceData (Data.atlas.chart i.1) b' phase e' ∧
      carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b').source ∧
      (actualHostAdaptedChart (Data.atlas.chart i.1) b').source ⊆
        (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ∧
      (∀ p, ((e' p).symm : Es → M) = (e p).symm) ∧
      (∀ z ∈ b'.target, ∀ v : Es,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e' z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ b'.target, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e' z.1).symm z.2 v‖^2 := by
  intro F hF phase
  let W := (actualHostAdaptedChart (Data.atlas.chart i.1) b).source
  have hParam (z : Ep × M) (hz : z ∈ W) :
      z.1 ∈ (Data.parameterChart i.2).target := by
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    have hn := hsource hz.2
    have heq := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply (q z))
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d (q z)) = z.1 at heq
    have ht := hn.1.2
    change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d (q z)) ∈
      (Data.parameterChart i.2).target at ht
    rwa [heq] at ht
  have hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W := by
    have hh := actual_original_parameter_pullback_smooth Data hd i.2 Data.F
      (incrementsOriginalParameterRegion Data) hs.F_joint W hParam
      (fun z hz => (hactive z hz).1.2)
    apply hh.congr
    intro z hz
    change actualOriginalOpenParameterSlice Data i z.1 z.2 = _
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (hactive z hz).1.2.1]
    rfl
  have hNu : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : Ep × M => Data.phase r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2)) W :=
    actual_original_parameter_pullback_smooth Data hd i.2 (Data.phase r.val.1.1)
      (Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data) (hs.phase_joint r.val.1.1)
      W hParam (fun z hz => (hactive z hz).1)
  have hMu : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (fun z : Ep × M => Data.phase r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2)) W :=
    actual_original_parameter_pullback_smooth Data hd i.2 (Data.phase r.val.1.2)
      (Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data) (hs.phase_joint r.val.1.2)
      W hParam (fun z hz => (hactive z hz).2)
  have hAll (q : Fin 4) : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (actualOriginalParameterSignedPhase Data i (r.val.1,q)) W := by
    change ContMDiffOn _ _ _ (fun z : Ep × M =>
      ![Data.phase r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2) +
          Data.phase r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2),
        Data.phase r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2) -
          Data.phase r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2),
        -Data.phase r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2) +
          Data.phase r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2),
        -Data.phase r.val.1.1 ((Data.parameterChart i.2).symm z.1,z.2) -
          Data.phase r.val.1.2 ((Data.parameterChart i.2).symm z.1,z.2)] q) W
    fin_cases q
    · exact hNu.add hMu
    · exact hNu.sub hMu
    · exact hNu.neg.add hMu
    · exact hNu.neg.sub hMu
  have hInj (z : Ep × M) (hz : z ∈ W) :
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) z.2) := by
    change Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (actualOriginalOpenParameterSlice Data i z.1) z.2)
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (hactive z hz).1.2.1]
    exact hImm.immersion _ (hactive z hz).1.2.1 z.2
  have hGood (z : Ep × M) (hz : z ∈ carrier) :
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (phase z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => phase (z.1,x)) z.2)) := by
    exact actual_original_parameter_signed_secondary_phase_good Data hd hs hp i r z (hpair z hz)
  exact actual_original_compact_carrier_conditioned_host F hF (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) b phase e hdata W
    (actualHostAdaptedChart (Data.atlas.chart i.1) b).open_source hFjoint (hAll r.val.2)
    (fun _ hz => hz) carrier hCompact hSupport hInj hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_signed_carrier_conditioned_chart
