import UpgradeContinuation.GeneralCarrierAtlas
import NormalPolar.ActualProbeInitialSupplySignedSecondaryResponses
import NormalPolar.ActualProbeInitialSupplyCarrierSecondaryOriginal
import NormalPolar.PassiveOriginalData

/-! The actual signed seed factory, rather than a supplied completed atlas,
produces the vanishing secondary responses. The primary raw fields are the
ones already delivered by the q440 background. All secondary pieces, their
observations and their response costs are manufactured internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold Filter
open scoped ContDiff Topology Classical BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m d N r : ℕ} {M P Tr Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
local notation "Params" => Fin d → ℝ
private local instance generalProbeInitialSupplySignedSecondaryResponsesSignedRecordFintype {Label : Type*} [Fintype Label] [DecidableEq Label] :
    Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

abbrev generalProbeInitialSignedSecondaryStatement
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight) : Prop :=
    let Data := passiveOriginalData (0 : Z) seed B Q
    let A := seed.atlas
    let S := incrementsOriginalEvaluation A B.chart seed.sourceNormDomain Q univ
    let K : (Fin seed.primaryCount ⊕ Fin r) → Set M :=
      Sum.elim (fun l => tsupport (fun x => seed.cutoff l (0,x)))
        (fun l => tsupport ((waves l).cutoff : M → ℝ))
    let signedPhase := fun (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) x =>
      jointSecondarySignedPhase
        (Sum.elim (fun l (z : Ep × M) => seed.phase l (0,z.2))
          (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val (0,x)
    ∀ (O : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r) → Set M)
      (seeds : (rec : ActualSecondarySignedRecord (Fin seed.primaryCount ⊕ Fin r)) →
        JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (signedPhase rec)
          (K rec.val.1.1 ∩ K rec.val.1.2) (O rec)),
    ∀ (Rsub : ℕ) (reserve Bnd Mg Ku : ℝ)
      (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKu : 0 ≤ Ku)
      (Tb : ℕ → ℝ) (hTb : ∀ k, 0 ≤ Tb k),
    ∃ C : ℝ, 0 ≤ C ∧ (∀ t, 0 ≤ actualProbeSecondaryModulus C t) ∧
      Tendsto (actualProbeSecondaryModulus C) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
    let tau := t^((6:ℝ)/5)
    let ell := t^((11:ℝ)/10)
    let delta := t^(10:ℕ)
    let F := fun _ : P => scale • F0
    let hF := fun _ : P => contMDiff_const_rescale F0 hF0 scale
    ∀ (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin seed.primaryCount) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
      (gCutoff : ∀ l, g.cutoff l = fun z => seed.cutoff l (0,z.2))
      (gPhase : ∀ l, g.phase l = fun z => seed.phase l (0,z.2))
      (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (primary : Fin seed.primaryCount → Set (P × M)) (u : P → Params)
      (hu : ∀ i, ContDiffOn ℝ ∞ (fun z : X => u ((B.chart i).symm z.1)) (Prod.fst ⁻¹' (B.chart i).target))
      (huj : ∀ k, k ≤ 885 → ∀ (i : Fin B.count) (z : X), z.1 ∈ Q i →
        ell^k*‖iteratedFDeriv ℝ k (fun y : X => u ((B.chart i).symm y.1)) z‖ ≤ Ku)
      (raw : ∀ i : Fin A.count × Fin B.count,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) 1329 442 885 Rsub
          (Fintype.card (Fin seed.primaryCount ⊕ Fin r)) reserve Bnd Mg Tb
          (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
          (round3ParameterNativePrimary F g (B.chart i.2))
          (fun p => input ((B.chart i.2).symm p)) (fun p => input ((B.chart i.2).symm p))
          (round3ParameterNativeDomain (B.chart i.2) (univ : Set (P × M)))
          (fun l => round3ParameterNativeDomain (B.chart i.2) (primary l)) (A.chart i.1)
          (actualRawObserverOpen (A.chart i.1) (round3ParameterNativeDomain (B.chart i.2) (univ : Set (P × M))))
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) tau ell 0)
      (geometry : ∀ i : Fin A.count × Fin B.count, ActualOriginalPrimaryPhysicalGeometry
        (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
        (round3ParameterNativePrimary F g (B.chart i.2)))
      (label : (Fin r × Bool) ↪ Fin d),
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P → D → M :=
      fun l s _ => (family.piece l).seed.coordinate s 0
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P × D → ℝ :=
      fun l s z => (family.piece l).seed.cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s _ x => actualRescaledNormal F0 hF0 scale
        (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
        ((waves l).normal ((family.piece l).seed.coordinate s 0 x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count → OpenPartialHomeomorph (P × M) (P × D) :=
      fun l s => passiveParameterChart (0 : Z) ((family.piece l).seed.physicalChart s)
    let phase : Fin r → P × M → ℝ := fun l z => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s p x => (-(delta*tau)/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let source := actualProbeInitialGroupedSource F hF g label c vf phase tau delta
      442 442 a input u (jointSecondarySeedPaddedChoice seeds) (jointSecondarySeedPaddedChoice_preserves seeds)
    actualProbeInitialSecondaryBallBounds A seed.sourceNormDomain B C t
      (actualParameterSecondarySourceSum F hF source tau 442)

theorem generalProbeInitialSupply_signed_secondary_original_responses
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (hs : IncrementsOriginalSmoothInputs (passiveOriginalData (0 : Z) seed B Q))
    (hOmega : ∀ i, IsCompact (seed.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (hweight : ∀ l, 0 < weight l)
    (family : GeneralLegalWaveRawFamily F0 hF0 waves weight) :
    generalProbeInitialSignedSecondaryStatement (Tr := Tr) (Β := Β) seed B Q hd F0 hF0 waves weight family := by
  unfold generalProbeInitialSignedSecondaryStatement
  intro Data A S K signedPhase O seeds Rsub reserve Bnd Mg Ku hreserve hBnd hMg hKu Tb hTb
  obtain ⟨Cback,Tcost,Tpfirst,Tobs,Phfirst,hCback,hFirstT,hPhfirst,hAtlas⟩ :=
    generalProbeInitialSupply_signed_carrier_atlas_uniform (Tr := Tr) (Β := Β)
      Data hd hs rfl hQ hOmega F0 hF0 hImm waves weight hweight family
      (fun l x => seed.cutoff l (0,x)) (fun l x => seed.phase l (0,x))
      (fun _ => rfl) (fun _ => rfl) O seeds
  let Bfirst := Cback Bnd
  let Mgfirst := Mg+family.geometryBudget 1329+jointSecondarySeedGeometryBudget seeds 885
  let Tbfirst := fun k => Tb k+Tcost k*bufferedTransitionPrefix Tb k
  have hBfirst : 0 ≤ Bfirst := hCback _ hBnd
  have hMgfirst : 0 ≤ Mgfirst :=
    add_nonneg (add_nonneg hMg (family.positive 1329).1.le)
      (jointSecondarySeedGeometryBudget_positive seeds 885).le
  have hTbfirst k : 0 ≤ Tbfirst k := add_nonneg (hTb k)
    (mul_nonneg (hFirstT k).1 (zero_le_one.trans (one_le_bufferedTransitionPrefix hTb k)))
  let L := Fintype.card (Fin seed.primaryCount ⊕ Fin r)
  let RP := ∑ l, (family.piece l).seed.refinement.count
  let RS := Fintype.card (Σ rec, Fin (seeds rec).refinement.count)
  let KC := jointSecondarySeedCutoffBudget seeds 885
  obtain ⟨C,hC,heta,hlimit,hResponse⟩ := actualProbeInitialSupply_carrier_secondary_original_responses
    (M := M) (P := P) (Tr := ℝ) (m := m) (d := d) (N := N) (p := d)
    (Λ := Fin seed.primaryCount) (Β := Β) (Pieces := fun l => Fin (family.piece l).seed.refinement.count)
    (Sub := Σ rec, Fin (seeds rec).refinement.count)
    1329 885 440 442 440 442 Rsub L RP RS (by omega) (by omega) (by omega) (by omega) (by omega)
    reserve Bfirst Mgfirst KC (family.cutoffBudget 1329) (family.normalBudget 1329) Ku Phfirst
    hreserve hBfirst hMgfirst (jointSecondarySeedCutoffBudget_positive seeds 885).le
    (family.positive 1329).2.1.le (family.positive 1329).2.2.le hKu hPhfirst weight
    Tbfirst Tpfirst (fun _ => 1) Tobs hTbfirst (fun k => (hFirstT k).2.1)
    (fun _ => zero_le_one) (fun k => (hFirstT k).2.2)
  refine ⟨C,hC,heta,hlimit,?_⟩
  intro scale hscale t ht ht1 tau ell delta F hF g hg gCutoff gPhase input primary u hu huj raw geometry label
    c chi nu a phase vf source
  have hscales := probe_original_scale_conditions t ht ht1
  obtain ⟨atlas⟩ := hAtlas Bnd Mg hBnd hMg Tb hTb Ku scale hscale Rsub reserve tau ell delta
    hscales.1.le hscales.2.1 g gCutoff gPhase input primary u hu huj raw geometry
  have ha l s : Round3ParameterChartPreserves (a l s) := passiveParameterChart_preserves (0 : Z) _
  exact hResponse A hd.atlas_smooth B seed.sourceNormDomain Q hd.source_norm_subset hQT hSampling
    F hF g hg label c chi nu phase a ha input input u primary (fun l => (univ : Set P) ×ˢ K l)
    (fun l s => {z : P × M | (0,z.2) ∈ (family.piece l).seed.carrier s})
    (jointSecondarySeedPaddedChoice seeds) (jointSecondarySeedPaddedChoice_preserves seeds)
    t 0 ht ht1 atlas

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.generalProbeInitialSignedSecondaryStatement
#print axioms GlobalEmbedding.Continuation.generalProbeInitialSupply_signed_secondary_original_responses
