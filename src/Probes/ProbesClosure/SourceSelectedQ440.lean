import NormalPolar.ActualProbeInitialSupplySignedCarrierAtlas
import NormalPolar.ActualProbeInitialSupplySignedSecondaryResponses
import NormalPolar.ActualProbeInitialSupplyCarrierQ440Complete
import NormalPolar.PassiveOriginalData
import NormalPolar.PassiveWaveSeedRescaledFamilyProfiles

/-!
# The original source-profile witness retained by the same q440 construction

This strengthens the frozen signed q440 orchestration by retaining the actual
`family.exists_uniform_parameter_raw_profiles` witness alongside its existing
increment, error and secondary outputs. The same Tp/Pphase fixes the amplitude
and the same global parameter. A subsequent sharp-background consumer can now
use this witness without a second existential choice or any smaller ball.

The analytic producers and all original map/error/secondary arguments below
are the existing verified components. This file repeats only their necessary
opaque-existential orchestration, with one extra returned primitive witness;
it does not reprove their analytic estimates or claim the original probes goal.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical BigOperators
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
universe uM uP uTr uΒ
variable {m d N r : ℕ} {M : Type uM} {P : Type uP} {Tr : Type uTr} {Β : Type uΒ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
private local instance probesSelectedSourceQ440SignedRecordFintype {Label : Type*} [Fintype Label] [DecidableEq Label] : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

private theorem probes_selected_q440_scalar_mean_factor
    (value epsilon ell delta cost : ℝ) (hell : ell ≠ 0) (he : 0 ≤ epsilon)
    (hvalue : value ≤ delta^2*(epsilon^441*cost)) :
    value ≤ delta^2*((epsilon*ell/ell)^(440+1)*max cost 0) := by
  rw [mul_div_cancel_right₀ _ hell]
  exact hvalue.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg he _)) (sq_nonneg delta))

/-- Complete primitive original profiles at fixed transition and phase costs.
This is the exact body of the existing uniform raw-profile producer. -/
abbrev ProbesSelectedOriginalProfiles
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (waves : Fin r → LocalLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (family : OriginalWaveSeedRescaledFamily F0 hF0 waves weight)
    (A : BufferedAtlas M D) (B : BufferedAtlas P Ep)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+d) → ℝ))
    (Tp Pphase : ℕ → ℝ) : Prop :=
  ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
  ∀ idx : Fin A.count × Fin B.count,
  Nonempty (JointGroupedPrescribedParameterChartRawData
    (fun _ : P => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
    (fun l s _ => (family.outer l s).spatialChart.symm)
    (fun l s (z : P × D) => (family.refinement l).cutoffCoordinates s (0,z.2))
    (fun l s _ x => actualRescaledNormal F0 hF0 scale (originalWave_contraction_ne_zero scale hscale)
      ((family.outer l s).spatialChart.symm x)
      ((waves l).normal ((family.outer l s).spatialChart.symm x)))
    (fun l (z : P × M) => weight l*(waves l).phase z.2)
    (fun l s => passiveParameterChart (0 : Z) (family.inner l s).chart)
    (B.chart idx.2) (A.chart idx.1) ((B.chart idx.2).target ×ˢ (A.chart idx.1).target)
    ((parameterTensorModelEquiv (m+1) d) ⁻¹' Samples idx)
    n j ell (family.geometryBudget (max n (j+1))) (family.cutoffBudget n)
    (family.normalBudget n) (Pphase (j+1)) Tp)

abbrev probesSelectedSourceQ440SecondaryStatement
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (hs : IncrementsOriginalSmoothInputs (passiveOriginalData (0 : Z) seed B Q))
    (hOmega : ∀ i, IsCompact (seed.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (waves : Fin r → LocalLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (hweight : ∀ l, 0 < weight l)
    (family : OriginalWaveSeedRescaledFamily F0 hF0 waves weight)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (rho : ℝ) (hrho : 0 < rho) : Prop :=
    let Data := passiveOriginalData (0 : Z) seed B Q
    let A := seed.atlas
    let S := incrementsOriginalEvaluation A B.chart seed.sourceNormDomain Q univ
    let hS := parameterRound2_originalEvaluation_univ_compact A B.chart seed.sourceNormDomain Q
      hOmega hQ hd.source_norm_subset hQT
    let hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
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
    ∃ Tp Pphase : ℕ → ℝ, (∀ k, 0 < Tp k ∧ 0 < Pphase k) ∧
    ProbesSelectedOriginalProfiles F0 hF0 waves weight family A B S Tp Pphase ∧
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.refinement l).count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∃ Ku : ℕ → ℝ, (∀ j, 0 ≤ Ku j) ∧ Ku 0 = amplitude ∧
    let ProbeB := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
      jointGroupedPrescribedMeanUniformCost (fun l => Fin (family.refinement l).count)
        m N d (j+444) 442 j Tp weight (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
    ∀ (HBound : ℕ → ℝ) (Rsub : ℕ) (reserve : ℝ) (hc : 0 < reserve)
      (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
      (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
      (Tb : ℕ → ℝ) (hTb : ∀ k, 0 ≤ Tb k),
    let L := Fintype.card (Fin seed.primaryCount ⊕ Fin r)
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,0,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      440 Rsub L (by omega) reserve hc Bnd Mg hBnd hMg Tb hTb
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C 440 444
    ∃ CU CE CS : ℝ, 0 ≤ CU ∧ 0 ≤ CE ∧ 0 ≤ CS ∧
      (∀ t, 0 ≤ actualProbeSecondaryModulus CS t) ∧
      Filter.Tendsto (actualProbeSecondaryModulus CS) (𝓝[>] 0) (𝓝 0) ∧ 0 < cap ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart S univ),
    (∀ s, parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell s H ≤ HBound s) →
    let F := fun _ : P => scale • F0
    let hF := fun _ : P => contMDiff_const_rescale F0 hF0 scale
    ∀ (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Fin seed.primaryCount) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
      (gCutoff : ∀ l, g.cutoff l = fun z => seed.cutoff l (0,z.2))
      (gPhase : ∀ l, g.phase l = fun z => seed.phase l (0,z.2))
      (primary : Fin seed.primaryCount → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B.chart S univ
      (parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell) H rho
      440 Rsub L reserve Bnd Mg Dinput Tb F hF g primary ell →
    (∀ i : Fin A.count × Fin B.count, ActualOriginalPrimaryPhysicalGeometry
      (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
      (round3ParameterNativePrimary F g (B.chart i.2))) →
    ∀ (label : (Fin r × Bool) ↪ Fin d) (epsilon : ℝ), 0 < epsilon → epsilon < cap →
    ∀ (delta : ℝ), 0 < delta → delta ≤ epsilon*ell →
    let c : (l : Fin r) → Fin (family.refinement l).count → P → D → M := fun l s (_ : P) => (family.outer l s).spatialChart.symm
    let chi : (l : Fin r) → Fin (family.refinement l).count → P × D → ℝ := fun l s (z : P × D) => (family.refinement l).cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.refinement l).count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s (_ : P) x => actualRescaledNormal F0 hF0 scale
      (originalWave_contraction_ne_zero scale hscale) ((family.outer l s).spatialChart.symm x)
      ((waves l).normal ((family.outer l s).spatialChart.symm x))
    let a : (l : Fin r) → Fin (family.refinement l).count → OpenPartialHomeomorph (P × M) (P × D) := fun l s => passiveParameterChart (P := P) (0 : Z) (family.inner l s).chart
    let phase : Fin r → P × M → ℝ := fun l (z : P × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.refinement l).count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s p x => (-(delta*(epsilon*ell))/(weight l)^2) • (chi l s (p,x) • nu l s p x)
    let meanProbe : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) := fun p x => jointGroupedParameterPrescribedMean (I := IM) label F hF c vf phase
      (epsilon*ell) 442 a (u p) p x
    let background : ℕ → (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) := fun i => actualParameterBackgroundMeanIterate F hF g 442
      (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0
    let U : P × M → V := actualProbeInitialGroupedIncrement F hF g label c vf phase (epsilon*ell) delta
      442 442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
      (jointSecondarySeedPaddedChoice_preserves seeds)
    let coordinates := incrementsOriginalMapCoordinates A B.chart U
    ((∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B.chart i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 440 (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 440 (epsilon*ell) coordinates (incrementsOriginalDifferentiation A B.chart) S).toReal ≤
        CU*delta/(epsilon*ell)) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B.chart) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B.chart) S).toReal ≤ CU*delta/(epsilon*ell)) ∧
    ∃ error : parameterRound2_originalTensorGermSpace A B.chart S univ,
      error.val = incrementsOriginalMetricError (fun z => F z.1 z.2) U H.val delta ∧
      parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO (epsilon*ell) 440 error ≤
        CE*(delta*((epsilon*ell)/ell)^440+delta^3/(epsilon*ell))) ∧
    ∀ (t : ℝ), 0 < t → t ≤ 1 → epsilon*ell = t^((6:ℝ)/5) →
      ell = t^((11:ℝ)/10) → delta = t^(10:ℕ) →
      actualProbeInitialSecondaryBallBounds A seed.sourceNormDomain B CS t
        (actualParameterSecondarySourceSum F hF
          (actualProbeInitialGroupedSource F hF g label c vf phase (epsilon*ell) delta
            442 442 a (background 441) u (jointSecondarySeedPaddedChoice seeds)
            (jointSecondarySeedPaddedChoice_preserves seeds)) (epsilon*ell) 442)

set_option backward.isDefEq.respectTransparency false in
theorem probes_selected_source_q440_with_secondary
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (hs : IncrementsOriginalSmoothInputs (passiveOriginalData (0 : Z) seed B Q))
    (hOmega : ∀ i, IsCompact (seed.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (waves : Fin r → LocalLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (hweight : ∀ l, 0 < weight l)
    (family : OriginalWaveSeedRescaledFamily F0 hF0 waves weight)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (rho : ℝ) (hrho : 0 < rho) :
    probesSelectedSourceQ440SecondaryStatement (Tr := Tr) (Β := Β) seed B hB Q hQ hQT hSampling hd hs hOmega
      F0 hF0 hImm waves weight hweight family b p₀ hp₀ rho hrho := by
  unfold probesSelectedSourceQ440SecondaryStatement
  intro Data A S hS hSO K signedPhase O seeds
  have hNative i : (parameterTensorModelEquiv (m+1) d) ⁻¹' S i = Q i.2 ×ˢ seed.sourceNormDomain i.1 :=
    passiveOriginal_native_norm_sample Data hd rfl i
  have hSQ i z (hz : parameterTensorModelEquiv (m+1) d z ∈ S i) : z.1 ∈ Q i.2 := by
    have hh : z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i := hz
    rw [hNative i] at hh
    exact hh.1
  have hSR i z (hz : parameterTensorModelEquiv (m+1) d z ∈ S i) : z.2 ∈ seed.sourceNormDomain i.1 := by
    have hh : z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i := hz
    rw [hNative i] at hh
    exact hh.2
  obtain ⟨Tp,Pphase,hpCost,hPrescribed⟩ := family.exists_uniform_parameter_raw_profiles
    A hd.atlas_smooth seed.sourceNormDomain hOmega hd.source_norm_subset B.chart S
    (fun i z hz => hQT i.2 (hSQ i z hz)) hSR
  refine ⟨Tp,Pphase,hpCost,hPrescribed,?_⟩
  intro Mgp Bchi Bnu Mphase Csrc amplitude u
  have hMgp j : 0 ≤ Mgp j := (family.positive _).1.le
  have hBchi j : 0 ≤ Bchi j := (family.positive _).2.1.le
  have hBnu j : 0 ≤ Bnu j := (family.positive _).2.2.le
  have hMphase j : 0 ≤ Mphase j := (hpCost _).2.le
  obtain ⟨Ku,hKu,hKu0,hproduce⟩ := jointBackground_grouped_q440_physical_mean_producer
    (m := m) (d := d) (N := N) (Tr := Tr) (Λ := Fin seed.primaryCount) (Β := Β)
    (Sub := fun l => Fin (family.refinement l).count)
    A hd.atlas_smooth B hB Q hQ hQT b p₀ hp₀ S hS hSO hSQ (fun _ => Tp)
    (fun j k => (hpCost k).1.le) weight Mgp Bchi Bnu Mphase hMgp hBchi hBnu hMphase rho hrho
  obtain ⟨Cback,Tcost,Tpfirst,Tobs,Phfirst,hCback,hFirstT,hPhfirst,hAtlas⟩ :=
    actualProbeInitialSupply_signed_carrier_atlas_uniform (Tr := Tr) (Β := Β)
      Data hd hs rfl hQ hOmega F0 hF0 hImm waves weight hweight family
      (fun l x => seed.cutoff l (0,x)) (fun l x => seed.phase l (0,x))
      (fun _ => rfl) (fun _ => rfl) O seeds
  obtain ⟨_,Kufirst,hKufirst,_,hu,huj⟩ := passiveOriginalSmallParameter_joint_profiles (Es := D)
    B hB Q hQ hQT amplitude (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀ hp₀
  refine ⟨Ku,hKu,hKu0,?_⟩
  intro ProbeB HBound Rsub reserve hc Bnd Mg Dinput hBnd hMg hDinput Tb hTb L C cap
  let R := round4ParameterProbeForcedProfile HBound ProbeB C 444
  let C0 := fun s => ProbeB s+max 0 (C s (HBound (s+444)))
  let Cd := fun i s => max 0 ((C s (max (R i (s+444)) (R (i+1) (s+444))))*Dinput s)
  let Bfirst := Cback (Bnd 885 (R 441 1329))
  let Mgfirst := Mg 885+family.geometryBudget 1329+jointSecondarySeedGeometryBudget seeds 885
  let Tbfirst := fun k => Tb k+Tcost k*bufferedTransitionPrefix Tb k
  have hBfirst : 0 ≤ Bfirst := hCback _ (hBnd _ _)
  have hMgfirst : 0 ≤ Mgfirst := by
    exact add_nonneg (add_nonneg (hMg 885) (family.positive 1329).1.le)
      (jointSecondarySeedGeometryBudget_positive seeds 885).le
  have hTbfirst k : 0 ≤ Tbfirst k := add_nonneg (hTb k)
    (mul_nonneg (hFirstT k).1 (zero_le_one.trans (one_le_bufferedTransitionPrefix hTb k)))
  let RP := ∑ l, (family.refinement l).count
  let RS := Fintype.card (Σ rec, Fin (seeds rec).refinement.count)
  let KC := jointSecondarySeedCutoffBudget seeds 885
  have hKC : 0 ≤ KC := (jointSecondarySeedCutoffBudget_positive seeds 885).le
  obtain ⟨CU,hCU,hMap⟩ := actualProbeInitialSupply_carrier_original_map_from_raw
    (M := M) (P := P) (Tr := ℝ) (m := m) (d := d) (N := N) (p := d) (count := B.count)
    (Λ := Fin seed.primaryCount) (Β := Β) (Pieces := fun l => Fin (family.refinement l).count)
    (Sub := Σ rec, Fin (seeds rec).refinement.count)
    1329 885 440 442 440 442 Rsub L RP RS (by omega) (by omega) (by omega) (by omega)
    le_rfl reserve Bfirst Mgfirst KC (family.cutoffBudget 1329) (family.normalBudget 1329) (Kufirst 885) Phfirst
    hc hBfirst hMgfirst hKC (family.positive 1329).2.1.le (family.positive 1329).2.2.le
    (hKufirst 885) hPhfirst weight Tbfirst Tpfirst (fun _ => 1) Tobs hTbfirst
    (fun k => (hFirstT k).2.1) (by intro; norm_num) (fun k => (hFirstT k).2.2)
  obtain ⟨CR,hCR,hRest⟩ := actualProbeInitialSupply_carrier_original_remainder_from_raw
    (M := M) (P := P) (Tr := ℝ) (m := m) (d := d) (N := N) (p := d) (count := B.count)
    (Λ := Fin seed.primaryCount) (Β := Β) (Pieces := fun l => Fin (family.refinement l).count)
    (Sub := Σ rec, Fin (seeds rec).refinement.count)
    1329 885 440 442 440 442 Rsub L RP RS (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) le_rfl
    reserve Bfirst Mgfirst KC (family.cutoffBudget 1329) (family.normalBudget 1329) (Kufirst 885) Phfirst
    hc hBfirst hMgfirst hKC (family.positive 1329).2.1.le (family.positive 1329).2.2.le
    (hKufirst 885) hPhfirst weight (fun l => ne_of_gt (hweight l))
    Tbfirst Tpfirst (fun _ => 1) Tobs hTbfirst
    (fun k => (hFirstT k).2.1) (by intro; norm_num) (fun k => (hFirstT k).2.2)
  obtain ⟨CS,hCS,hSecondaryNonneg,hSecondaryLimit,hSecondary⟩ :=
    actualProbeInitialSupply_signed_secondary_original_responses (Tr := Tr) (Β := Β)
      seed B Q hQ hQT hSampling hd hs hOmega F0 hF0 hImm waves weight hweight family O seeds
      Rsub reserve (Bnd 885 (R 441 1329)) (Mg 885) (Kufirst 885)
      hc (hBnd _ _) (hMg _) (hKufirst _) Tb hTb
  let CM := max (parameterRound2_finiteMeanErrorCost C0 Cd 444 441 440) 0
  have hCM : 0 ≤ CM := le_max_right _ _
  refine ⟨CU,CR+CM,CS,hCU,add_nonneg hCR hCM,hCS,hSecondaryNonneg,hSecondaryLimit,?_,?_⟩
  · exact round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C 440 444
  intro scale hscale ell hell hell1 H hH F hF g hg gCutoff gPhase primary supply geometry
    label epsilon he hecap delta hdelta hdeltatau c chi nu a phase vf meanProbe background U coordinates
  have ha l s : Round3ParameterChartPreserves (a l s) := passiveParameterChart_preserves (0 : Z) _
  let Omega := fun (_ : ℕ) (i : Fin A.count × Fin B.count) => (B.chart i.2).target ×ˢ (A.chart i.1).target
  have hOmegaOpen j i : IsOpen (Omega j i) := (B.chart i.2).open_target.prod (A.chart i.1).open_target
  have hSamples j i : (parameterTensorModelEquiv (m+1) d) ⁻¹' S i ⊆ Omega j i := by
    rw [hNative i]
    exact Set.prod_mono (hQT i.2) (hd.source_norm_subset i.1)
  let profiles := fun j i => Classical.choice (hPrescribed scale hscale (j+444) j ell hell.le hell1 i)
  obtain ⟨Kt,hvalue,hreserve,hbound,hraw,Mean,hMean,hMeanBound⟩ :=
    (hproduce H HBound Rsub L reserve hc Bnd Mg Dinput hBnd hMg hDinput Tb hTb).2
      ell hell hell1 hH F hF g hg primary supply label c chi nu a ha phase Omega hOmegaOpen
      (fun _ _ => Subset.rfl) hSamples profiles epsilon he hecap delta hdelta
  obtain ⟨raw⟩ := hraw 441 le_rfl 885
  rw [actualProbeInitialSupply_restrict_univ F g] at raw
  obtain ⟨atlas⟩ := hAtlas (Bnd 885 (R 441 1329)) (Mg 885) (hBnd _ _) (hMg 885) Tb hTb (Kufirst 885)
    scale hscale Rsub reserve (epsilon*ell) ell delta hell.le hell1 g gCutoff gPhase
    (background 441) primary u hu (huj 885 ell hell.le hell1) raw geometry
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  have htau : 0 < epsilon*ell := mul_pos he hell
  have htaul : epsilon*ell ≤ ell := by nlinarith
  let support := fun l => (univ : Set P) ×ˢ K l
  let pieceK := fun l s => {z : P × M | (0,z.2) ∈ tsupport ((family.refinement l).cutoff s)}
  let choice := jointSecondarySeedPaddedChoice (P := P) seeds
  have hchoice := jointSecondarySeedPaddedChoice_preserves (P := P) seeds
  have hmap := hMap A B.chart S F hF g hg label c chi nu phase a ha
    (background 441) (background 441) u univ primary support pieceK choice hchoice (epsilon*ell) ell delta 0
    htau htaul hell1 hdelta.le hdeltatau atlas
  obtain ⟨Rest,hRestValue,hRestBound⟩ := hRest A hd.atlas_smooth B.chart S hS hSO F hF g hg
    label c chi nu phase a ha (background 441) (background 441) u univ primary support pieceK choice hchoice
    (epsilon*ell) ell delta 0 htau htaul hell1 hdelta.le hdeltatau atlas
  have hMeanCost : parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell 440 Mean ≤
      delta^2*((epsilon*ell/ell)^(440+1)*CM) :=
    probes_selected_q440_scalar_mean_factor _ epsilon ell delta
      (parameterRound2_finiteMeanErrorCost C0 Cd 444 441 440) hell.ne' he.le (hMeanBound 440)
  have herr := actualProbeInitialSupply_same_mean_germ_add A B.chart S univ hS hSO
    (fun z => F z.1 z.2) U
    (actualProbeInitialGroupedMean F hF g label c vf phase (epsilon*ell) delta
      442 442 a (background 441) u)
    H.val 440 440 delta (epsilon*ell) ell CR CM hdelta.le hdeltatau htau htaul hell1 hCM
    Rest Mean hRestValue hMean hRestBound hMeanCost
  refine ⟨⟨hmap.1,hmap.2.1,hmap.2.2,herr⟩,?_⟩
  intro t ht ht1 hTau hEll hDelta
  have rawPaper : ∀ i : Fin A.count × Fin B.count,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) 1329 442 885 Rsub L
        reserve (Bnd 885 (R 441 1329)) (Mg 885) Tb
        (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
        (round3ParameterNativePrimary F g (B.chart i.2))
        (fun p => background 441 ((B.chart i.2).symm p))
        (fun p => background 441 ((B.chart i.2).symm p))
        (round3ParameterNativeDomain (B.chart i.2) (univ : Set (P × M)))
        (fun l => round3ParameterNativeDomain (B.chart i.2) (primary l)) (A.chart i.1)
        (actualRawObserverOpen (A.chart i.1) (round3ParameterNativeDomain (B.chart i.2) (univ : Set (P × M))))
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) (t^((6:ℝ)/5)) (t^((11:ℝ)/10)) 0 := by
    intro i
    rw [← hTau,← hEll]
    exact raw i
  have huPaper : ∀ k, k ≤ 885 → ∀ (i : Fin B.count) (z : X), z.1 ∈ Q i →
      (t^((11:ℝ)/10))^k*‖iteratedFDeriv ℝ k (fun y : X => u ((B.chart i).symm y.1)) z‖ ≤ Kufirst 885 := by
    simpa only [hEll] using huj 885 ell hell.le hell1
  have hsec := hSecondary scale hscale t ht ht1 g hg gCutoff gPhase
    (background 441) primary u hu huPaper rawPaper geometry label
  simpa only [vf,hTau,hDelta] using hsec

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_selected_source_q440_with_secondary

#print axioms GlobalEmbedding.Continuation.ProbesSelectedOriginalProfiles
