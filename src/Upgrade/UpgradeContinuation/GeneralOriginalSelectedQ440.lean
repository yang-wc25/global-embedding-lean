import UpgradeContinuation.GeneralSourceSelectedQ440
import ProbesClosure.OriginalSelectedQ440
import NormalPolar.PassiveOriginalRescaledRawOutput
import NormalPolar.PassiveOriginalRescaledPhysical
import NormalPolar.PassiveRawRecenter

/-!
# One original primary supplier, original source witness and same q440 map

The original passive/rescaled primary factory is called once. This theorem
retains its numerical record and literal reserve supplier, the selected
original grouped source profiles, and all existing same-U map/error/secondary
outputs. The reserve radius used in the original construction is exactly
half this retained primary radius. A downstream background sharp theorem
therefore need not choose either source profiles or primary numbers again.

This is an explicit refinement of the existing original q440 orchestration;
all analytic constructors are reused without modifying their statements.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical BigOperators
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
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
private local instance probesSelectedGeneralOriginalQ440SignedRecordFintype {Label : Type*} [Fintype Label] [DecidableEq Label] : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

abbrev probesSelectedGeneralOriginalQ440SecondaryStatement
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hp₀ : IncrementsOriginalPhaseConditions seed hd₀ hs₀)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl Z)
    (Rsub : ℕ) (reference : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub Rsub)
    (cF reserve0 : ℝ) (he₀ : IncrementsOriginalCoordinateEllipticityInputs seed cF)
    (hl₀ : IncrementsOriginalLinearSmoothInputs seed)
    (hc₀ : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hr₀ : IncrementsOriginalDecompositionReserveInputs seed reserve0)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (hs : IncrementsOriginalSmoothInputs (passiveOriginalData (0 : Z) seed B Q))
    (hOmega : ∀ i, IsCompact (seed.sourceNormDomain i))
    (SeedPacket : ℕ → ℝ)
    (hSeed : ∀ n ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile seed n ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile seed n ell).toReal ≤ SeedPacket n)
    (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => seed.F (0,x)))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x)) hF0)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (family : GeneralLegalWaveRawFamily (fun x => seed.F (0,x)) hF0 waves weight)
    (b : Fin B.count) (p₀ : P) (hpP : p₀ ∈ B.inner b)
    : Prop :=
    let Data := passiveOriginalData (0 : Z) seed B Q
    let A := seed.atlas
    let S := incrementsOriginalEvaluation A B.chart seed.sourceNormDomain Q univ
    let hS := parameterRound2_originalEvaluation_univ_compact A B.chart seed.sourceNormDomain Q
      hOmega hQ hd.source_norm_subset hQT
    let hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i := fun _ _ hy => hy.1
    let F0 := fun x => seed.F (0,x)
    let g0 := passiveOriginalReferencePrimary seed hd₀ hs₀ hn₀ base Rsub reference
    let gp := passiveParameterPrimary (P := P) (0 : Z) (fun p x => seed.F (p,x)) g0
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
    ∃ rho : ℝ, ∃ hrho : 0 < rho, ∃ Tp Pphase : ℕ → ℝ,
      (∀ k, 0 < Tp k ∧ 0 < Pphase k) ∧
    ∃ numbers : Round3RepairMeanPrimitiveProfiles,
      rho = numbers.rho/2 ∧
      ProbesSelectedPrimarySupplier A B S hS hSO F0 hF0 gp Data.primaryDomain Data.H numbers ∧
      ProbesSelectedGeneralProfiles F0 hF0 waves weight family A B S Tp Pphase ∧
    let Mgp := fun j => family.geometryBudget (max (j+444) (j+1))
    let Bchi := fun j => family.cutoffBudget (j+444)
    let Bnu := fun j => family.normalBudget (j+444)
    let Mphase := fun j => Pphase (j+1)
    let Csrc := jointGroupedPrescribedZeroSourceCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d d 444 442 Tp weight (Mgp 0) (Bchi 0) (Bnu 0) (Mphase 0)
    let amplitude := passiveOriginalReserveAmplitude Csrc rho
    let u := passiveOriginalSmallParameter B amplitude
      (passiveOriginalReserveAmplitude_pos Csrc rho hrho) b p₀
    ∀ (H0 : parameterRound2_originalTensorGermSpace A B.chart S univ), H0.val = Data.H →
    ∀ HBound : ℕ → ℝ,
    ∃ cap CU CE CS : ℝ, 0 < cap ∧ 0 ≤ CU ∧ 0 ≤ CE ∧ 0 ≤ CS ∧
      (∀ t, 0 ≤ actualProbeSecondaryModulus CS t) ∧
      Filter.Tendsto (actualProbeSecondaryModulus CS) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart S univ),
    (∀ s, parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell s H ≤ HBound s) →
    parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell 0 (H-H0) ≤ rho →
    let F := fun _ : P => scale • F0
    let hF := fun _ : P => contMDiff_const_rescale F0 hF0 scale
    let g := passiveRescaledPrimary (fun _ : P => F0) (fun _ => hF0) gp scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale)
    ∀ (label : (Fin r × Bool) ↪ Fin d) (epsilon : ℝ), 0 < epsilon → epsilon < cap →
    ∀ (delta : ℝ), 0 < delta → delta ≤ epsilon*ell →
    let c : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P → D → M := fun l s (_ : P) => (family.piece l).seed.coordinate s 0
    let chi : (l : Fin r) → Fin (family.piece l).seed.refinement.count → P × D → ℝ := fun l s (z : P × D) => (family.piece l).seed.cutoffCoordinates s (0,z.2)
    let nu : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
      normalSpace (I := IM) (F p) (c l s p x) := fun l s (_ : P) x => actualRescaledNormal F0 hF0 scale
      (GeneralLegalWaveSeed.contraction_ne_zero scale hscale) ((family.piece l).seed.coordinate s 0 x)
      ((waves l).normal ((family.piece l).seed.coordinate s 0 x))
    let a : (l : Fin r) → Fin (family.piece l).seed.refinement.count → OpenPartialHomeomorph (P × M) (P × D) := fun l s => passiveParameterChart (P := P) (0 : Z) ((family.piece l).seed.physicalChart s)
    let phase : Fin r → P × M → ℝ := fun l (z : P × M) => weight l*(waves l).phase z.2
    let vf : (l : Fin r) → (s : Fin (family.piece l).seed.refinement.count) → (p : P) → (x : D) →
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

theorem probes_selected_general_original_q440_with_secondary
    (seed : IncrementsOriginalNativeData (m+1) 0 N M Z)
    (hd₀ : IncrementsOriginalDomainConditions seed) (hs₀ : IncrementsOriginalSmoothInputs seed)
    (hp₀ : IncrementsOriginalPhaseConditions seed hd₀ hs₀)
    (hn₀ : IncrementsOriginalFreeNormalConditions seed hd₀ hs₀)
    (hi₀ : IncrementsOriginalSliceImmersionInputs seed)
    (hAll : seed.parameterSet = univ)
    (base : Fin seed.atlas.count × Fin seed.parameterCount)
    (hId : seed.parameterChart base.2 = OpenPartialHomeomorph.refl Z)
    (Rsub : ℕ) (reference : Round3PreparedReferencePrimaryPacket seed hd₀ hs₀ hn₀ base Sub Rsub)
    (cF reserve0 : ℝ) (he₀ : IncrementsOriginalCoordinateEllipticityInputs seed cF)
    (hl₀ : IncrementsOriginalLinearSmoothInputs seed)
    (hc₀ : IncrementsOriginalQualitativeDecompositionInputs seed)
    (hr₀ : IncrementsOriginalDecompositionReserveInputs seed reserve0)
    (B : BufferedAtlas P Ep) (hB : IsSmoothBufferedAtlas B)
    (hforward : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,Ep) ∞ (B.chart i))
    (Q : Fin B.count → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hQT : ∀ i, Q i ⊆ (B.chart i).target)
    (hSampling : ∀ i, tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas B) i ⊆ Q i)
    (hd : IncrementsOriginalDomainConditions (passiveOriginalData (0 : Z) seed B Q))
    (hs : IncrementsOriginalSmoothInputs (passiveOriginalData (0 : Z) seed B Q))
    (hOmega : ∀ i, IsCompact (seed.sourceNormDomain i))
    (SeedPacket : ℕ → ℝ)
    (hSeed : ∀ n ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile seed n ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile seed n ell).toReal ≤ SeedPacket n)
    (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ (fun x => seed.F (0,x)))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) (fun x => seed.F (0,x)) hF0)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (family : GeneralLegalWaveRawFamily (fun x => seed.F (0,x)) hF0 waves weight)
    (b : Fin B.count) (p₀ : P) (hpP : p₀ ∈ B.inner b)
    : probesSelectedGeneralOriginalQ440SecondaryStatement seed hd₀ hs₀ hp₀ hn₀ hi₀ hAll base hId Rsub reference cF reserve0 he₀ hl₀ hc₀ hr₀
      B hB hforward Q hQ hQT hSampling hd hs hOmega SeedPacket hSeed hF0 waves weight hweight family b p₀ hpP := by
  unfold probesSelectedGeneralOriginalQ440SecondaryStatement
  intro Data A S hS hSO F0 g0 gp K signedPhase O seeds
  have hzero : (0 : Z) ∈ seed.parameterOpen := hd₀.parameter_subset (by rw [hAll]; trivial)
  obtain ⟨Packet,Forward,Inverse,Meta,hPacket,hSupply⟩ :=
    passiveOriginal_reference_rescaled_raw_numbers (r := r) seed hd₀ hs₀ hp₀ hn₀ hi₀ hAll base hId
      Rsub reference cF reserve0 he₀ hl₀ hc₀ hr₀ B hB hforward Q hQ hQT hS SeedPacket hSeed 440 hd hs
  let numbers := round3RepairOriginalMeanNumbers m d N 440 Rsub
    (Fintype.card (Fin seed.primaryCount ⊕ Fin r)) (cF/4) (reference.cT/4)
    reserve0 hr₀.reserve_pos Packet Forward Inverse Meta hPacket
  let rho := numbers.rho/2
  have hrho : 0 < rho := div_pos numbers.rho_pos (by norm_num)
  obtain ⟨Tp,Pphase,hpCost,hPrescribed,Ku,hKu,hKu0,hcomplete⟩ :=
    probes_selected_general_source_q440_with_secondary (Tr := ℝ) (Β := Sub)
      seed B hB Q hQ hQT hSampling hd hs hOmega F0 hF0 (hi₀.immersion 0 hzero)
      waves weight hweight family b p₀ hpP rho hrho O seeds
  refine ⟨rho,hrho,Tp,Pphase,hpCost,numbers,rfl,?_,hPrescribed,?_⟩
  · intro scale hscale ell hell hell1 H0 hH0
    exact hSupply scale hscale.1 hscale.2 ell hell hell1 H0 hH0
  intro Mgp Bchi Bnu Mphase Csrc amplitude u H0 hH0 HBound
  let ProbeB := fun j => ((j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j)*
    jointGroupedPrescribedMeanUniformCost (fun l => Fin (family.piece l).seed.refinement.count)
      m N d (j+444) 442 j Tp weight (Mgp j) (Bchi j) (Bnu j) (Mphase j) (Ku j)
  let C := round3ParameterMeanSizeCost.{uM,0,uP,0,uSub} (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    440 numbers.Rsub numbers.Lprimary (by omega) numbers.reserve numbers.reserve_pos
    numbers.Bnd numbers.Mg numbers.Bnd_nonneg numbers.Mg_nonneg numbers.T numbers.T_nonneg
  let cap := round4ParameterProbeForcedCap HBound rho ProbeB C 440 444
  obtain ⟨CU,CE,CS,hCU,hCE,hCS,hSecondaryNonneg,hSecondaryLimit,hcap,hresult⟩ := hcomplete HBound numbers.Rsub numbers.reserve numbers.reserve_pos
    numbers.Bnd numbers.Mg numbers.Dinput numbers.Bnd_nonneg numbers.Mg_nonneg numbers.Dinput_nonneg
    numbers.T numbers.T_nonneg
  refine ⟨cap,CU,CE,CS,hcap,hCU,hCE,hCS,hSecondaryNonneg,hSecondaryLimit,?_⟩
  intro scale hscale ell hell hell1 H hH hCenter F hF g label epsilon he hecap delta hdelta hdeltatau
  have original := hSupply scale hscale.1 hscale.2 ell hell hell1 H0 hH0
  have supply := round3Parameter_canonical_supply_recenter A B.chart S univ
    (parameterRound2_originalTensorGermSeminorm A B.chart S univ hS hSO ell)
    H0 H numbers.rho 440 numbers.Rsub numbers.Lprimary numbers.reserve
    numbers.Bnd numbers.Mg numbers.Dinput numbers.T F hF g Data.primaryDomain ell original hCenter
  have hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k) :=
    passiveParameterPrimary_chart_preserves (0 : Z) (fun p x => seed.F (p,x)) g0
  have hGeometry := passiveOriginal_reference_rescaled_physical_geometry seed hd₀ hs₀ hn₀ hi₀ hAll
    base hId Rsub reference B hB Q hS hd hs scale hscale.1
  exact hresult scale hscale ell hell hell1 H hH g hg (fun _ => rfl) (fun _ => rfl)
    Data.primaryDomain supply (fun i => Classical.choice (hGeometry i))
    label epsilon he hecap delta hdelta hdeltatau

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_selected_general_original_q440_with_secondary

