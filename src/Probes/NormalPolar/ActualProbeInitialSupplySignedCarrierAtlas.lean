import NormalPolar.ActualProbeInitialSupplySignedCarrierPrimary
import NormalPolar.ActualProbeInitialSupplySignedAtlasBackground
import NormalPolar.JointSecondarySignedCarrierBindings
import NormalPolar.JointSecondarySignedPrescribedConstruction
import NormalPolar.JointSecondaryNativeCarrier
import NormalPolar.JointMixedSignedObserverConstruction
import NormalPolar.JointMixedObserverBudget
import NormalPolar.JointMixedObserverTransitionBudget
import NormalPolar.PassiveWaveSeedNativePhysical

/-! Construct the entire original first-wave raw atlas from the actual
original wave family, fixed signed seeds and the native background supplied
by q440. Every extra host, compact observation sample, source partition,
physical prescribed geometry and original observer is built internally.
The original open primary domains and closed amplitude carriers are distinct.
All first-wave costs are fixed before the contraction and reconstruction scales. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
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
local instance actualProbeInitialSupplySignedCarrierAtlasSignedRecordFintype {Label : Type*} [Fintype Label] [DecidableEq Label] : Fintype (ActualSecondarySignedRecord Label) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem actualProbeInitialSupply_signed_carrier_atlas_uniform
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hAll : Data.parameterSet = univ)
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i))
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (F0 : M → V) (hF0 : ContMDiff IM 𝓘(ℝ,V) ∞ F0)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F0 x))
    (waves : Fin r → LocalLegalWave (n := m+1) F0 hF0) (weight : Fin r → ℝ)
    (hweight : ∀ l, 0 < weight l)
    (family : OriginalWaveSeedRescaledFamily F0 hF0 waves weight)
    (chi theta : Fin Data.primaryCount → M → ℝ)
    (hChi : ∀ l, Data.cutoff l = fun z => chi l z.2)
    (hTheta : ∀ l, Data.phase l = fun z => theta l z.2) :
    let K : (Fin Data.primaryCount ⊕ Fin r) → Set M :=
      Sum.elim (fun l => tsupport (chi l)) (fun l => tsupport ((waves l).cutoff : M → ℝ))
    let signedPhase := fun (rec : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r)) x =>
      jointSecondarySignedPhase
        (Sum.elim (fun l (z : Ep × M) => theta l z.2)
          (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val (0,x)
    ∀ (O : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r) → Set M)
      (seeds : (rec : ActualSecondarySignedRecord (Fin Data.primaryCount ⊕ Fin r)) →
        JointSecondarySignedSeed («Ep» := Ep) F0 hF0 (signedPhase rec)
          (K rec.val.1.1 ∩ K rec.val.1.2) (O rec)),
    ∃ C : ℝ → ℝ, ∃ Tcost Tpfirst Tobs : ℕ → ℝ, ∃ Phfirst : ℝ,
      (∀ B, 0 ≤ B → 0 ≤ C B) ∧
      (∀ k, 0 ≤ Tcost k ∧ 0 ≤ Tpfirst k ∧ 0 ≤ Tobs k) ∧ 0 ≤ Phfirst ∧
      ∀ (Bnd Mg : ℝ) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
      (Tb : ℕ → ℝ) (hTb : ∀ k, 0 ≤ Tb k) (Ku : ℝ),
    let Mgfirst := Mg+family.geometryBudget 1329+jointSecondarySeedGeometryBudget seeds 885
    let Tbfirst := fun k => Tb k+Tcost k*bufferedTransitionPrefix Tb k
    ∀ (scale : ℝ) (hscale : scale ∈ Icc (1/2:ℝ) 1)
      (Rsub : ℕ) (reserve tau ell delta : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m)
        (Λ := Fin Data.primaryCount) (Β := Β) (fun _ : P => scale • F0))
      (gCutoff : ∀ l, g.cutoff l = Data.cutoff l) (gPhase : ∀ l, g.phase l = Data.phase l)
      (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (primaryDomain : Fin Data.primaryCount → Set (P × M))
      (u : P → Fin d → ℝ)
      (hu : ∀ i, ContDiffOn ℝ ∞ (fun z : X => u ((Data.parameterChart i).symm z.1))
        (Prod.fst ⁻¹' (Data.parameterChart i).target))
      (huj : ∀ k, k ≤ 885 → ∀ (i : Fin Data.parameterCount) (z : X),
        z.1 ∈ Data.parameterNormDomain i → ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => u ((Data.parameterChart i).symm y.1)) z‖ ≤ Ku)
      (raw : ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) 1329 442 885 Rsub
          (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) reserve Bnd Mg Tb
          (fun _ : Ep => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
          (round3ParameterNativePrimary (fun _ : P => scale • F0) g (Data.parameterChart i.2))
          (fun p => input ((Data.parameterChart i.2).symm p))
          (fun p => input ((Data.parameterChart i.2).symm p))
          (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M)))
          (fun l => round3ParameterNativeDomain (Data.parameterChart i.2) (primaryDomain l))
          (Data.atlas.chart i.1)
          (actualRawObserverOpen (Data.atlas.chart i.1)
            (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))))
          ((parameterTensorModelEquiv (m+1) d) ⁻¹'
            incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
              Data.parameterNormDomain Data.parameterSet i) tau ell 0)
      (geometry : ∀ i : Fin Data.atlas.count × Fin Data.parameterCount,
        ActualOriginalPrimaryPhysicalGeometry (fun _ : Ep => scale • F0)
          (fun _ => contMDiff_const_rescale F0 hF0 scale)
          (round3ParameterNativePrimary (fun _ : P => scale • F0) g (Data.parameterChart i.2))),
    Nonempty (ActualProbeInitialCarrierRawAtlas (Tr := ℝ)
      Data.atlas Data.parameterChart
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet)
      (fun _ : P => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale) g
      (fun l s _ => (family.outer l s).spatialChart.symm)
      (fun l s (z : P × D) => (family.refinement l).cutoffCoordinates s (0,z.2))
      (fun l s _ x => actualRescaledNormal F0 hF0 scale
        (originalWave_contraction_ne_zero scale hscale) ((family.outer l s).spatialChart.symm x)
        ((waves l).normal ((family.outer l s).spatialChart.symm x)))
      (fun l (z : P × M) => weight l*(waves l).phase z.2)
      (fun l s => passiveParameterChart (0 : Z) (family.inner l s).chart)
      input input u univ primaryDomain (fun l => (univ : Set P) ×ˢ K l)
      (fun l s => {z : P × M | (0,z.2) ∈ tsupport ((family.refinement l).cutoff s)})
      (jointSecondarySeedPaddedChoice seeds) 1329 885 440 442 440 Rsub
      (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) (∑ l, (family.refinement l).count)
      (Fintype.card (Σ rec, Fin (seeds rec).refinement.count)) reserve (C Bnd) Mgfirst
      (jointSecondarySeedCutoffBudget seeds 885) (family.cutoffBudget 1329) (family.normalBudget 1329)
      Ku Phfirst tau ell delta 0 Tbfirst Tpfirst (fun _ => 1) Tobs) := by
  intro K signedPhase O seeds
  let Spatial := passiveOriginalSpatialNormSample Data
  have hSpatial i := passiveOriginal_spatial_norm_sample Data hd i (hOmega i)
  obtain ⟨Cback,Tcost,hTcost,hCback,hbackground⟩ :=
    actualProbeInitialSupply_signed_atlas_background_uniform (Tr := Tr) (Β := Β)
      Data hd hs hAll hQ hOmega F0 hF0 signedPhase
      (fun rec => K rec.val.1.1 ∩ K rec.val.1.2) O seeds
  obtain ⟨Tprimary,Pprimary,hprimaryPos,hprimary⟩ :=
    actualProbeInitialSupply_signed_carrier_primary_uniform (Tr := Tr) (Β := Β)
      Data hd hAll hOmega F0 hF0 waves weight family
  obtain ⟨Thost,Phost,hhostPos,hhost⟩ :=
    jointSecondary_signed_prescribed_from_original_waves (P := P) («Ep» := Ep)
      family seeds Spatial (fun i => (hSpatial i).1)
  choose Ti hTi hObserver using fun i : Fin Data.atlas.count =>
    jointMixedSignedObserver_from_actual_seeds (P := P) F0 hF0 signedPhase K O seeds
      (Data.atlas.chart i) (hd.atlas_smooth.chart_mem i) (Spatial i)
      (hSpatial i).1 (hSpatial i).2.1
  let Tpfirst := fun k => 1+Tprimary k+Thost k
  let Tobs := fun k => 1+∑ i, Ti i k
  let Phfirst := Pprimary 442+Phost 886
  have hTobs i k : Ti i k ≤ Tobs k := by
    have hh : Ti i k ≤ ∑ a, Ti a k :=
      Finset.single_le_sum (fun a _ => (hTi a k).le) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left (by norm_num))
  have hTobs0 k : 0 ≤ Tobs k := by
    dsimp [Tobs]
    exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => (hTi i k).le))
  refine ⟨fun B => Cback 1329 885 B,Tcost,Tpfirst,Tobs,Phfirst,
    fun B hB => (hCback 1329 885 B hB).1,
    fun k => ⟨hTcost k,by dsimp [Tpfirst]; linarith [(hprimaryPos k).1,(hhostPos k).1],hTobs0 k⟩,
    add_nonneg (hprimaryPos 442).2.le (hhostPos 886).2.le,?_⟩
  intro Bnd Mg hBnd hMg Tb hTb Ku Mgfirst Tbfirst scale hscale Rsub reserve tau ell delta hell hell1
    g gCutoff gPhase input primaryDomain u hu huj raw geometry
  have hGbg : Mg ≤ Mgfirst := by
    dsimp [Mgfirst]
    linarith [(family.positive 1329).1,jointSecondarySeedGeometryBudget_positive seeds 885]
  have hGp : family.geometryBudget 1329 ≤ Mgfirst := by
    dsimp [Mgfirst]
    linarith [jointSecondarySeedGeometryBudget_positive seeds 885]
  have hGs : jointSecondarySeedGeometryBudget seeds 885 ≤ Mgfirst := by
    dsimp [Mgfirst]
    linarith [(family.positive 1329).1]
  have hTbLift k : Tb k ≤ Tbfirst k :=
    le_add_of_nonneg_right (mul_nonneg (hTcost k)
      (zero_le_one.trans (one_le_bufferedTransitionPrefix hTb k)))
  have hTpPrimary k : 1+Tprimary k ≤ Tpfirst k := le_add_of_nonneg_right (hhostPos k).1.le
  have hTpHost k : Thost k ≤ Tpfirst k := le_add_of_nonneg_left (by
    linarith [(hprimaryPos k).1])
  have hPhPrimary : Pprimary 442 ≤ Phfirst := le_add_of_nonneg_right (hhostPos 886).2.le
  have hPhHost : Phost 886 ≤ Phfirst := le_add_of_nonneg_left (hprimaryPos 442).2.le
  obtain ⟨primary,hPrimaryDomain⟩ := hprimary scale hscale Rsub reserve Bnd Mg
    (Cback 1329 885 Bnd) Mgfirst Ku Phfirst tau ell hBnd (hCback 1329 885 Bnd hBnd).2
    hGbg hGp hPhPrimary Tb Tbfirst Tpfirst hTbLift hTpPrimary hell hell1
    g input primaryDomain (fun l => (univ : Set P) ×ˢ K l) u hu
    (fun k hk => huj k (hk.trans (by omega))) raw
  let gN := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    round3ParameterNativePrimary (fun _ : P => scale • F0) g (Data.parameterChart i.2)
  have hNativeCutoff i l : (gN i).cutoff l = fun z => chi l z.2 := by
    funext z
    change g.cutoff l ((Data.parameterChart i.2).symm z.1,z.2) = _
    rw [gCutoff l,hChi l]
  have hNativePhase i l : (gN i).phase l = fun z => theta l z.2 := by
    funext z
    change g.phase l ((Data.parameterChart i.2).symm z.1,z.2) = _
    rw [gPhase l,hTheta l]
  have hPhase i rec : (fun z : Ep × M => signedPhase rec z.2) =
      jointSecondarySignedPhase (Sum.elim (gN i).phase
        (fun l (z : Ep × M) => weight l*(waves l).phase z.2)) rec.val := by
    have hp : (gN i).phase = fun l z => theta l z.2 := funext (hNativePhase i)
    rw [hp]
    funext z
    dsimp only [signedPhase,jointSecondarySignedPhase]
    cases h₁ : rec.val.1.1 <;> cases h₂ : rec.val.1.2 <;>
      simp only [Sum.elim_inl,Sum.elim_inr]
  have hPiece (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (l : Fin r) (s : Fin (family.refinement l).count) :
      {z : Ep × M | z.1 ∈ (Data.parameterChart i.2).target ∧
        (0,z.2) ∈ tsupport ((family.refinement l).cutoff s)} ⊆
      round3ParameterNativeDomain (Data.parameterChart i.2) ((univ : Set P) ×ˢ K (Sum.inr l)) := by
    intro z hz
    exact ⟨hz.1,mem_univ _,((family.refinement l).cutoff_support s hz.2).1⟩
  have hCarrier i l : incrementsGlobalRelativeSupport
      (round3ParameterNativeDomain (Data.parameterChart i.2) (univ : Set (P × M))) ((gN i).cutoff l) ⊆
      round3ParameterNativeDomain (Data.parameterChart i.2) ((univ : Set P) ×ˢ K (Sum.inl l)) := by
    rw [hNativeCutoff i l]
    exact jointSecondary_native_spatial_cutoff_carrier (Data.parameterChart i.2) (chi l)
  let back := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) rec s =>
    (Classical.choice (hbackground i scale hscale 885 442 1329 442 885 Rsub
      (Fintype.card (Fin Data.primaryCount ⊕ Fin r)) reserve Bnd Mg hBnd Tb hTb (gN i)
      (fun l => by funext z; change g.cutoff l _ = _; rw [gCutoff l])
      (fun l => by funext z; change g.phase l _ = _; rw [gPhase l])
      (fun p => input ((Data.parameterChart i.2).symm p))
      (fun l => round3ParameterNativeDomain (Data.parameterChart i.2) (primaryDomain l))
      _ tau ell hell hell1 (raw i) rec s)).enlargeBudgets
      (Cback 1329 885 Bnd) Mgfirst Tbfirst le_rfl hGbg (fun _ => le_rfl)
  let prescribed := fun (i : Fin Data.atlas.count × Fin Data.parameterCount) rec s =>
    (Classical.choice (hhost scale hscale 885 442 1329 886 ell hell hell1 i.1
      (Data.parameterChart i.2) (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2) rec s)).enlargeBudgets
      Mgfirst (family.cutoffBudget 1329) (family.normalBudget 1329) Phfirst Tpfirst
      hGp le_rfl le_rfl hPhHost hTpHost
  let sourceBase := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    jointSecondarySignedCarrierProfiles (Tr := ℝ) (P := P) (p := d)
      (m := m) (N := N) (r := r) («Ep» := Ep) (Λ := Fin Data.primaryCount) (Β := Β)
      (Pieces := fun l => Fin (family.refinement l).count) F0 hF0 signedPhase K O seeds
      (Data.parameterChart i.2) (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2) (Spatial i.1)
      scale hscale 1329 885 440 442 442 Rsub (Fintype.card (Fin Data.primaryCount ⊕ Fin r))
      reserve (Cback 1329 885 Bnd) Mgfirst (family.cutoffBudget 1329) (family.normalBudget 1329)
      Ku Phfirst tau ell delta 0 hell hell1 hGs Tbfirst Tpfirst (gN i)
      (fun l s _ => (family.outer l s).spatialChart.symm)
      (fun l s (z : X) => (family.refinement l).cutoffCoordinates s (0,z.2))
      (fun l s _ x => actualRescaledNormal F0 hF0 scale
        (originalWave_contraction_ne_zero scale hscale) ((family.outer l s).spatialChart.symm x)
        ((waves l).normal ((family.outer l s).spatialChart.symm x)))
      (fun l s => round3ParameterChartPullback (Data.parameterChart i.2)
        (passiveParameterChart (0 : Z) (family.inner l s).chart))
      (fun l (z : Ep × M) => weight l*(waves l).phase z.2) (hPhase i)
      (fun l => round3ParameterNativeDomain (Data.parameterChart i.2) (primaryDomain l))
      (fun p => input ((Data.parameterChart i.2).symm p))
      (fun p => input ((Data.parameterChart i.2).symm p))
      (fun p => u ((Data.parameterChart i.2).symm p))
      (fun l s => {z : Ep × M | z.1 ∈ (Data.parameterChart i.2).target ∧
        (0,z.2) ∈ tsupport ((family.refinement l).cutoff s)}) (hPiece i) (hCarrier i)
  let sourceBack := fun i : Fin Data.atlas.count × Fin Data.parameterCount => sourceBase i (back i)
  let sourcePrescribed := fun i : Fin Data.atlas.count × Fin Data.parameterCount => sourceBack i (prescribed i)
  let source := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    sourcePrescribed i ((hu i.2).mono (fun _ hz => hz.1))
      (fun k hk z hz => huj k hk i.2 z hz)
  refine ⟨{
    primary := primary
    profiles := source
    choice_eq := ?_
    observer := ?_
    background_geometry := geometry
    prescribed_geometry := ?_ }⟩
  · intro i rec s
    have hbase := jointSecondarySignedNativeRaw_choice seeds (Data.parameterChart i.2)
      (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2) (Spatial i.1)
      scale hscale 885 442 ell hell hell1 rec s
    change ({
      host := (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
      chart := (jointSecondarySignedNativeRaw seeds (Data.parameterChart i.2)
        (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2) (Spatial i.1)
        scale hscale 885 442 ell hell hell1 rec s).chart
      c := (jointSecondarySignedNativeRaw seeds (Data.parameterChart i.2)
        (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2) (Spatial i.1)
        scale hscale 885 442 ell hell hell1 rec s).c
      cutoff := jointSecondarySignedNativeCutoff seeds (Data.parameterChart i.2) rec s} :
      Round3ParameterSecondaryChoice Ep M m) = _
    rw [hbase.1,hbase.2.1]
    rfl
  · intro i
    rw [hPrimaryDomain i]
    have obs := (Classical.choice (hObserver i.1 (Data.parameterChart i.2)
      (Data.parameterNormDomain i.2) (hd.parameter_norm_subset i.2)
      scale hscale 885 441 ell hell hell1)).enlargeBudget hGs
    have obs' := obs.enlargeTransitionBudget (hTobs i.1)
    rw [(hSpatial i.1).2.2] at obs'
    have hSample := passiveOriginal_native_norm_sample Data hd hAll i
    rw [hSample]
    exact obs'
  · intro i l s
    exact passiveWaveSeed_native_physical (Data.parameterChart i.2)
      (fun _ : Z => scale • F0) (fun _ => contMDiff_const_rescale F0 hF0 scale)
      (fun _ => (family.outer l s).spatialChart.symm)
      (fun _ x => actualRescaledNormal F0 hF0 scale (originalWave_contraction_ne_zero scale hscale)
        ((family.outer l s).spatialChart.symm x) ((waves l).normal ((family.outer l s).spatialChart.symm x)))
      (family.inner l s).chart (fun z : Z × M => weight l*(waves l).phase z.2)
      ((family.inner l s).rescaled_physical_geometry (family.outer l s) (family.nested l s)
        (hweight l) hImm scale (originalWave_contraction_ne_zero scale hscale))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_signed_carrier_atlas_uniform
