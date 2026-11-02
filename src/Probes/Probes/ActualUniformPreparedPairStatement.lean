import Probes.ActualUniformPreparedPrimaryFiniteIncrement
import Probes.ActualSecondaryPreparedRawObservations
import Probes.ActualUniformRestrictedScaledStep
import Probes.ActualOriginalIncrementRawBaseTwo
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
variable {m d N c : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

local instance actualUniformPreparedPairStatementRepairChartedSpace : ChartedSpace (Ep × D) (Ep × M) :=
  prodChartedSpace Ep Ep D M
local instance actualUniformPreparedPairStatementRepairIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M

def ActualUniformPreparedPairRepairStatement
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
    (radius : ℝ) (hradius : 0 < radius) : Prop :=
    let Csize := fun s R => parameterRound2_rawMeanOriginalGermNormCost
      (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Label) (Β := SubPrimary)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bmean s R) (Mmean s)
      hc (hBmean s R) (hMmean s) T TP hT hTP
    let Rq := parameterRound2_uniformMeanProfile B0 Csize (q+4) q
    let Brest := fun j => Bmean (actualSecondarySolveOrder q j) (Rq (actualSecondaryInputOrder q j))
    let Mrest := fun j => max (Mmean (actualSecondarySolveOrder q j)) (Msecondary j)
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
      (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W Vprep : Set (Ep × M)) (hVprep : IsOpen Vprep)
      (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B.chart i)
      (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
      (H : parameterRound2_originalTensorGermSpace A B.chart S W),
    let p := parameterRound2_originalTensorGermSeminorm A B.chart S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    ( ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i →
      ∀ k, 1 ≤ k → ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B.chart i.2)) z‖ ≤ TP k) →
    ∀
    (parameterSet : Set Ep)
    (RS : TensorRawCutoffPreparation A BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B parameterSet BP0 TP0 Dp)
    (hbuffer : radius ≤ min B.buffer A.buffer)
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (hsource : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hparameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i)
    (hSinner : ∀ i, S i ⊆ tensorLocalOriginalInner A B parameterSet i),
    ∀ t : ℝ, ell ≤ t → t ≤ 1 →
    ∀ (G : Ep × M → V), ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ G →
    ∀ (hstar h0 : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)),
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart hstar i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart h0 i)
      (incrementsOriginalDifferentiation A B.chart i)) →
    ∀ (delta deltaNext : ℝ), 0 < delta → deltaNext ≠ 0 →
    let Hold := fun t x => (delta^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)) x)
    ∀ budget : ℝ,
    (parameterLocalOriginalTotalPairWeighted A B G Hold q t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
    let mu := (volume : Measure X)
    let kernel := fixedSmoothingKernel mu radius hradius q
    let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
    let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu kernel ell chi G
    let SH := tensorLocalParameterSmoothing A B hA mu kernel ell chi Hold
    H.val = (fun t x => SH t x-(deltaNext/delta)^2 • h0 t x) →
    ∀ (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t)),
    ∀ (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary)
      F) (primary : Label → Set (Ep × M)),
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := Tr) A B.chart S W Vprep p H rho q Rsub Lprimary reserve
      Bmean Mmean Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B.chart S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B.chart S W,
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 → delta ≤ epsilon*ell →
    let Top := parameterRound2_actualGermMeanReserveOperator A B.chart S W p H rho ell
      F hF g q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H rho (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ rho/2) ∧
    ∃ Gdomain : Set (Ep × M), ∃ hGdomain : IsOpen Gdomain,
    Gdomain ⊆ W ∧ Gdomain ⊆ Vprep ∧
    (∀ i, MapsTo (incrementsOriginalJointPoint A B.chart i) (S i) Gdomain) ∧
    let gG := parameterRound2_restrictPrimaryFamily F g Gdomain hGdomain
    let NativeSamples := fun i : Fin A.count × Fin c =>
      parameterRound2_meanParameterMap (m := m) (B.chart i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
    ∀ (hBackground : ∀ z ∈ Gdomain, (fun x => F z.1 x) = (fun x => SF (z.1,x))),
    ∀ (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m),
    let choiceG := fun r a => (choice r a).restrictOpen Gdomain hGdomain
    let U := actualOriginalIncrementMap F hF gG (K q).val (q+2) (epsilon*ell) delta choiceG
    ∀ (j : ℕ)
    (geom : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q j) (j+1) ell (Mrest j) Vprep)
    (hCoordinate : ∀ r a, (geom r a).c = (choice r a).c)
    (hChart : ∀ r a, (geom r a).chart = (choice r a).chart)
    (hPhase : ∀ r a, (geom r a).phase = actualOriginalSecondaryPhase F gG r.val)
    (hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source)
    (hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
    (hHostSource : ∀ r a, (geom r a).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
    (hSupport : ∀ r a, tsupport (fun y : Vprep => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2)) ⊆ Subtype.val ⁻¹' (geom r a).support)
    (hPair : ∀ r a, (geom r a).support ⊆ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2))
    (hPartition : ∀ r : ActualSecondarySignedRecord Label, ∀ y,
      y ∈ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2) → ∑ a, (choice r a).cutoff y = 1)
    (hCut : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ ((choice r a).cutoff ∘ b.symm) (b.symm.trans (geom r a).chart).source)
    (hInv : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ (b.symm.trans (geom r a).chart).symm (b.symm.trans (geom r a).chart).target)
    (hCutJets : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k ≤ (actualSecondarySolveOrder q j), ∀ z ∈ (geom r a).sample, ell^k*‖iteratedFDeriv ℝ k
        ((choice r a).cutoff ∘ b.symm) ((b.symm.trans (geom r a).chart).symm z)‖ ≤ (Kcut j))
    (hInvJets : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k, 1 ≤ k → k ≤ (actualSecondarySolveOrder q j)+1 → ∀ z ∈ (geom r a).sample,
        ell^(k-1)*‖iteratedFDeriv ℝ k (b.symm.trans (geom r a).chart).symm z‖ ≤ Tinv k)
    (hostIndex : ActualSecondarySignedRecord Label → SubSecondary → (Fin A.count × Fin c))
    (hHostIndex : ∀ r a, (choice r a).host = A.chart (hostIndex r a).1)
    (hNativeSamples : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geom r a).chart).symm '' (geom r a).sample ⊆ NativeSamples (hostIndex r a))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF gG)
    (hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) Gdomain)
    (hChartInv : ∀ r a,
      letI : ChartedSpace X X := chartedSpaceSelf X
      ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (geom r a).chart.symm (geom r a).chart.target)
    (hObserverNativeSamples : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(A.chart i.1).symm z.2)) ⁻¹' (geom r a).support →
      (geom r a).chart (z.1,(A.chart i.1).symm z.2) ∈ (geom r a).sample)
    (hObserverJets : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(A.chart i.1).symm z.2)) ⁻¹' (geom r a).support →
      ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((geom r a).chart ∘ (fun z : X => (z.1,(A.chart i.1).symm z.2))) z‖ ≤ Tobs k)
    (hObserverCount : ∀ i (r : ActualSecondarySignedRecord Label), ∀ z ∈ NativeSamples i,
      (Finset.univ.filter (fun a => (z.1,(A.chart i.1).symm z.2) ∈ (geom r a).support)).card ≤ Rsecondary),
    ∀ (geomHigher : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q (j+1)) ((j+1)+1) ell (Mrest (j+1)) Vprep)
    (hCoordinateHigher : ∀ r a, (geomHigher r a).c = (choice r a).c)
    (hChartHigher : ∀ r a, (geomHigher r a).chart = (choice r a).chart)
    (hPhaseHigher : ∀ r a, (geomHigher r a).phase = actualOriginalSecondaryPhase F gG r.val)
    (hHostHigher : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source)
    (hHostInvHigher : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
    (hHostSourceHigher : ∀ r a, (geomHigher r a).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
    (hSupportHigher : ∀ r a, tsupport (fun y : Vprep => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2)) ⊆ Subtype.val ⁻¹' (geomHigher r a).support)
    (hPairHigher : ∀ r a, (geomHigher r a).support ⊆ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2))
    (hPartitionHigher : ∀ r : ActualSecondarySignedRecord Label, ∀ y,
      y ∈ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2) → ∑ a, (choice r a).cutoff y = 1)
    (hCutHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ ((choice r a).cutoff ∘ b.symm) (b.symm.trans (geomHigher r a).chart).source)
    (hInvHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ContDiffOn ℝ ∞ (b.symm.trans (geomHigher r a).chart).symm (b.symm.trans (geomHigher r a).chart).target)
    (hCutJetsHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k ≤ (actualSecondarySolveOrder q (j+1)), ∀ z ∈ (geomHigher r a).sample, ell^k*‖iteratedFDeriv ℝ k
        ((choice r a).cutoff ∘ b.symm) ((b.symm.trans (geomHigher r a).chart).symm z)‖ ≤ (Kcut (j+1)))
    (hInvJetsHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      ∀ k, 1 ≤ k → k ≤ (actualSecondarySolveOrder q (j+1))+1 → ∀ z ∈ (geomHigher r a).sample,
        ell^(k-1)*‖iteratedFDeriv ℝ k (b.symm.trans (geomHigher r a).chart).symm z‖ ≤ Tinv k)
    (hostIndexHigher : ActualSecondarySignedRecord Label → SubSecondary → (Fin A.count × Fin c))
    (hHostIndexHigher : ∀ r a, (choice r a).host = A.chart (hostIndexHigher r a).1)
    (hNativeSamplesHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geomHigher r a).chart).symm '' (geomHigher r a).sample ⊆ NativeSamples (hostIndexHigher r a))
    (primaryGeometryHigher : ActualOriginalPrimaryPhysicalGeometry F hF gG)
    (hOriginalHigher : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) Gdomain)
    (hChartInvHigher : ∀ r a,
      letI : ChartedSpace X X := chartedSpaceSelf X
      ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (geomHigher r a).chart.symm (geomHigher r a).chart.target)
    (hObserverNativeSamplesHigher : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(A.chart i.1).symm z.2)) ⁻¹' (geomHigher r a).support →
      (geomHigher r a).chart (z.1,(A.chart i.1).symm z.2) ∈ (geomHigher r a).sample)
    (hObserverJetsHigher : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(A.chart i.1).symm z.2)) ⁻¹' (geomHigher r a).support →
      ∀ k, 1 ≤ k → k ≤ (j+1)+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((geomHigher r a).chart ∘ (fun z : X => (z.1,(A.chart i.1).symm z.2))) z‖ ≤ Tobs k)
    (hObserverCountHigher : ∀ i (r : ActualSecondarySignedRecord Label), ∀ z ∈ NativeSamples i,
      (Finset.univ.filter (fun a => (z.1,(A.chart i.1).symm z.2) ∈ (geomHigher r a).support)).card ≤ Rsecondary),
    let Hnext := fun t x => (deltaNext^2)⁻¹ • (hstar t x-inducedMetric (I := 𝓙) (fun y => G (t,y)+U (t,y)) x)
    let O := incrementsOriginalDifferentiation A B.chart
    let nextPair := parameterLocalOriginalTotalPairWeighted A B (fun z => G z+U z) Hnext j (epsilon*ell) S
    (∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart (fun z => G z+U z) i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Hnext i) V0) ∧
    nextPair ≠ ⊤ ∧
    ∀ k s : ℕ, 10 ≤ k → s ≤ k+1 → q = 40*(k+1) →
      ell = t^(11/10 : ℝ) → delta = t^k → epsilon*ell = t^(6/5 : ℝ) →
      deltaNext = (t^(6/5 : ℝ))^s →
    let inherited := (parameterLocalOriginalTotalPairWeighted A B G Hold j t
      (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal
    nextPair.toReal ≤
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart G) O S).toReal+
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart h0) O S).toReal+
      (1+j*(paperAtlasCj j (incrementsOriginalTensorCoordinates A B.chart h0) O S).toReal+
        2*C j*(1+budget))*t^(1/5 : ℝ)*(1+inherited)

end GlobalEmbedding.Continuation
