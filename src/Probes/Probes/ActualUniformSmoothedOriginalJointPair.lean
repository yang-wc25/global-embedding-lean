import Probes.ActualPreparedJointPair
import Probes.ActualUniformPreparedPairStepAllIndex
import Probes.ActualSmoothedPreparedPairConclusion
import Smoothing.ParameterRound2StageNumericProfiles
import Smoothing.ParameterRound2SmoothedOriginalPreparedSupply
import Smoothing.ParameterRound2IdentityPreparedCanonicalSupply
import Smoothing.ParameterRound2OriginalSmoothingStageData
import Smoothing.ParameterRound2IdentityParameterJets
import Smoothing.ParameterRound2ActualFinalRawProfiles
import Smoothing.ParameterRound2MeanRawPreparedCanonicalSupply
import Smoothing.ParameterRound2IdentityRefinementSamples
import Smoothing.ParameterRound2IdentityRawCosts
/-! Original C0 closeness constructs a common genuine positive neighborhood
for a finite list of actual native tensors. The same actual original primary
family, restricted to this one neighborhood, then supplies every mean
primitive for every input. No computed mean/source/output estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle IsManifold MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators TensorProduct Classical
namespace GlobalEmbedding.Continuation

universe uM uPrimary uSecondary
variable {m d N : ℕ} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)

local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance meanPrimitiveSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance meanPrimitiveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

private local instance meanPrimitiveGeometryFirstNormed : NormedAddCommGroup (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFirstSpace : NormedSpace ℝ (Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianNormed : NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryHessianSpace : NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
private local instance meanPrimitiveGeometryT0Normed : NormedAddCommGroup (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveGeometryT0Space : NormedSpace ℝ (Es →L[ℝ] Tdata) := inferInstance
private local instance meanPrimitiveCdataNormed : NormedAddCommGroup (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCdataSpace : NormedSpace ℝ (Fin (m+1) → ℂ) := inferInstance
private local instance meanPrimitiveCjetNormed : NormedAddCommGroup (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCjetSpace : NormedSpace ℝ (Es →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCANormed : NormedAddCommGroup
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCASpace : NormedSpace ℝ
    ((Es →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ContinuousLinearMap.toNormedSpace
private local instance meanPrimitiveCBNormed : NormedAddCommGroup
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
private local instance meanPrimitiveCBSpace : NormedSpace ℝ
    ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := ContinuousLinearMap.toNormedSpace



private local instance finiteArgumentLinearNormed : NormedAddCommGroup ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance finiteArgumentLinearSpace : NormedSpace ℝ ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance finiteArgumentBilinearNormed : NormedAddCommGroup
    ((Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] (Fin ((m+1)*(m+1)) → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup


local instance actualNativeJointPairChartedSpace : ChartedSpace (Ep × Es) (Ep × M) :=
  prodChartedSpace Ep Ep Es M
local instance actualNativeJointPairIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (Ep × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) Ep M
local notation "D" => Es

def ActualSmoothedPreparedJointPairConclusion
    {Β : Type uPrimary} {SubSecondary : Type uSecondary} [Fintype Β] [Fintype SubSecondary]
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ)
    (smoothingRadius : ℝ) (hSmoothingRadius : 0 < smoothingRadius) (q : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : ParameterRound2OriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp smoothingRadius hSmoothingRadius q budget reference givenPacket)
    (Rsub Lprimary Rsecondary : ℕ) (Brest Mrest Kcut Tfixed Tinv Tobs : ℕ → ℝ)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ))
    (W0 Vprep : Set (Ep × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0))
    (H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0) (radius ell : ℝ)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Fin Data.primaryCount) (Β := Β) F)
    (epsilon0 : ℝ) (C : ℕ → ℝ)
    (hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 // p 0 (K-H) < radius},
      incrementsGlobalPrimaryMeanError F hF g0 K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0) : Prop :=
    let hzero := fun p x => inducedMetric (I := 𝓙) (fun y => stage.referenceMap (p,y)) x
    let Hold := fun p x => (stage.delta^2)⁻¹ • (stage.metric p x-inducedMetric (I := 𝓙) (fun y => stage.oldMap (p,y)) x)
    ∀ epsilon, 0 < epsilon → epsilon < epsilon0 → stage.delta ≤ epsilon*ell →
    let Top := parameterRound2_actualGermMeanReserveOperator Data.atlas Data.parameterChart S W0 p H radius ell
      F hF g0 q hsm
    let K := fun i : ℕ => (meanReserveStep (p 0) H radius (Top epsilon))^[i] H
    (∀ i ≤ q, p 0 (K i-H) ≤ radius/2) ∧
    ∃ Gdomain : Set (Ep × M), ∃ hGdomain : IsOpen Gdomain,
    Gdomain ⊆ W0 ∧ Gdomain ⊆ Vprep ∧
    (∀ i, MapsTo (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) (S i) Gdomain) ∧
    let gG := parameterRound2_restrictPrimaryFamily F g0 Gdomain hGdomain
    let NativeSamples := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
      parameterRound2_meanParameterMap (m := m) (Data.parameterChart i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
    ∀ (choice : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → ActualOriginalSecondaryChoice Ep M m),
    let choiceG := fun r a => (choice r a).restrictOpen Gdomain hGdomain
    let U := actualOriginalIncrementMap F hF gG (K q).val (q+2) (epsilon*ell) stage.delta choiceG
    ∀ (j : ℕ)
    (geom : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q j) (j+1) ell (Mrest j) Vprep)
    (hCoordinate : ∀ r a, (geom r a).c = (choice r a).c)
    (hChart : ∀ r a, (geom r a).chart = (choice r a).chart)
    (hPhase : ∀ r a, (geom r a).phase = actualOriginalSecondaryPhase F gG r.val)
    (hHost : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,Es) ∞ (choice r a).host (choice r a).host.source)
    (hHostInv : ∀ r a, ContMDiffOn 𝓘(ℝ,Es) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
    (hHostSource : ∀ r a, (geom r a).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
    (hSupport : ∀ r a, tsupport (fun y : Vprep => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2)) ⊆ Subtype.val ⁻¹' (geom r a).support)
    (hPair : ∀ r a, (geom r a).support ⊆ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2))
    (hPartition : ∀ r : ActualSecondarySignedRecord (Fin Data.primaryCount), ∀ y,
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
    (hostIndex : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → (Fin Data.atlas.count × Fin Data.parameterCount))
    (hHostIndex : ∀ r a, (choice r a).host = Data.atlas.chart (hostIndex r a).1)
    (hNativeSamples : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geom r a).chart).symm '' (geom r a).sample ⊆ NativeSamples (hostIndex r a))
    (primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF gG)
    (hOriginal : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) Gdomain)
    (hChartInv : ∀ r a,
      letI : ChartedSpace X X := chartedSpaceSelf X
      ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (geom r a).chart.symm (geom r a).chart.target)
    (hObserverNativeSamples : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹' (geom r a).support →
      (geom r a).chart (z.1,(Data.atlas.chart i.1).symm z.2) ∈ (geom r a).sample)
    (hObserverJets : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹' (geom r a).support →
      ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((geom r a).chart ∘ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2))) z‖ ≤ Tobs k)
    (hObserverCount : ∀ i (r : ActualSecondarySignedRecord (Fin Data.primaryCount)), ∀ z ∈ NativeSamples i,
      (Finset.univ.filter (fun a => (z.1,(Data.atlas.chart i.1).symm z.2) ∈ (geom r a).support)).card ≤ Rsecondary),
    ∀ (geomHigher : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → ActualSecondaryRawGeometry F hF (actualSecondarySolveOrder q (j+1)) ((j+1)+1) ell (Mrest (j+1)) Vprep)
    (hCoordinateHigher : ∀ r a, (geomHigher r a).c = (choice r a).c)
    (hChartHigher : ∀ r a, (geomHigher r a).chart = (choice r a).chart)
    (hPhaseHigher : ∀ r a, (geomHigher r a).phase = actualOriginalSecondaryPhase F gG r.val)
    (hHostHigher : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,Es) ∞ (choice r a).host (choice r a).host.source)
    (hHostInvHigher : ∀ r a, ContMDiffOn 𝓘(ℝ,Es) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target)
    (hHostSourceHigher : ∀ r a, (geomHigher r a).chart.source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source)
    (hSupportHigher : ∀ r a, tsupport (fun y : Vprep => (choice r a).cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
        incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2)) ⊆ Subtype.val ⁻¹' (geomHigher r a).support)
    (hPairHigher : ∀ r a, (geomHigher r a).support ⊆ incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.1) ∩
      incrementsGlobalRelativeSupport Vprep (gG.cutoff r.val.1.2))
    (hPartitionHigher : ∀ r : ActualSecondarySignedRecord (Fin Data.primaryCount), ∀ y,
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
    (hostIndexHigher : ActualSecondarySignedRecord (Fin Data.primaryCount) → SubSecondary → (Fin Data.atlas.count × Fin Data.parameterCount))
    (hHostIndexHigher : ∀ r a, (choice r a).host = Data.atlas.chart (hostIndexHigher r a).1)
    (hNativeSamplesHigher : ∀ r a,
      let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
      (b.symm.trans (geomHigher r a).chart).symm '' (geomHigher r a).sample ⊆ NativeSamples (hostIndexHigher r a))
    (primaryGeometryHigher : ActualOriginalPrimaryPhysicalGeometry F hF gG)
    (hOriginalHigher : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (fun y : Ep × M => F y.1 y.2) Gdomain)
    (hChartInvHigher : ∀ r a,
      letI : ChartedSpace X X := chartedSpaceSelf X
      ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ (geomHigher r a).chart.symm (geomHigher r a).chart.target)
    (hObserverNativeSamplesHigher : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹' (geomHigher r a).support →
      (geomHigher r a).chart (z.1,(Data.atlas.chart i.1).symm z.2) ∈ (geomHigher r a).sample)
    (hObserverJetsHigher : ∀ i r a z, z ∈ NativeSamples i ∩ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2)) ⁻¹' (geomHigher r a).support →
      ∀ k, 1 ≤ k → k ≤ (j+1)+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
        ((geomHigher r a).chart ∘ (fun z : X => (z.1,(Data.atlas.chart i.1).symm z.2))) z‖ ≤ Tobs k)
    (hObserverCountHigher : ∀ i (r : ActualSecondarySignedRecord (Fin Data.primaryCount)), ∀ z ∈ NativeSamples i,
      (Finset.univ.filter (fun a => (z.1,(Data.atlas.chart i.1).symm z.2) ∈ (geomHigher r a).support)).card ≤ Rsecondary),
    let Hnext := fun p x => (stage.deltaNext^2)⁻¹ • (stage.metric p x-inducedMetric (I := 𝓙) (fun y => stage.oldMap (p,y)+U (p,y)) x)
    let O := incrementsOriginalDifferentiation Data.atlas Data.parameterChart
    let nextPair := parameterLocalOriginalTotalPairWeighted Data.atlas stage.parameterFamily (fun z => stage.oldMap z+U z) Hnext j (epsilon*ell) S
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U Gdomain ∧
    (∀ i, ∃ V0 : Set (Fin (m+1+d) → ℝ), IsOpen V0 ∧ S i ⊆ V0 ∧ V0 ⊆ O i ∧
      ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (fun z => stage.oldMap z+U z) i) V0 ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Hnext i) V0) ∧
    nextPair ≠ ⊤ ∧
    ∀ k s : ℕ, 10 ≤ k → s ≤ k+1 → q = 40*(k+1) →
      ell = stage.t^(11/10 : ℝ) → stage.delta = stage.t^k → epsilon*ell = stage.t^(6/5 : ℝ) →
      stage.deltaNext = (stage.t^(6/5 : ℝ))^s →
    let inherited := (parameterLocalOriginalTotalPairWeighted Data.atlas stage.parameterFamily stage.oldMap Hold j stage.t
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart stage.Omega stage.Q univ)).toReal
    nextPair.toReal ≤
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart stage.oldMap) O S).toReal+
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart hzero) O S).toReal+
      (1+j*(paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart hzero) O S).toReal+
        2*C j*(1+budget))*stage.t^(1/5 : ℝ)*(1+inherited)


def ActualPreparedJointPairFamily
    (B0 : ℕ → ℝ) (rho : ℝ) (q Rsub Lprimary Rsecondary : ℕ) (reserve : ℝ)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut T Tinv Tobs TP : ℕ → ℝ)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (C : ℕ → ℝ) (epsilon0 : ℝ) : Prop :=
    ∀
      (Label : Type) (SubPrimary : Type uPrimary) (SubSecondary : Type uSecondary)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary] (c : ℕ)
      (A : BufferedAtlas M D) (B : TensorBufferedChartFamily (Fin c) Ep Ep)
      (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep) (ip : Fin c)
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
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := ℝ) A B.chart S W Vprep p H rho q Rsub Lprimary reserve
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
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ U Gdomain ∧
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


theorem actual_prepared_joint_pair_stage_apply
    (B0 : ℕ → ℝ) (rho : ℝ) (q Rsub Lprimary Rsecondary : ℕ) (reserve : ℝ)
    (Bmean : ℕ → ℝ → ℝ) (Mmean Dinput Brest Mrest Kcut T Tinv Tobs TP : ℕ → ℝ)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (C : ℕ → ℝ) (epsilon0 : ℝ)
    (hFamily : ActualPreparedJointPairFamily.{uM,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M)
      B0 rho q Rsub Lprimary Rsecondary reserve Bmean Mmean Dinput Brest Mrest Kcut T Tinv Tobs TP
      BS0 TS0 BP0 TP0 Ds Dp radius hradius C epsilon0)
    (Β : Type uPrimary) (SubSecondary : Type uSecondary) [Fintype Β] [Fintype SubSecondary]
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep) (ip : Fin Data.parameterCount)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : ParameterRound2OriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q budget reference givenPacket)
    (hDelta : 0 < stage.delta) (hNext : stage.deltaNext ≠ 0)
    (S : Fin Data.atlas.count × Fin Data.parameterCount → Set (Fin (m+1+d) → ℝ)) (W Vprep : Set (Ep × M))
    (hVprep : IsOpen Vprep) (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart i)
    (hSinner : ∀ i, S i ⊆ tensorLocalOriginalInner Data.atlas stage.parameterFamily Data.parameterSet i)
    (H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W)
    (hH : H.val = Data.H) :
    let ell := stage.ell
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W hS hSO ell
    (∀ s, p s H ≤ B0 s) →
    (∀ v : Fin Data.atlas.count × Fin Data.parameterCount, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S v → ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (Data.parameterChart v.2)) z‖ ≤ TP k) → ∀
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g0 : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Fin Data.primaryCount) (Β := Β) F),
    ParameterRound2MeanRawPreparedCanonicalSupply (Tr := ℝ) Data.atlas Data.parameterChart S W Vprep p H rho
      q Rsub Lprimary reserve Bmean Mmean Dinput T F hF g0 Data.primaryDomain ell →
    (∀ z ∈ W, (fun x => F z.1 x) = (fun x => Data.F (z.1,x))) →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W // p 0 (K-H) < rho},
      incrementsGlobalPrimaryMeanError F hF g0 K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W,
    ActualSmoothedPreparedJointPairConclusion (SubSecondary := SubSecondary) Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q
      budget reference givenPacket stage Rsub Lprimary Rsecondary Brest Mrest Kcut T Tinv Tobs
      S W Vprep p H rho ell F hF g0 epsilon0 C hsm := by
  intro ell p hHbudget hParam F hF g0 hStrong hBackground
  have hB : ∀ i, Data.parameterChart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep := by
    simpa only [stage.chart_eq] using stage.parameter_smooth
  have hmA := hFamily (Fin Data.primaryCount) Β SubSecondary Data.parameterCount
    Data.atlas stage.parameterFamily stage.atlas_smooth stage.parameter_smooth ip
  rw [stage.chart_eq] at hmA
  have hstarReg : ∀ v, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart stage.metric v)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart v) := by
    simpa only [stage.chart_eq] using stage.metric_smooth
  have h0Reg := parameterRound2_inducedMetric_originalCoordinates_contDiffOn
    Data.atlas Data.parameterChart stage.atlas_smooth hB stage.referenceMap stage.referenceMap_smooth
  have htarget := hH.trans stage.target_eq
  have hBeforeTarget := hmA S W Vprep hVprep hS hSO ell stage.ell_pos
    (stage.ell_le_t.trans stage.t_le_one) H hHbudget hParam Data.parameterSet
    stage.sourcePreparation stage.parameterPreparation stage.buffer stage.Omega stage.Q
    stage.source_compact stage.parameter_compact stage.source_target (by simpa only [stage.chart_eq] using stage.parameter_target)
    stage.source_sampling stage.parameter_sampling hSinner stage.t stage.ell_le_t stage.t_le_one
    stage.oldMap stage.oldMap_smooth stage.metric
    (fun p x => inducedMetric (I := 𝓙) (fun y => stage.referenceMap (p,y)) x)
    hstarReg h0Reg stage.delta stage.deltaNext hDelta hNext budget (by simpa only [stage.chart_eq] using stage.old_pair_budget)
  have hAfterTarget := hBeforeTarget htarget
  obtain ⟨hsm,hcomplete⟩ := hAfterTarget F hF g0 Data.primaryDomain hStrong
  refine ⟨hsm,?_⟩
  unfold ActualSmoothedPreparedJointPairConclusion
  intro hzero Hold epsilon he he0lt hdeltatau Top K
  obtain ⟨hreserve,Gdomain,hGdomain,hGW,hGP,hSG,hout⟩ := hcomplete epsilon he he0lt hdeltatau
  refine ⟨hreserve,Gdomain,hGdomain,hGW,hGP,hSG,?_⟩
  intro gG NativeSamples
  have hb : ∀ z ∈ Gdomain, (fun x => F z.1 x) = (fun x => Data.F (z.1,x)) := fun z hz => hBackground z (hGW hz)
  rw [stage.map_eq] at hb
  exact hout hb


def ActualUniformSmoothedOriginalJointPairStatement
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (smoothingRadius : ℝ) (hSmoothingRadius : 0 < smoothingRadius) (q : ℕ) (hq : 1 ≤ q)
    (Cmap : ℕ → ℝ) (hCmap : ∀ j, 0 ≤ Cmap j)
    (Ctarget : ℕ → ℝ) (hCtarget : ∀ j, 0 ≤ Ctarget j)
    (Rsecondary : ℕ) (Msecondary Kcut Tobs : ℕ → ℝ)
    (hMsecondary : ∀ j, 0 ≤ Msecondary j) (hKcut : ∀ j, 0 ≤ Kcut j)
    (hTobs : ∀ j, 0 ≤ Tobs j) : Prop := ∀
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (hbudget : 0 ≤ budget) (hreference : ∀ j, 0 ≤ reference j)
    (c cT Bnative rho : ℝ) (hrho : 0 < rho) (hcT : 0 < cT) (hBnative : 0 < Bnative)
    (Rsub Lprimary : ℕ) (Tinv Forward Meta : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hForward : ∀ k, 0 ≤ Forward k) (hMeta : ∀ k, 0 ≤ Meta k),
    let B0 := fun j => Ctarget j*budget+(j+1)*reference j
    let Packet := fun j => max (Cmap j*budget) (max (B0 j) (givenPacket j))
    let ML := Packet 0
    let hPacket0 := fun j => (mul_nonneg (hCmap j) hbudget).trans (le_max_left _ (max (B0 j) (givenPacket j)))
    let radius := rho/(2*(‖actualOriginalCoefficientFunctional (m+1)‖*ML+1))
    let Bnd := fun s R => parameterRound2_identityRawBnd m d N (s+(q+4)) (Packet (s+(q+4)))
      c cT Bnative (Meta (s+(q+4))) R Tinv
    let Mg := fun s => parameterRound2_identityRawMg m d N (s+(q+4)) (Packet (s+(q+4))) c cT Bnative Tinv
    let Dinput := fun s => parameterRound2_identityRawDinput m d (s+(q+4)) (Packet (s+(q+4))) Tinv
    let Tfixed := parameterRound2_identityRawTransition m d Packet Forward
    let hBnd := fun s R => parameterRound2_identityRawBnd_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT Bnative (Meta (s+(q+4))) R (hPacket0 _) Tinv
    let hMg := fun s => parameterRound2_identityRawMg_nonneg m d N (s+(q+4))
      (Packet (s+(q+4))) c cT Bnative Tinv
    let hDinput := fun s => parameterRound2_identityRawDinput_nonneg m d (s+(q+4))
      (Packet (s+(q+4))) (hPacket0 _) Tinv
    let hT := parameterRound2_identityRawTransition_nonneg m d Packet Forward hPacket0 hForward
    let Csize := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,0,0,uPrimary}
      (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) (rho/4) (Bnd s R) (Mg s)
      (div_pos hrho (by norm_num)) (hBnd s R) (hMg s) Tfixed (fun _ => 1) hT (fun _ => zero_le_one)
    let Rq := parameterRound2_uniformMeanProfile B0 Csize (q+4) q
    let Brest := fun j => Bnd (actualSecondarySolveOrder q j) (Rq (actualSecondaryInputOrder q j))
    let Mrest := fun j => max (Mg (actualSecondarySolveOrder q j)) (Msecondary j)
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ ∀
    (Β : Type uPrimary) (SubSecondary : Type uSecondary) [Fintype Β] [Fintype SubSecondary], ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (stage : ParameterRound2OriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp smoothingRadius hSmoothingRadius
      q budget reference givenPacket),
    ∀ (hDelta : 0 < stage.delta) (hNext : stage.deltaNext ≠ 0), ∀
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep)
    (hOne : Data.parameterCount = 1)
    (host : Fin Data.primaryCount → Β → Fin Data.atlas.count)
    (b : Fin Data.primaryCount → Β → OpenPartialHomeomorph X X)
    (e : Fin Data.primaryCount → Β → Ep → OpenPartialHomeomorph M Es)
    (hdata : ∀ nu beta, ActualOriginalHostSliceData (Data.atlas.chart (host nu beta)) (b nu beta)
      (fun z : Ep × M => Data.phase nu ((Data.parameterChart i.2).symm z.1,z.2)) (e nu beta))
    (eta : Fin Data.primaryCount → Β → Ep × M → ℝ)
    (hactive : ∀ nu beta w,
      w ∈ (actualHostAdaptedChart (Data.atlas.chart (host nu beta)) (b nu beta)).source →
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hsource : ∀ nu beta, (b nu beta).source ⊆ actualOriginalNativeOpen Data (host nu beta,i.2))
    (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (hnative : ∀ nu beta z, z ∈ (b nu beta).source → ‖fderiv ℝ (b nu beta) z‖ ≤ Bnative)
    (hTreserve : ∀ nu beta z, z ∈ (b nu beta).target → ∀ v : Tdata, cT*‖v‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame
        (actualOriginalOpenParameterSlice Data i z.1)
        (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1)
        (e nu beta z.1).symm z.2 v‖^2)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecompOriginal : IncrementsOriginalQualitativeDecompositionInputs Data)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (Vprep : Set (Ep × M)) (hVprep : IsOpen Vprep)
    (hKVprep : Data.parameterSet ×ˢ (univ : Set M) ⊆ Vprep),
    let ell := stage.ell
    let hS := stage.samples_compact
    let F := actualOriginalOpenParameterSlice Data i
    let hF := actualOriginalOpenParameterSlice_contMDiff Data hd hs i
    let g0 := actualOriginalPrimaryFamily Data hd hs hn i host b e hdata eta hactive
    ParameterRound2IdentityRefinementSamples Data i.2 F g0 host b Vprep ell Tinv Forward Meta Rsub Lprimary →
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W0 := incrementsOriginalParameterRegion Data
    let p := parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W0 hS
      (fun _ _ hy => hy.1) ell
    ∃ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
    H.val = Data.H ∧ (∀ s, p s H ≤ B0 s) ∧
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0 // p 0 (K-H) < radius},
      incrementsGlobalPrimaryMeanError F hF g0 K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W0,
    ActualSmoothedPreparedJointPairConclusion (SubSecondary := SubSecondary) Data BS0 TS0 BP0 TP0 Ds Dp smoothingRadius hSmoothingRadius q
      budget reference givenPacket stage Rsub Lprimary Rsecondary Brest Mrest Kcut Tfixed Tinv Tobs
      S W0 Vprep p H radius ell F hF g0 epsilon0 C hsm


theorem exists_uniform_actual_smoothed_original_joint_pair_repair
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (smoothingRadius : ℝ) (hSmoothingRadius : 0 < smoothingRadius) (q : ℕ) (hq : 1 ≤ q)
    (Rsecondary : ℕ) (Msecondary Kcut Tobs : ℕ → ℝ)
    (hMsecondary : ∀ j, 0 ≤ Msecondary j) (hKcut : ∀ j, 0 ≤ Kcut j)
    (hTobs : ∀ j, 0 ≤ Tobs j) :
    ∃ Cmap : ℕ → ℝ, ∃ hCmap : ∀ j, 0 ≤ Cmap j,
    ∃ Ctarget : ℕ → ℝ, ∃ hCtarget : ∀ j, 0 ≤ Ctarget j,
    ActualUniformSmoothedOriginalJointPairStatement.{uM,uPrimary,uSecondary}
      (m := m) (d := d) (N := N) (M := M)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp smoothingRadius hSmoothingRadius q hq
      Cmap hCmap Ctarget hCtarget Rsecondary Msecondary Kcut Tobs hMsecondary hKcut hTobs := by
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,hstageProducer⟩ :=
    exists_uniform_parameterRound2_original_stage_data_profiles
      (n := m+1) (d := d) (N := N) (M := M) (P := Ep)
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp smoothingRadius hSmoothingRadius q
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,?_⟩
  unfold ActualUniformSmoothedOriginalJointPairStatement
  intro budget reference givenPacket hbudget hreference c cT Bnative rho hrho hcT hBnative
    Rsub Lprimary Tinv Forward Meta hTinv hForward hMeta B0 Packet ML hPacket0 radius Bnd Mg Dinput Tfixed
    hBnd hMg hDinput hT Csize Rq Brest Mrest
  have hradius : 0 < radius := by
    have hp0 := hPacket0 0
    dsimp only [radius,ML]
    positivity
  have hm := actual_original_uniform_prepared_joint_pair_repair_step.{uM,0,0,uPrimary,uSecondary}
    (m := m) (d := d) (N := N) (M := M) (Tr := ℝ)
    B0 radius hradius q Rsub Lprimary Rsecondary hq (rho/4) (div_pos hrho (by norm_num))
    Bnd Mg Dinput Msecondary Kcut hBnd hMg hDinput hMsecondary hKcut
    Tfixed Tinv Tobs (fun _ => 1) hT hTinv hTobs (fun _ => zero_le_one)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp smoothingRadius hSmoothingRadius
  unfold ActualUniformPreparedJointPairStatement at hm
  obtain ⟨C,hC,epsilon0,he0,he01,hm⟩ := hm
  change ActualPreparedJointPairFamily.{uM,uPrimary,uSecondary} (m := m) (d := d) (N := N) (M := M) B0 radius q Rsub Lprimary Rsecondary (rho/4)
    Bnd Mg Dinput Brest Mrest Kcut Tfixed Tinv Tobs (fun _ => 1)
    BS0 TS0 BP0 TP0 Ds Dp smoothingRadius hSmoothingRadius C epsilon0 at hm
  refine ⟨C,hC,epsilon0,he0,he01,?_⟩
  intro Β SubSecondary _ _ Data stage hDelta hNext hd hs hn hp i hId hOne host b e hdata eta hactive hImm hsource
    hEll hnative hTreserve hLinear hDecompOriginal hReserve Vprep hVprep hKVprep
    ell hS F hF g0 hRef S W0 p
  obtain ⟨H,hH,hHbudget,hProfiles⟩ := hstageProducer Data budget reference givenPacket stage
  have hfinite : incrementsOriginalCoreInputProfile Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hProfiles 0).1 (actualOriginalGivenInputProfile_core_le Data 0 ell)
  have hProfile : incrementsOriginalInputProfileWithLinear Data 0 ell ≠ ⊤ :=
    ne_top_of_le_ne_top (hProfiles 0).1 (actualOriginalGivenInputProfile_linear_le Data 0 ell)
  have hML : (incrementsOriginalInputProfileWithLinear Data 0 ell).toReal ≤ ML :=
    (ENNReal.toReal_mono (hProfiles 0).1 (actualOriginalGivenInputProfile_linear_le Data 0 ell)).trans (hProfiles 0).2
  have hGiven : ∀ n, actualOriginalGivenInputProfile Data n ell ≠ ⊤ := fun n => (hProfiles n).1
  have hPacket : ∀ n, (actualOriginalGivenInputProfile Data n ell).toReal ≤ Packet n := fun n => (hProfiles n).2
  have hSupply := parameterRound2_identity_original_prepared_canonical_supply Data hd hs hn hp i hId hOne
    host b e hdata eta hactive hImm hsource ell c cT Bnative stage.ell_pos (stage.ell_le_t.trans stage.t_le_one)
    hEll hcT hBnative hfinite hnative hTreserve hLinear hDecompOriginal rho hReserve Vprep hVprep hKVprep
    hS ML hProfile hML q Rsub Lprimary Packet Tinv Forward Meta hTinv hForward hMeta hGiven hPacket hRef
  have hStrong := hSupply.2 H hH
  have hParam : ∀ v : Fin Data.atlas.count × Fin Data.parameterCount, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S v → ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (Data.parameterChart v.2)) z‖ ≤ 1 := by
    intro v z hz k hk
    have hip : v.2 = i.2 := by
      letI : Subsingleton (Fin Data.parameterCount) := by rw [hOne]; infer_instance
      exact Subsingleton.elim _ _
    rw [hip,hId]
    exact parameterRound2_identity_parameter_map_jets m d ell k hk z
  have hBackground : ∀ z ∈ W0, (fun x => F z.1 x) = (fun x => Data.F (z.1,x)) := by
    intro z hz
    have hp : (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen := by
      simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hz.1
    have heq := actualOriginalOpenParameterSlice_eq Data i z.1 hp
    funext x
    simpa only [actualOriginalParameterSlice,hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using congrFun heq x
  have hout := actual_prepared_joint_pair_stage_apply
    B0 radius q Rsub Lprimary Rsecondary (rho/4) Bnd Mg Dinput Brest Mrest Kcut Tfixed Tinv Tobs (fun _ => 1)
    BS0 TS0 BP0 TP0 Ds Dp smoothingRadius hSmoothingRadius C epsilon0 hm
    Β SubSecondary Data i.2 budget reference givenPacket stage hDelta hNext S W0 Vprep hVprep hS
    (fun _ _ hy => hy.1) stage.samples_inner H hH hHbudget hParam F hF g0 hStrong hBackground
  exact ⟨H,hH,hHbudget,hout⟩

#print axioms actual_prepared_joint_pair_stage_apply
#print axioms exists_uniform_actual_smoothed_original_joint_pair_repair
end GlobalEmbedding.Continuation
