import Probes.ActualUniformPreparedPairStep
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
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter Bundle
open scoped ContDiff ENNReal Topology BigOperators TensorProduct Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local notation "𝓙" => 𝓘(ℝ,Es)
variable {Β SubSecondary : Type*} [Fintype Β] [Fintype SubSecondary]

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

def ActualSmoothedPreparedPairConclusion
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

end GlobalEmbedding.Continuation
