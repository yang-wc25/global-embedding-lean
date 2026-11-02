import OriginalCollars.OriginalParentPrimitiveExistence
import OriginalCollars.FiniteNativePrimitiveFamily

/-! The original fixed phase family and physical compact parent cutoffs
manufacture one common primitive budget. No chart solver, adapted packet,
uniform norm comparison, or output supplier is assumed. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem original_common_native_primitive_regions_exist
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    ∃ (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ),
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<coordinateBound ∧ 0<kernel ∧ 0<lower ∧ 0≤nativeTwo ∧
      (∀j, 0≤Phase j) ∧ Phase 1≤Mb ∧ buffer*Phase 2≤Mb ∧
      ∀ (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
        (i : Fin Data.atlas.count × Fin Data.parameterCount),
      Nonempty (NativePrimitiveSignedRegion Data i r
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
        mu R buffer coordinateBound kernel lower nativeTwo Phase) := by
  classical
  let Index := ActualSecondarySignedRecord (Fin Data.primaryCount) ×
    (Fin Data.atlas.count × Fin Data.parameterCount)
  letI : Fintype (ActualSecondarySignedRecord (Fin Data.primaryCount)) := by
    unfold ActualSecondarySignedRecord
    infer_instance
  letI : Fintype Index := inferInstance
  obtain ⟨mu,Mb,R,buffer,coordinateBound,kernel,lower,nativeTwo,Phase,
    hMu,hMb,hR,hBuffer,hCoordinate,hKernel,hLower,hTwo,hPhase,hOne,hSecond,regions⟩ :=
    finite_native_primitive_regions (ι := Index) Data (fun a => a.2) (fun a => a.1)
      (fun a => (Data.parameterChart a.2.2).target ×ˢ (univ : Set M))
      (fun a => round3ParameterNativeParent (Data.parameterChart a.2.2) (theta a.2))
      (fun a => original_parent_native_primitive_regions_exist Data hd hs hp hImm
        theta hCompact hSmooth hSupport a.1 a.2)
  exact ⟨mu,Mb,R,buffer,coordinateBound,kernel,lower,nativeTwo,Phase,
    hMu,hMb,hR,hBuffer,hCoordinate,hKernel,hLower,hTwo,hPhase,hOne,hSecond,fun r i => regions (r,i)⟩
end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_common_native_primitive_regions_exist
