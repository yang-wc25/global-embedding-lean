import OriginalCollars.OriginalPrimaryRegionExistence
import OriginalCollars.NativePrimitiveBudgetMonotonicity
import OriginalCollars.ProtectedRegionPrimaryGeometry

/-! The literal original primary phase family supplies its common low
geometry and common restriction reserve on the same construction regions.
The finite min/max operation has no multiplicative chart-count cost.
These witnesses depend on the fixed datum; class uniformity is separate. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open OriginalCollars SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance commonPrimaryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance commonPrimarySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)

theorem original_common_primary_geometry_exists
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    ∃ mu Mb R buffer kernel : ℝ,
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<kernel ∧
      ∃ geometry : OriginalCommonPrimaryGeometry Data theta mu Mb R buffer,
        OriginalRegionPrimaryKernelInputs Data geometry.region kernel := by
  classical
  let Index := Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount)
  have available (a : Index) :=
    original_parent_primary_regions_exist Data hd hs hp hImm theta hCompact hSmooth hSupport a.1 a.2
  choose mu Mb R buffer kernel O hMu hMb hR hBuffer hKernel hOpen hNative
    hRadius hBufferO hNoncritical hFirst hSecond hRestriction using available
  let mu' := finitePrimitiveLower mu
  let Mb' := finitePrimitiveUpper Mb + 1
  let R' := finitePrimitiveUpper R + 1
  let buffer' := finitePrimitiveLower buffer
  let kernel' := finitePrimitiveLower kernel
  have hMu' : 0 < mu' := finitePrimitiveLower_pos mu hMu
  have hMb' : 0 < Mb' := by dsimp [Mb']; linarith [finitePrimitiveUpper_nonneg Mb]
  have hR' : 0 < R' := by dsimp [R']; linarith [finitePrimitiveUpper_nonneg R]
  have hBuffer' : 0 < buffer' := finitePrimitiveLower_pos buffer hBuffer
  have hKernel' : 0 < kernel' := finitePrimitiveLower_pos kernel hKernel
  have hMbCommon (a : Index) : Mb a ≤ Mb' :=
    (le_finitePrimitiveUpper Mb a).trans (by dsimp [Mb']; linarith)
  have hRCommon (a : Index) : R a ≤ R' :=
    (le_finitePrimitiveUpper R a).trans (by dsimp [R']; linarith)
  let geometry : OriginalCommonPrimaryGeometry Data theta mu' Mb' R' buffer' := {
    mu_pos := hMu'
    Mb_nonneg := hMb'.le
    radius_pos := hR'
    buffer_pos := hBuffer'
    region := fun nu i => O (nu,i)
    open_region := fun nu i => hOpen (nu,i)
    native := fun nu i => hNative (nu,i)
    radius := fun nu i => (hRadius (nu,i)).trans (closedBall_subset_closedBall (hRCommon (nu,i)))
    buffered := fun nu i z hz =>
      (ball_subset_ball (finitePrimitiveLower_le buffer (nu,i))).trans (hBufferO (nu,i) z hz)
    noncritical := fun nu i z hz =>
      (finitePrimitiveLower_le mu (nu,i)).trans (hNoncritical (nu,i) z hz)
    first := fun nu i z hz => (hFirst (nu,i) z hz).trans (hMbCommon (nu,i))
    second := fun nu i z hz =>
      ((mul_le_mul_of_nonneg_right (finitePrimitiveLower_le buffer (nu,i)) (norm_nonneg _)).trans
        (hSecond (nu,i) z hz)).trans (hMbCommon (nu,i)) }
  refine ⟨mu',Mb',R',buffer',kernel',hMu',hMb',hR',hBuffer',hKernel',geometry,?_⟩
  refine ⟨?_⟩
  intro nu i z hz v
  exact (mul_le_mul_of_nonneg_right (finitePrimitiveLower_le kernel (nu,i)) (norm_nonneg v)).trans
    (hRestriction (nu,i) z hz v)
end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_common_primary_geometry_exists
