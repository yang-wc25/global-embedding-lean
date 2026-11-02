import OriginalCollars.OriginalNativePrimitiveExistence
import OriginalCollars.NativePrimitiveSecondaryPacket

/-! The actual physical original parent family supplies every native signed
primitive region. The parameter chart target remains unrestricted: only
the compact parent support must lie in the original parameter-open set.
The result is ready for finite common lower/upper budget aggregation. -/

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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓙

theorem original_parent_native_primitive_regions_exist
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : Fin Data.atlas.count × Fin Data.parameterCount → P × M → ℝ)
    (hCompact : ∀i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    ∀ (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
      (i : Fin Data.atlas.count × Fin Data.parameterCount),
    ∃ (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ),
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<coordinateBound ∧ 0<kernel ∧ 0<lower ∧ 0≤nativeTwo ∧
      (∀j, 0≤Phase j) ∧ Phase 1≤Mb ∧ buffer*Phase 2≤Mb ∧
      Nonempty (NativePrimitiveSignedRegion Data i r
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
        mu R buffer coordinateBound kernel lower nativeTwo Phase) := by
  intro r i
  let W := (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW : IsOpen W := (Data.parameterChart i.2).open_target.prod isOpen_univ
  have hPhysical : tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz=>⟨(hSupport i hz).1.1,mem_univ _⟩
  have hNative := round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) hPhysical
  have hNativeSupport : tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆
      W ∩ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hNative.2.2 hy
    have hh := hSupport i hz
    exact ⟨⟨(Data.parameterChart i.2).map_source hh.1.1,mem_univ _⟩,
      mem_univ _,Data.atlas.inner_subset i.1 hh.2⟩
  have hOriginal : ∀y∈tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)),
      ((Data.parameterChart i.2).symm y.1,y.2)∈incrementsOriginalParameterRegion Data := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hNative.2.2 hy
    have hh := hSupport i hz
    change ((Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1),z.2)∈_
    rw [(Data.parameterChart i.2).left_inv hh.1.1]
    exact ⟨hh.1.2,mem_univ _⟩
  have hInner : ∀y∈tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)),
      y.2∈Data.atlas.inner i.1 := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := hNative.2.2 hy
    exact (hSupport i hz).2
  exact original_native_primitive_signed_region_exists Data hd hs hp hImm i r W hW
    (fun z hz=>hz.1) _ hNative.2.1 hOriginal hNativeSupport hInner

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_parent_native_primitive_regions_exist
