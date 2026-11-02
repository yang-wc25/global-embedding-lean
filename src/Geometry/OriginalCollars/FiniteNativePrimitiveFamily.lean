import OriginalCollars.NativePrimitiveBudgetMonotonicity

/-! A finite original family has one actual primitive budget, chosen before
orders and scales. This is a fixed-data existence result. The maximum
operation does not supply a uniform bound across varying original data. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P ι : Type*} [Fintype ι]
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- All original hosts and signed interactions retain their literal domains,
centers, phases and functions when their numerical witnesses are combined. -/
theorem finite_native_primitive_regions
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (host : ι → Fin Data.atlas.count × Fin Data.parameterCount)
    (signed : ι → ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : ι → Set (Ep × M)) (theta : ι → Ep × M → ℝ)
    (available : ∀ a, ∃ (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ)
        (Phase : ℕ → ℝ),
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<coordinateBound ∧ 0<kernel ∧ 0<lower ∧ 0≤nativeTwo ∧
      (∀j, 0≤Phase j) ∧ Phase 1≤Mb ∧ buffer*Phase 2≤Mb ∧
      Nonempty (NativePrimitiveSignedRegion Data (host a) (signed a) (W a) (theta a)
        mu R buffer coordinateBound kernel lower nativeTwo Phase)) :
    ∃ (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ),
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<coordinateBound ∧ 0<kernel ∧ 0<lower ∧ 0≤nativeTwo ∧
      (∀j, 0≤Phase j) ∧ Phase 1≤Mb ∧ buffer*Phase 2≤Mb ∧
      ∀ a, Nonempty (NativePrimitiveSignedRegion Data (host a) (signed a) (W a) (theta a)
        mu R buffer coordinateBound kernel lower nativeTwo Phase) := by
  classical
  choose mu Mb R buffer coordinateBound kernel lower nativeTwo Phase
    hMu hMb hR hBuffer hCoordinate hKernel hLower hTwo hPhase hPhaseOne hPhaseTwo hRegion using available
  let mu' := finitePrimitiveLower mu
  let buffer' := finitePrimitiveLower buffer
  let kernel' := finitePrimitiveLower kernel
  let lower' := finitePrimitiveLower lower
  let R' := finitePrimitiveUpper R + 1
  let coordinate' := finitePrimitiveUpper coordinateBound + 1
  let two' := finitePrimitiveUpper nativeTwo
  let Phase' := fun j => finitePrimitiveUpper (fun a => Phase a j)
  let Mb' := 1 + Phase' 1 + buffer' * Phase' 2
  have hMu' : 0 < mu' := finitePrimitiveLower_pos mu hMu
  have hBuffer' : 0 < buffer' := finitePrimitiveLower_pos buffer hBuffer
  have hKernel' : 0 < kernel' := finitePrimitiveLower_pos kernel hKernel
  have hLower' : 0 < lower' := finitePrimitiveLower_pos lower hLower
  have hR' : 0 < R' := by dsimp [R']; linarith [finitePrimitiveUpper_nonneg R]
  have hCoordinate' : 0 < coordinate' := by
    dsimp [coordinate']; linarith [finitePrimitiveUpper_nonneg coordinateBound]
  have hTwo' : 0 ≤ two' := finitePrimitiveUpper_nonneg nativeTwo
  have hPhase' : ∀ j, 0 ≤ Phase' j := fun j => finitePrimitiveUpper_nonneg _
  have hProduct : 0 ≤ buffer' * Phase' 2 := mul_nonneg hBuffer'.le (hPhase' 2)
  have hMb' : 0 < Mb' := by dsimp [Mb']; linarith [hPhase' 1]
  have hOne' : Phase' 1 ≤ Mb' := by dsimp [Mb']; linarith
  have hSecond' : buffer' * Phase' 2 ≤ Mb' := by dsimp [Mb']; linarith [hPhase' 1]
  refine ⟨mu',Mb',R',buffer',coordinate',kernel',lower',two',Phase',
    hMu',hMb',hR',hBuffer',hCoordinate',hKernel',hLower',hTwo',hPhase',hOne',hSecond',?_⟩
  intro a
  let region := Classical.choice (hRegion a)
  apply Nonempty.intro
  exact region.weaken mu' R' buffer' coordinate' kernel' lower' two' Phase'
    (finitePrimitiveLower_le mu a)
    ((le_finitePrimitiveUpper R a).trans (by dsimp [R']; linarith))
    (finitePrimitiveLower_le buffer a)
    ((le_finitePrimitiveUpper coordinateBound a).trans (by dsimp [coordinate']; linarith))
    (finitePrimitiveLower_le kernel a) (finitePrimitiveLower_le lower a)
    (le_finitePrimitiveUpper nativeTwo a) (fun j => le_finitePrimitiveUpper (fun a => Phase a j) a)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.finite_native_primitive_regions
