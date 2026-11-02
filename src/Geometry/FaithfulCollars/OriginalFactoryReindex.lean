import FaithfulCollars.OriginalChartReindex

/-!
# Pointwise identity of the original phase factory after index transport

The reference map and native tensor are the same physical objects.  The
factory uses only their literal source and parameter charts, so internal
compact carriers do not alter its values or original coordinate margin.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Bundle
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulCollars

def originalReferenceSeed {n d N pc : ℕ} {M P : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace P]
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (Omega : Fin A.count → Set (EuclideanSpace ℝ (Fin n)))
    (chart : Fin pc → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d)))
    (Q : Fin pc → Set (EuclideanSpace ℝ (Fin d))) (K U : Set P)
    (F0 : P × M → EuclideanSpace ℝ (Fin N)) : RepairOriginalReferenceSeed n d N M P where
  atlas := A
  sourceNormDomain := Omega
  parameterCount := pc
  parameterChart := chart
  parameterNormDomain := Q
  parameterSet := K
  parameterOpen := U
  F0 := F0

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IT" => 𝓘(ℝ,Es)

theorem repairFactoryField_cast
    (seed seed' : RepairOriginalReferenceSeed (m+1) d N M P)
    (hs : seed'.atlas.count = seed.atlas.count)
    (hp : seed'.parameterCount = seed.parameterCount)
    (hS : ∀ i, seed'.atlas.chart i = seed.atlas.chart (Fin.cast hs i))
    (hP : ∀ i, seed'.parameterChart i = seed.parameterChart (Fin.cast hp i))
    (hF : seed'.F0 = seed.F0)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (i : Fin seed'.atlas.count × Fin seed'.parameterCount) (z : Ep × Es) :
    repairReferenceFactoryField seed' T i z =
      repairReferenceFactoryField seed T (Fin.cast hs i.1, Fin.cast hp i.2) z := by
  apply Prod.ext
  · dsimp only [repairReferenceFactoryField]
    rw [hF, hP i.2, hS i.1]
  · dsimp only [repairReferenceFactoryField, round4OriginalNativeTensorCoordinates]
    rw [originalTensorCoordinates_cast seed.atlas seed'.atlas seed.parameterChart
      seed'.parameterChart hs hp hS hP T i]

variable [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem compactSetup_factory_original
    {pc : ℕ} (g : SourceCollarNovSetup (m+1) d M P)
    (A : BufferedAtlas M Es) (Omega : Fin A.count → Set Es)
    (chart : Fin pc → OpenPartialHomeomorph P Ep) (Q : Fin pc → Set Ep)
    (hs : g.source.count = A.count) (hp : g.parameter.count = pc)
    (hS : ∀ i, g.source.chart i = A.chart (Fin.cast hs i))
    (hP : ∀ i, g.parameter.chart i = chart (Fin.cast hp i))
    (F0 : P × M → EuclideanSpace ℝ (Fin N))
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (i : Fin g.source.count × Fin g.parameter.count) (z : Ep × Es) :
    repairReferenceFactoryField (g.seed F0) T i z =
      repairReferenceFactoryField (originalReferenceSeed A Omega chart Q univ univ F0)
        T (Fin.cast hs i.1, Fin.cast hp i.2) z :=
  repairFactoryField_cast (originalReferenceSeed A Omega chart Q univ univ F0)
    (g.seed F0) hs hp hS hP rfl T i z

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.repairFactoryField_cast
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.compactSetup_factory_original
