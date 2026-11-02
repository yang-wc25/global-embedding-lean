import NormalPolar.PassiveOriginalData
import NormalPolar.PassiveOriginalCoordinateNorm

/-!
# Literal native coordinate identities for passive original data

These statements identify the actual original map, tensor, cutoff and phase
covector coordinates after adding a genuine parameter manifold. They keep
the same source atlas and its native tangent vectors. The coordinate
projection uses the original Pi norm and will feed the constant-one budget
comparison in `PassiveOriginalCoordinateNorm`.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d N : ℕ} {M S P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P]

theorem passiveOriginal_sourcePoint (y : Fin (n+d) → ℝ) :
    incrementsOriginalSourcePoint (n := n) (d := 0) (passiveOriginalSourceProjection y) =
      incrementsOriginalSourcePoint (n := n) (d := d) y := rfl

theorem passiveOriginal_sourceVector
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (i : Fin A.count) (y : Fin (n+d) → ℝ) (r : Fin n) :
    incrementsOriginalSourceVector (d := 0) A i (passiveOriginalSourceProjection y) r =
      incrementsOriginalSourceVector (d := d) A i y r := rfl

variable (s₀ : S) (seed : IncrementsOriginalNativeData n 0 N M S)
  (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
  (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
  (b₀ : Fin seed.parameterCount)

theorem passiveOriginal_mapCoordinates
    (f : S × M → EuclideanSpace ℝ (Fin N))
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalMapCoordinates seed.atlas B.chart (fun z => f (s₀,z.2)) i y =
    incrementsOriginalMapCoordinates seed.atlas seed.parameterChart f (i.1,b₀)
      (passiveOriginalSourceProjection y) := by
  unfold incrementsOriginalMapCoordinates incrementsOriginalJointPoint
  have hp : (seed.parameterChart b₀).symm
      (incrementsOriginalParameterPoint (passiveOriginalSourceProjection y)) = s₀ :=
    Subsingleton.elim _ _
  rw [hp,passiveOriginal_sourcePoint]

theorem passiveOriginal_tensorCoordinates
    (T : (s : S) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x))
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalTensorCoordinates seed.atlas B.chart (fun _ => T s₀) i y =
    incrementsOriginalTensorCoordinates seed.atlas seed.parameterChart T (i.1,b₀)
      (passiveOriginalSourceProjection y) := by
  unfold incrementsOriginalTensorCoordinates incrementsOriginalJointPoint
  have hp : (seed.parameterChart b₀).symm
      (incrementsOriginalParameterPoint (passiveOriginalSourceProjection y)) = s₀ :=
    Subsingleton.elim _ _
  rw [hp,passiveOriginal_sourcePoint]
  rfl

theorem passiveOriginal_scalarCoordinates (f : S × M → ℝ)
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalScalarCoordinates (passiveOriginalData s₀ seed B Q)
      (fun z => f (s₀,z.2)) i y =
    incrementsOriginalScalarCoordinates seed f (i.1,b₀) (passiveOriginalSourceProjection y) := by
  unfold incrementsOriginalScalarCoordinates incrementsOriginalJointPoint
  have hp : (seed.parameterChart b₀).symm
      (incrementsOriginalParameterPoint (passiveOriginalSourceProjection y)) = s₀ :=
    Subsingleton.elim _ _
  rw [hp]
  rfl

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

theorem passiveOriginal_phaseCovectorCoordinates (l : Fin seed.primaryCount)
    (i : Fin seed.atlas.count × Fin B.count) (y : Fin (n+d) → ℝ) :
    incrementsOriginalPhaseCovectorCoordinates (passiveOriginalData s₀ seed B Q) l i y =
    incrementsOriginalPhaseCovectorCoordinates seed l (i.1,b₀) (passiveOriginalSourceProjection y) := by
  unfold incrementsOriginalPhaseCovectorCoordinates incrementsOriginalJointPoint
  have hp : (seed.parameterChart b₀).symm
      (incrementsOriginalParameterPoint (passiveOriginalSourceProjection y)) = s₀ :=
    Subsingleton.elim _ _
  rw [hp]
  rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_mapCoordinates
#print axioms GlobalEmbedding.Continuation.passiveOriginal_tensorCoordinates
#print axioms GlobalEmbedding.Continuation.passiveOriginal_phaseCovectorCoordinates
