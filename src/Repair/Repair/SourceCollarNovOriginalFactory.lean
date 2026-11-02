import Repair.SourceCollarNovBufferedFactory
import Repair.SourceCollarNovOriginalDomains

/-!
# Original source buffers supply the existing local-factory boundary

The public output uses exactly A, B.chart, Omega, Q and the original
paperAtlasCj norm.  Actual convex source balls are constructed internally
from the original buffers.  The original whole sampling domain is allowed
to be nonconvex; no atlas index, chart map, norm, cutoff radius, per-host
piece bound, normal radius or chart derivative profile is changed.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance novOriginalFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance novOriginalFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance novOriginalFactoryHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance novOriginalFactoryHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance novOriginalFactoryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance
private local instance novOriginalFactoryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) := inferInstance

/-- A literal view of the original charts and original norm sets. -/
def sourceCollarNovOriginalSeed
    (A : BufferedAtlas M D) (B : BufferedAtlas P Ep)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep) (F0 : P × M → V) :
    RepairOriginalReferenceSeed (m+1) d N M P where
  atlas := A
  sourceNormDomain := Omega
  parameterCount := B.count
  parameterChart := B.chart
  parameterNormDomain := Q
  parameterSet := univ
  parameterOpen := univ
  F0 := F0

/-- Actual source local-factory production from the original buffered atlases.
All geometric domain, carrier, sampling, boundedness and buffer obligations
are proved here; they are not inputs. Only the original fixed radius and
buffer budgets and original low analytic inputs occur. -/
theorem sourceCollarNov_original_local_factory
    (b : RepairReferenceFactoryBudget m d N)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A) (B : BufferedAtlas P Ep)
    (Omega : Fin A.count → Set D) (Q : Fin B.count → Set Ep)
    (hS : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (hP : ∀ i, bufferedSamplingCoordinates B i ⊆ Q i)
    (hRS : ∀ i x, x ∈ Omega i → ‖x‖ ≤ b.modelRadius)
    (hRP : ∀ i p, p ∈ Q i → ‖p‖ ≤ b.modelRadius)
    (hBS : b.buffer ≤ A.buffer) (hBP : b.buffer ≤ B.buffer)
    (F0 : P × M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (hCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart F0 i)
      (incrementsOriginalDifferentiation A B.chart i))
    (hC3 : paperAtlasCj 3 (incrementsOriginalMapCoordinates A B.chart F0)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal b.mapC3)
    (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hTensorCoords : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart Htensor i)
      (incrementsOriginalDifferentiation A B.chart i))
    (hC1 : paperAtlasCj 1 (incrementsOriginalTensorCoordinates A B.chart Htensor)
      (incrementsOriginalDifferentiation A B.chart)
      (incrementsOriginalEvaluation A B.chart Omega Q univ) ≤ ENNReal.ofReal b.tensorC1)
    (hSymm : ∀ p x, (Htensor p x).IsSymm)
    (i : Fin A.count × Fin B.count)
    (hPhase : ∀ z ∈ sourceCollarNovOriginalInner A B i,
      b.phaseMargin ≤ bestPhaseSupremum
        (repairReferenceFactoryField (sourceCollarNovOriginalSeed A B Omega Q F0) Htensor i z).1)
    (hPositive : ∀ z ∈ sourceCollarNovOriginalInner A B i, ∀ v : D,
      b.tensorLower*‖v‖^2 ≤ round4OriginalNativeTensorCoordinates A B.chart Htensor i z v v)
    (hFirst : ∀ z ∈ sourceCollarNovOriginalOuter A B i, ∀ v : D, b.firstLower*‖v‖^2 ≤
      ‖fderiv ℝ ((fun x => F0 ((B.chart i.2).symm z.1,x)) ∘ (A.chart i.1).symm) z.2 v‖^2) :
    Nonempty (RepairReferenceOriginalLocalFactory b
      (sourceCollarNovOriginalSeed A B Omega Q F0) hF Htensor
      (incrementsOriginalEvaluation A B.chart Omega Q univ) i
      (sourceCollarNovOriginalOuter A B i) (sourceCollarNovOriginalInner A B i) 0) := by
  apply repair_reference_original_local_factory_buffered b
    (sourceCollarNovOriginalSeed A B Omega Q F0) hF
    (incrementsOriginalEvaluation A B.chart Omega Q univ)
    (fun _ _ hy => hy.1) hCoords hC3 Htensor hTensorCoords hC1 hSymm i (hA.chart_mem i.1)
    (sourceCollarNovOriginalOuter A B i) (sourceCollarNovOriginalInner A B i) 0
    (sourceCollarNov_original_outer_open A B i)
    (sourceCollarNov_original_samples A B Omega Q hS hP i)
    (sourceCollarNov_original_inner_bounded A B Omega Q hS hP b.modelRadius hRS hRP i)
    (sourceCollarNov_original_buffer A B i b.buffer hBS hBP)
    hPhase hPositive hFirst

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_local_factory
