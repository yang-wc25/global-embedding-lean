import Repair.EndpointHostTemplateArgument

/-!
# Native reference data with literal template phases and coefficients

Only the original atlas, norm pieces, compact parameter region and map are
stored in the seed. Both reference tensors are computed as gamma(F0).
Every primary phase, cutoff and coefficient is then constructed from the
chosen actual local template and the original host differential.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Bundle
open scoped BigOperators ContDiff
namespace GlobalEmbedding.Continuation

structure RepairOriginalReferenceSeed (n d N : ℕ) (M P : Type*)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [TopologicalSpace P] where
  atlas : BufferedAtlas M (EuclideanSpace ℝ (Fin n))
  sourceNormDomain : Fin atlas.count → Set (EuclideanSpace ℝ (Fin n))
  parameterCount : ℕ
  parameterChart : Fin parameterCount → OpenPartialHomeomorph P (EuclideanSpace ℝ (Fin d))
  parameterNormDomain : Fin parameterCount → Set (EuclideanSpace ℝ (Fin d))
  parameterSet : Set P
  parameterOpen : Set P
  F0 : P × M → EuclideanSpace ℝ (Fin N)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

variable {Host : Type*} [Fintype Host] {Piece : Host → Type*} [∀ i, Fintype (Piece i)]

def repairTemplateIndex : Fin (Fintype.card (Σ i, Piece i × Edge)) ≃ (Σ i, Piece i × Edge) :=
  (Fintype.equivFin _).symm

def repairOriginalTemplateData
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (normal : (Σ i, Piece i × Edge) → P × M → V)
    (domain : (Σ i, Piece i × Edge) → Set (P × M)) :
    IncrementsOriginalNativeData (m+1) d N M P where
  atlas := seed.atlas
  sourceNormDomain := seed.sourceNormDomain
  parameterCount := seed.parameterCount
  parameterChart := seed.parameterChart
  parameterNormDomain := seed.parameterNormDomain
  parameterSet := seed.parameterSet
  parameterOpen := seed.parameterOpen
  F := seed.F0
  H := fun p x => inducedMetric (I := IT) (fun y => seed.F0 (p,y)) x
  reference := fun p x => inducedMetric (I := IT) (fun y => seed.F0 (p,y)) x
  primaryCount := Fintype.card (Σ i, Piece i × Edge)
  phase := fun nu z =>
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    ((template a.1 a.2.1).covectors a.2.2) (host a.1 z.2)
  cutoff := fun nu z =>
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    outer a.1 z * inner a.1 a.2.1 z
  freeNormal := fun nu => normal (repairTemplateIndex (m := m) (Piece := Piece) nu)
  primaryDomain := fun nu => domain (repairTemplateIndex (m := m) (Piece := Piece) nu)
  linearArgument := fun nu _p x =>
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    repairHostTemplateArgument (host a.1) (hhost a.1) (template a.1 a.2.1) a.2.2 x
  tensorNeighborhood := fun _ _ => Set.univ

theorem repair_original_template_covector
    (seed : RepairOriginalReferenceSeed (m+1) d N M P)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ i, host i ∈ IsManifold.maximalAtlas IT ∞ M)
    (template : ∀ i, Piece i → ActualGoodDictionaryTemplate D V)
    (outer : Host → P × M → ℝ) (inner : ∀ i, Piece i → P × M → ℝ)
    (normal : (Σ i, Piece i × Edge) → P × M → V)
    (domain : (Σ i, Piece i × Edge) → Set (P × M))
    (nu : Fin (Fintype.card (Σ i, Piece i × Edge))) (p : P) (x : M) :
    let data := repairOriginalTemplateData seed host hhost template outer inner normal domain
    let a := repairTemplateIndex (m := m) (Piece := Piece) nu
    incrementsOriginalPhaseCovector data nu p x =
      round4HostPhaseCovector (host a.1) ((template a.1 a.2.1).covectors a.2.2) x := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairOriginalTemplateData

