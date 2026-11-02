import Repair.ReferenceOriginalLocalFactoryGlobal
import Repair.ReferenceWeightedNativeData
import Repair.EndpointOriginalLinearJets

/-! Full original linear smoothness of the actual generated reference data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance globalFactoryRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance globalFactorySquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "I" => 𝓘(ℝ,D)
local notation "IJ" => ModelWithCorners.prod 𝓘(ℝ,Ep) 𝓘(ℝ,D)
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)
private local instance globalFactoryProductChart : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance globalFactoryTargetChart : ChartedSpace (Ep × D) (Ep × D) := chartedSpaceSelf (Ep × D)
private local instance globalFactoryProductManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod («I» := 𝓘(ℝ,Ep)) (I' := I) (n := ∞) P M

variable (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : (Fin seed.atlas.count × Fin seed.parameterCount) →
    Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1))))
  (center : (Fin seed.atlas.count × Fin seed.parameterCount) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m+1)))
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))

include hF Htensor O K center in
/-- The actual native linear field now has the original full-joint smooth
input certificate.  Both the field identity and owner-domain containment
are read from the very same generated family datum. -/
theorem repair_reference_original_family_linear_smooth
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ) :
    IncrementsOriginalLinearSmoothInputs
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) := by
  let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
  let Piece : (Fin seed.atlas.count × Fin seed.parameterCount) → Type := fun i => ↥(family i).s
  let index := repairTemplateIndex (m := m) (Piece := Piece)
  apply repair_original_template_linear_smooth_inputs data hseed.atlas_smooth
    (fun nu => seed.atlas.chart (index nu).1.1)
    (fun nu => hseed.atlas_smooth.chart_mem (index nu).1.1)
    (fun nu => b.cover.template ((family (index nu).1).pick (index nu).2.1))
    (fun nu => (index nu).2.2) (fun _ _ _ => rfl)
  intro nu z hz
  exact hz.1.2

include hF Htensor O K center in
theorem repair_reference_positive_weighted_family_linear_smooth
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (rho : ℝ)
    (weight : Fin (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryCount → ℝ) :
    IncrementsOriginalLinearSmoothInputs
      (repairReferenceWeightedData
        (repairReferencePositiveData
          (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) rho) weight) := by
  apply repair_reference_weighted_linear_smooth
  constructor
  exact (repair_reference_original_family_linear_smooth b seed hF Htensor S O K center family hseed outer).linear_coordinates

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_linear_smooth
#print axioms GlobalEmbedding.Continuation.repair_reference_positive_weighted_family_linear_smooth
