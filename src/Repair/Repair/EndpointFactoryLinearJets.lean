import Repair.EndpointFactoryLinearInputs
import Repair.EndpointOriginalPrimaryRegularity

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
theorem repair_reference_original_family_linear_jets
    (hseed : RepairReferenceSeedDomains seed)
    (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (nu : Fin (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryCount)
    (i : Fin seed.atlas.count × Fin seed.parameterCount)
    (y : Fin (m+1+d) → ℝ)
    (hy : y ∈ incrementsOriginalPrimaryDifferentiation
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) nu i)
    (hForward : ∀ k, 1 ≤ k →
      let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖iteratedFDeriv ℝ k (seed.atlas.chart ix.1.1 ∘ (seed.atlas.chart i.1).symm)
        (incrementsOriginalSourcePoint y)‖ ≤ T k)
    (hInverse : ∀ k,
      let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      ‖iteratedFDeriv ℝ k (seed.atlas.chart i.1 ∘ (seed.atlas.chart ix.1.1).symm)
        (seed.atlas.chart ix.1.1 ((seed.atlas.chart i.1).symm (incrementsOriginalSourcePoint y)))‖ ≤ T k)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (incrementsOriginalLinearArgumentCoordinates
      (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer) nu i) y‖ ≤
      repairOriginalJointLinearProfile (m+1) d b.cover.coefficientBound T j := by
  let data := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
  let ix := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
  exact repair_actual_original_linear_jet data hseed.atlas_smooth nu
    (seed.atlas.chart ix.1.1) (hseed.atlas_smooth.chart_mem ix.1.1)
    (b.cover.template ((family ix.1).pick ix.2.1)) ix.2.2 (fun _ _ => rfl)
    b.cover.coefficientBound b.cover.coefficientBound_pos.le
    (b.cover.bounds ((family ix.1).pick ix.2.1)).2.2.2.1 T hT i y j
    ⟨hy.1.1,hy.2.1.2⟩ (fun k hk _ => hForward k hk) (fun k _ => hInverse k)

/-- Hierarchy rescaling never increases an original linear coefficient
jet, since every chosen hierarchy weight is at least one. -/
theorem repair_weighted_original_linear_jet_le
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hl : IncrementsOriginalLinearSmoothInputs Data) (hOpen : Data.parameterOpen = univ)
    (weight : Fin Data.primaryCount → ℝ) (hWeight : ∀ nu, 1 ≤ weight nu)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (m+1+d) → ℝ) (hy : y ∈ incrementsOriginalPrimaryDifferentiation Data nu i)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (incrementsOriginalLinearArgumentCoordinates (repairReferenceWeightedData Data weight) nu i) y‖ ≤
      ‖iteratedFDeriv ℝ j (incrementsOriginalLinearArgumentCoordinates Data nu i) y‖ := by
  have he : incrementsOriginalLinearArgumentCoordinates (repairReferenceWeightedData Data weight) nu i =
      (weight nu^2)⁻¹ • incrementsOriginalLinearArgumentCoordinates Data nu i := rfl
  have hReg : ContDiffOn ℝ ∞ (incrementsOriginalLinearArgumentCoordinates Data nu i)
      (incrementsOriginalPrimaryDifferentiation Data nu i) := by
    simpa only [incrementsOriginalParameterRegion,hOpen,univ_prod_univ,preimage_univ,inter_univ] using
      hl.linear_coordinates nu i
  have hSmooth := hReg.contDiffAt
    ((actual_original_primaryDifferentiation_open Data hd.primary_open nu i).mem_nhds hy)
  rw [he]
  change ‖iteratedFDeriv ℝ j (fun z => (weight nu^2)⁻¹ • incrementsOriginalLinearArgumentCoordinates Data nu i z) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hSmooth.of_le (by simp)),norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hw : 1 ≤ weight nu^2 := by nlinarith [hWeight nu]
  exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hw) (norm_nonneg _)).trans_eq (one_mul _)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_linear_jets
#print axioms GlobalEmbedding.Continuation.repair_weighted_original_linear_jet_le
