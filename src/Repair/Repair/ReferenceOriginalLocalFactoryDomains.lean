import Repair.ReferenceOriginalLocalFactoryPhases

/-! Exact original owner sampling locations of the actual normal carrier.
These statements are used for backward transitions without enlarging the
original source or parameter norm domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation

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
local notation "Edge" => EdgePair (Module.finrank ℝ D+1)

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
  (hseed : RepairReferenceSeedDomains seed)
  (outer : (Fin seed.atlas.count × Fin seed.parameterCount) → P × M → ℝ)


include hF Htensor O K center in
theorem repair_reference_original_family_domain_coordinates
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) (z : P × M)
    (hz : z ∈ (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryDomain nu) :
    let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
    let q := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
    z ∈ q.source ∧ q z ∈ O a.1 ∧ parameterTensorModelEquiv (m+1) d (q z) ∈ S a.1 := by
  intro a q
  change z ∈ q.source ∩ q ⁻¹' round4NormalCutoffCarrier
    ((family a.1).charts a.2.1 a.2.2).chart a.2.1.val b.normalRadius at hz
  have hO := ((family a.1).charts a.2.1 a.2.2).source_domain hz.2.1
  exact ⟨hz.1,hO,hSample a.1 _ hO⟩

include hF Htensor O K center in
theorem repair_reference_original_family_owner_samples
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (hSEval : ∀ i, S i ⊆ incrementsOriginalEvaluation seed.atlas seed.parameterChart
      seed.sourceNormDomain seed.parameterNormDomain seed.parameterSet i)
    (nu : Fin (Fintype.card (Σ i, ↥(family i).s × Edge))) (z : P × M)
    (hz : z ∈ (repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer).primaryDomain nu) :
    let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
    z.2 ∈ (seed.atlas.chart a.1.1).source ∧
      seed.atlas.chart a.1.1 z.2 ∈ seed.sourceNormDomain a.1.1 ∧
      seed.parameterChart a.1.2 z.1 ∈ seed.parameterNormDomain a.1.2 ∧ z.1 ∈ seed.parameterSet := by
  intro a
  have hc := repair_reference_original_family_domain_coordinates b seed hF Htensor S O K center family
    hseed outer hSample nu z hz
  have heval := hSEval a.1 hc.2.2
  have hmodel := (parameterTensorModelEquiv (m+1) d).symm_apply_apply
    (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2)
  have hp := congrArg Prod.fst hmodel
  have hx := congrArg Prod.snd hmodel
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d
    (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2))=seed.parameterChart a.1.2 z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d
    (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2))=seed.atlas.chart a.1.1 z.2 at hx
  have hs := heval.2.1
  have ht := heval.2.2.1
  have hparam := heval.2.2.2
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d
    (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2)) ∈ seed.sourceNormDomain a.1.1 at hs
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d
    (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2)) ∈ seed.parameterNormDomain a.1.2 at ht
  change (seed.parameterChart a.1.2).symm (incrementsOriginalParameterPoint
    (parameterTensorModelEquiv (m+1) d (seed.parameterChart a.1.2 z.1,seed.atlas.chart a.1.1 z.2))) ∈ seed.parameterSet at hparam
  rw [hx] at hs
  rw [hp] at ht hparam
  rw [(seed.parameterChart a.1.2).left_inv hc.1.1] at hparam
  exact ⟨hc.1.2,hs,ht,hparam⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_domain_coordinates
#print axioms GlobalEmbedding.Continuation.repair_reference_original_family_owner_samples
