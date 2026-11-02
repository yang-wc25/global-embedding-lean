import OriginalCollars.PrimaryPlateauCarrier
import Repair.ReferenceOriginalLocalFactoryInteraction

/-!
# Common primary buffers produced by the same actual original factory

This calls the original factory's actual plateau and its proved observer
jets. The open construction carrier has the explicit common numerical
radius repairReferenceFactoryInteractionBuffer b T. No supplied primary
carrier, chosen inverse, grid packet, or construction-domain evaluation
inclusion is requested.

The omitted old `hInner` and `hEval` premises belonged to an oversized
interaction record. The current geometric conclusion needs neither. In
particular it does not put an open construction set inside a compact
parameter sample with boundary, nor replace the original sample by an
enlarged one. All fields of the same weighted original datum are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Metric Bundle Filter
open scoped ContDiff Topology TensorProduct BigOperators ENNReal
namespace GlobalEmbedding.Continuation.OriginalCollars

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



/-- The actual factory, its actual plateaus and the original transition
profile manufacture a common primary buffer on the same weighted datum. -/
theorem original_factory_primary_common_carrier
    (b : RepairReferenceFactoryBudget m d N)
  (seed : RepairOriginalReferenceSeed (m+1) d N M P)
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (fun x => seed.F0 (p,x)))
  (Htensor : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (S : Fin seed.atlas.count × Fin seed.parameterCount → Set (Fin (m+1+d) → ℝ))
  (O K : Fin seed.atlas.count × Fin seed.parameterCount → Set X)
  (center : Fin seed.atlas.count × Fin seed.parameterCount → X)
  (family : ∀ i, RepairReferenceOriginalLocalFactory b seed hF Htensor S i (O i) (K i) (center i))
    (hseed : RepairReferenceSeedDomains seed)
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation seed.atlas seed.parameterChart i)
    (hSample : ∀ i z, z ∈ O i → parameterTensorModelEquiv (m+1) d z ∈ S i)
    (outer theta : Fin seed.atlas.count × Fin seed.parameterCount → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff IJ 𝓘(ℝ,ℝ) ∞ (theta i))
    (hThetaSource : ∀ i, tsupport (theta i) ⊆
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)).source ∩
      ((seed.parameterChart i.2).prod (seed.atlas.chart i.1)) ⁻¹' K i)
    (hO : ∀ i, IsOpen (O i))
    (hK : ∀ i, K i ⊆ closedBall (center i) b.modelRadius)
    (hBuffer : ∀ i z, z ∈ K i → ball z b.buffer ⊆ O i)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTransition : ∀ nu i z, z ∈ O i → ∀ j, 1 ≤ j →
      let a := repairTemplateIndex (m := m) (Piece := fun i => ↥(family i).s) nu
      let owner := (seed.parameterChart a.1.2).prod (seed.atlas.chart a.1.1)
      let observer := (seed.parameterChart i.2).prod (seed.atlas.chart i.1)
      observer.symm z ∈ owner.source → ‖iteratedFDeriv ℝ j (owner ∘ observer.symm) z‖ ≤ T j)
    (rho : ℝ) (weight : Fin (Fintype.card (Σ i, ↥(family i).s × Edge)) → ℝ) :
    let raw := repairReferenceOriginalFamilyData b seed hF Htensor S O K center family hseed outer
    let data := repairReferenceWeightedData (repairReferencePositiveData raw rho) weight
    ∀ (hd : IncrementsOriginalDomainConditions data)
      (hOOpen : ∀ i, O i ⊆ actualOriginalNativeOpen data i)
      (nu : Fin data.primaryCount) (i : Fin seed.atlas.count × Fin seed.parameterCount),
      let thetaN := round3ParameterNativeParent (seed.parameterChart i.2) (theta i)
      let radius := repairReferenceFactoryInteractionBuffer b T
      let carrier := originalNativePrimaryCarrier data i nu thetaN
      ∃ U : Set X,
        0 < radius ∧ IsCompact carrier ∧ IsOpen U ∧
        carrier ⊆ closedBall (center i) b.modelRadius ∧
        (∀ z ∈ carrier, ball z radius ⊆ U) ∧
        U ⊆ O i ∩ actualOriginalPrimaryNativeOpen data nu i ∧
        U ⊆ (actualOriginalHostJointChart («Ep» := Ep) (seed.atlas.chart i.1)).target ∧
        MapsTo (actualOriginalHostJointChart («Ep» := Ep) (seed.atlas.chart i.1)).symm U
          ((seed.parameterChart i.2).target ×ˢ (univ : Set M)) ∧
        U ⊆ ball (center i) (b.modelRadius+radius) ∧
        (U.Nonempty ↔ carrier.Nonempty) := by
  intro raw data hd hOOpen nu i thetaN radius carrier
  have hParent := repair_reference_original_parent_collar data hd i (theta i)
    (hCompact i) (hSmooth i) (K i) (O i) (center i) b.modelRadius b.buffer
    (hThetaSource i) (hK i) (hBuffer i)
  have hNative := round3Parameter_native_compact_parent (seed.parameterChart i.2)
    (hseed.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i)
    (fun z hz => ⟨(hThetaSource i hz).1.1,mem_univ _⟩)
  have hProperties := repair_reference_original_family_plateau_properties
    b seed hF Htensor S O K center family hseed hSO hSample outer nu
  apply original_primary_buffer_from_actual_plateau b.buffer
    (repairReferenceFactoryInteractionDerivative b T) b.modelRadius b.buffer_pos
    (repairEntranceCompositionProfile_nonneg _ _ (repairReferenceFactoryPlateauProfile_nonneg b) hT 1)
    data hd i nu thetaN hNative.2.1 hParent.1
    (repairReferenceOriginalFamilyPlateau b seed hF Htensor S O K center family nu)
    hProperties.2.1 hProperties.2.2.1
    (fun z hz => (hProperties.2.2.2 z hz).eq_of_nhds)
    (O i) (hO i) (hOOpen i) _ hParent.2.1 (center i) hParent.2.2
  intro z hz
  have hh := repair_reference_original_family_plateau_observer_jets
    b seed hF Htensor S O K center family hseed hSO hSample T hT nu i z
    (repair_reference_original_native_joint_target seed S hSO i z (hSample i z hz))
    (hTransition nu i z hz) 1
  rw [norm_iteratedFDeriv_one] at hh
  exact hh

end GlobalEmbedding.Continuation.OriginalCollars

#print axioms GlobalEmbedding.Continuation.OriginalCollars.original_factory_primary_common_carrier
