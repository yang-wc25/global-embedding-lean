import Repair.IncrementRegionTransitionBudget
import Repair.IncrementLiteralSignedReserves
import Repair.ReferenceSignedPhaseJets

/-! The actual fixed template phases and their original numerical jets.
The datum below records only literal original phases, original owner
coordinates, and template membership. It contains no secondary chart,
completed signed phase bound, solver, or increment output. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter
open scoped ContDiff Topology TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
private local instance regionLiteralRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) := Submodule.closed_of_finiteDimensional _
private local instance regionLiteralSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
variable {K : Set ((SymmetricSquare (EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
  EuclideanSpace ℝ (Fin N)) × (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ))}

structure IncrementActualLiteralPhaseData
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (labelBound : ℕ) where
  owner : Fin Data.primaryCount → Fin Data.atlas.count
  index : Fin Data.primaryCount → C.indices
  edge : Fin Data.primaryCount → EdgePair (Module.finrank ℝ D+1)
  label : Fin Data.primaryCount → ℕ
  label_le : ∀ nu, label nu ≤ labelBound
  phase_eq : ∀ nu, Data.phase nu = fun z =>
    repairReferenceSignedHierarchy C R T ^ label nu *
      (C.template (index nu)).covectors (edge nu) (Data.atlas.chart (owner nu) z.2)
  source : ∀ nu z, z ∈ Data.primaryDomain nu → z.2 ∈ (Data.atlas.chart (owner nu)).source
  owner_samples : ∀ nu z, z ∈ Data.primaryDomain nu →
    Data.atlas.chart (owner nu) z.2 ∈ Data.sourceNormDomain (owner nu)
  operator : ∀ nu z, z ∈ Data.primaryDomain nu →
    ‖repairReferenceSliceOperator (fun x => Data.F (z.1,x))
      (Data.atlas.chart (owner nu)) (Data.atlas.chart (owner nu) z.2)‖ ≤ R ∧
    repairReferenceSliceOperator (fun x => Data.F (z.1,x))
      (Data.atlas.chart (owner nu)) (Data.atlas.chart (owner nu) z.2) ∈
      (C.template (index nu)).operatorDomain
  proper : ∀ nu mu, nu ≠ mu →
    (tsupport (Data.cutoff nu) ∩ tsupport (Data.cutoff mu)).Nonempty → label nu ≠ label mu

def incrementRegionPhaseProfile
    (C : UniformActualGoodDictionaryCover K) (R T coordinateBound sourceBound : ℝ)
    (labelBound : ℕ) (Spatial : ℕ → ℝ) (j : ℕ) : ℝ :=
  repairReferenceSignedHierarchy C R T ^ labelBound * C.covectorBound *
    (incrementRegionTransitionProfile coordinateBound sourceBound Spatial j +
      incrementRegionTransitionProfile coordinateBound sourceBound Spatial j)

theorem increment_actual_region_phase_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (labelBound : ℕ)
    (literal : IncrementActualLiteralPhaseData Data C R T labelBound)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) :
    ((actualOriginalParameterSignedPhase Data i r.val) ∘
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm) =
    repairReferenceActualSignedPhase (Data.atlas.chart i.1)
      (Data.atlas.chart (literal.owner r.val.1.1)) (Data.atlas.chart (literal.owner r.val.1.2))
      ((C.template (literal.index r.val.1.1)).covectors (literal.edge r.val.1.1))
      ((C.template (literal.index r.val.1.2)).covectors (literal.edge r.val.1.2))
      (repairReferenceSignedHierarchy C R T ^ literal.label r.val.1.1)
      (repairReferenceSignedHierarchy C R T ^ literal.label r.val.1.2) r.val.2 := by
  funext z
  simp only [Function.comp_apply,actualOriginalParameterSignedPhase,literal.phase_eq]
  rfl

theorem increment_actual_region_phase_jets
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (C : UniformActualGoodDictionaryCover K) (R T : ℝ) (hT : 0 ≤ T) (labelBound : ℕ)
    (literal : IncrementActualLiteralPhaseData Data C R T labelBound)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (theta : Ep × M → ℝ) (radius buffer coordinateBound sourceBound : ℝ)
    (geometry : RepairReferenceActualInteractionGeometry Data i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) theta radius buffer coordinateBound)
    (hSourceBound : ∀ ih y, y ∈ Data.sourceNormDomain ih → ‖y‖ ≤ sourceBound)
    (Parameter Spatial : ℕ → ℝ) (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    let phase := ((actualOriginalParameterSignedPhase Data i r.val) ∘
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).symm)
    ContDiffOn ℝ ∞ phase geometry.domain ∧
      ∀ j z, z ∈ geometry.domain → ‖iteratedFDeriv ℝ j phase z‖ ≤
        incrementRegionPhaseProfile C R T coordinateBound sourceBound labelBound Spatial j := by
  intro phase
  have hL := increment_actual_interaction_owner_transition_jets Data hd i r theta radius buffer
    coordinateBound sourceBound geometry literal.owner literal.source literal.owner_samples hSourceBound
    Parameter Spatial transition r.val.1.1 (Or.inl rfl)
  have hR := increment_actual_interaction_owner_transition_jets Data hd i r theta radius buffer
    coordinateBound sourceBound geometry literal.owner literal.source literal.owner_samples hSourceBound
    Parameter Spatial transition r.val.1.2 (Or.inr rfl)
  have hLeft := repair_reference_signed_weight_cap C R T hT labelBound (literal.label_le r.val.1.1)
  have hRight := repair_reference_signed_weight_cap C R T hT labelBound (literal.label_le r.val.1.2)
  have hCap := (repair_reference_signed_weight_cap C R T hT labelBound (le_refl labelBound)).1.le
  have h := repair_reference_actual_signed_phase_jets
    (Data.atlas.chart i.1) (Data.atlas.chart (literal.owner r.val.1.1))
    (Data.atlas.chart (literal.owner r.val.1.2)) (hd.atlas_smooth.chart_mem i.1)
    (hd.atlas_smooth.chart_mem _) (hd.atlas_smooth.chart_mem _) geometry.domain geometry.isOpen hL.1 hR.1
    ((C.template (literal.index r.val.1.1)).covectors (literal.edge r.val.1.1))
    ((C.template (literal.index r.val.1.2)).covectors (literal.edge r.val.1.2))
    C.covectorBound (repairReferenceSignedHierarchy C R T ^ labelBound)
    (repairReferenceSignedHierarchy C R T ^ literal.label r.val.1.1)
    (repairReferenceSignedHierarchy C R T ^ literal.label r.val.1.2)
    C.covectorBound_pos.le hCap ((C.bounds _).2.2.2.2 _) ((C.bounds _).2.2.2.2 _)
    ⟨hLeft.1.le,hLeft.2⟩ ⟨hRight.1.le,hRight.2⟩
    (incrementRegionTransitionProfile coordinateBound sourceBound Spatial)
    (incrementRegionTransitionProfile coordinateBound sourceBound Spatial) hL.2 hR.2 r.val.2
  dsimp only [phase]
  rw [increment_actual_region_phase_eq Data C R T labelBound literal i r]
  exact h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_region_phase_eq
#print axioms GlobalEmbedding.Continuation.increment_actual_region_phase_jets
