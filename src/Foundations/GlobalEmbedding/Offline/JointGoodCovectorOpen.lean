import GlobalEmbedding.Offline.GoodDictionaryMargins
import GlobalEmbedding.Offline.GoodCovectorDensity
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Joint openness of the actual second-form/covector good condition

Source: `repair-phase-preparation`, uniform covector neighborhoods for the finite
compact templates. The fixed-domain operator is literally `q ↦ (B q, c_ξ q)`
on the original ambient symmetric square. The original contraction dictionary
identifies its injectivity with the original restriction on `Sym² ker ξ`.
Thus native injective-operator openness gives a true product neighborhood.
-/

noncomputable section
open GlobalEmbedding.Paper Set
open scoped TensorProduct Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance jointGoodRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance jointGoodSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual fixed-domain pair of the second form and original contraction. -/
def secondFormContractionPair
    (B : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ) :
    SymmetricSquare E →L[ℝ] F × E :=
  B.prod (contractionKernelCovectorOperator (LinearMap.id : SymmetricSquare E →ₗ[ℝ]
    SymmetricSquare E) ξ)

/-- The original good predicate is exactly nonzeroness and injectivity of
the actual fixed-domain pair. The full original Sym²-kernel dictionary is reused. -/
theorem good_iff_secondFormContractionPair_injective
    (B : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ) :
    LinearSecondFormGoodCovector B.toLinearMap ξ.toLinearMap ↔
      ξ ≠ 0 ∧ Function.Injective (secondFormContractionPair B ξ) := by
  rw [linearSecondFormGoodCovector_iff_contraction]
  have hn : ξ.toLinearMap ≠ 0 ↔ ξ ≠ 0 := by
    constructor
    · intro h hz
      exact h (by rw [hz]; rfl)
    · intro h hz
      exact h (ContinuousLinearMap.coe_injective hz)
  rw [hn]
  apply and_congr Iff.rfl
  rw [LinearMap.injective_domRestrict_iff]
  have hpair : (secondFormContractionPair B ξ).toLinearMap =
      B.toLinearMap.prod (contractionKernelQuotientMap ξ.toLinearMap) := by
    ext q <;> rfl
  change Disjoint B.toLinearMap.ker (contractionKernelQuotientMap ξ.toLinearMap).ker ↔
    Function.Injective (secondFormContractionPair B ξ).toLinearMap
  rw [← LinearMap.ker_eq_bot, hpair, LinearMap.ker_prod]
  exact disjoint_iff

/-- Joint continuity is continuity of the same actual fixed-domain operator. -/
theorem continuous_secondFormContractionPair :
    Continuous (fun p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) ↦
      secondFormContractionPair p.1 p.2) := by
  let A := contractionKernelCovectorOperator
    (LinearMap.id : SymmetricSquare E →ₗ[ℝ] SymmetricSquare E)
  have hp : Continuous (fun p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) ↦
      (p.1, A p.2)) := continuous_fst.prodMk (A.continuous.comp continuous_snd)
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := SymmetricSquare E)
    (F := F) (G := E) ℝ).continuous.comp hp

/-- The SAME original good predicate is open jointly in the actual operator
and actual continuous covector, with no supplied common good cone. -/
theorem isOpen_joint_actual_good_covectors :
    IsOpen {p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) |
      LinearSecondFormGoodCovector p.1.toLinearMap p.2.toLinearMap} := by
  let : NormedAddCommGroup (SymmetricSquare E) := inferInstance
  let : NormedSpace ℝ (SymmetricSquare E) := inferInstance
  let : FiniteDimensional ℝ (SymmetricSquare E) := inferInstance
  have heq : {p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) |
      LinearSecondFormGoodCovector p.1.toLinearMap p.2.toLinearMap} =
      {p | p.2 ≠ 0} ∩ {p | Function.Injective (secondFormContractionPair p.1 p.2)} := by
    ext p
    exact good_iff_secondFormContractionPair_injective p.1 p.2
  rw [heq]
  have hn : IsOpen {p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) | p.2 ≠ 0} :=
    isOpen_ne.preimage continuous_snd
  have hi : IsOpen {A : SymmetricSquare E →L[ℝ] F × E | Function.Injective A} :=
    ContinuousLinearMap.isOpen_injective (𝕜 := ℝ) (E := SymmetricSquare E) (F := F × E)
  exact hn.inter (hi.preimage (continuous_secondFormContractionPair (E := E) (F := F)))

private theorem open_product_contains_ball {X Y : Type*}
    [TopologicalSpace X] [PseudoMetricSpace Y]
    (s : Set (X × Y)) (hs : IsOpen s) (x : X) (y : Y) (hxy : (x, y) ∈ s) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ x' ∈ U, ∀ y' : Y, dist y' y < ε → (x', y') ∈ s := by
  obtain ⟨U, V, hU, hx, hV, hy, hUV⟩ :=
    (mem_nhds_prod_iff' (x := x) (y := y)).mp (hs.mem_nhds hxy)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV y hy
  refine ⟨ε, hε, U, hU, hx, ?_⟩
  intro x' hx' y' hy'
  exact hUV ⟨hx', hball hy'⟩

/-- One actual good direction has a positive covector-ball radius valid for
every actual second form in a genuine open neighborhood of the reference. -/
theorem actual_good_covector_product_ball
    (B0 : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ)
    (hgood : LinearSecondFormGoodCovector B0.toLinearMap ξ.toLinearMap) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (SymmetricSquare E →L[ℝ] F),
      IsOpen U ∧ B0 ∈ U ∧
      ∀ B ∈ U, ∀ η : E →L[ℝ] ℝ, ‖η - ξ‖ < ε →
        LinearSecondFormGoodCovector B.toLinearMap η.toLinearMap := by
  let : NormedAddCommGroup (SymmetricSquare E) := inferInstance
  let : NormedSpace ℝ (SymmetricSquare E) := inferInstance
  let : FiniteDimensional ℝ (SymmetricSquare E) := inferInstance
  simpa only [dist_eq_norm, Set.mem_ofPred_eq] using open_product_contains_ball
    {p : (SymmetricSquare E →L[ℝ] F) × (E →L[ℝ] ℝ) |
      LinearSecondFormGoodCovector p.1.toLinearMap p.2.toLinearMap}
    (isOpen_joint_actual_good_covectors (E := E) (F := F)) B0 ξ hgood

#print axioms good_iff_secondFormContractionPair_injective
#print axioms continuous_secondFormContractionPair
#print axioms isOpen_joint_actual_good_covectors
#print axioms actual_good_covector_product_ball

end GlobalEmbedding.Offline
