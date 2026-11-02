import Smoothing.Round4ActualChartMarginTransport
import GlobalEmbedding.Paper.TruePhaseMarginSpecification
import Repair.IncrementUniformSignedReserve

/-!
# The original auxiliary-norm phase margin in actual coordinates

The ambient inclusion of the normal space is isometric.  The source chart
differential need not be isometric for the fixed auxiliary tangent norm.
Consequently the original best-phase margin gives a coordinate margin with
the explicit square of the forward chart differential as denominator.
This comparison is a background geometric bound, independent of the map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function Bundle
open scoped TensorProduct ContDiff
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule
attribute [local irreducible] bestPhaseSupremum leastSingularNorm
private local instance originalMarginRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private noncomputable local instance originalMarginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section Linear
variable {D E V : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The supremum over unit covectors is transported on the same canonical
kernel quotient.  The pulled covector is normalized only after transporting;
nonzero scalar multiplication leaves its kernel and lower reserve unchanged. -/
theorem increment_best_phase_supremum_transport
    (hdim : 2 ≤ Module.finrank ℝ E) (A : D ≃L[ℝ] E)
    (B : SymmetricSquare D →L[ℝ] V) (T : SymmetricSquare E →L[ℝ] V)
    (hBT : B = T.comp (symmetricSquareMapL A.toContinuousLinearMap))
    (C : ℝ) (hC : 0 < C) (hForward : ‖A.symm.toContinuousLinearMap‖^2 ≤ C) :
    bestPhaseSupremum T / C ≤ bestPhaseSupremum B := by
  have hdimD : 2 ≤ Module.finrank ℝ D := by
    rwa [A.toLinearEquiv.finrank_eq]
  obtain ⟨eta,heta,hattain⟩ := best_phase_maximum_attainment hdim T
  let : Nontrivial eta.ker := covector_kernel_nontrivial hdim eta
  let : Nontrivial (SymmetricSquare eta.ker) := symmetric_square_nontrivial
  have hLower : ∀ z, bestPhaseSupremum T * ‖z‖ ≤ ‖covectorRestriction T eta z‖ := by
    intro z
    have hl := (least_singular_norm_bound (E := SymmetricSquare eta.ker) (F := V)
      (covectorRestriction T eta)).2.1 z
    rwa [hattain] at hl
  have hTB : T = B.comp (symmetricSquareMapL A.symm.toContinuousLinearMap) := by
    ext z
    rw [hBT]
    simp only [ContinuousLinearMap.comp_apply,symmetricSquareMapL_apply]
    rw [show symmetricSquareMap A.toContinuousLinearMap
      (symmetricSquareMap A.symm.toContinuousLinearMap z) = z by
        simpa only [ContinuousLinearEquiv.symm_symm] using symmetricSquareMap_symm A.symm z]
  let xi := eta.comp A.toContinuousLinearMap
  have hxi : xi ≠ 0 := by
    intro hz
    have he : eta = 0 := by
      ext v
      obtain ⟨w,rfl⟩ := A.surjective v
      exact congrArg (fun L : D →L[ℝ] ℝ => L w) hz
    simp [he] at heta
  have hn : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
  have hUnit : ‖(‖xi‖⁻¹ : ℝ) • xi‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hTransport : ∀ z, (bestPhaseSupremum T/C)*‖z‖ ≤
      ‖covectorRestriction B xi z‖ :=
    round4_covector_margin_coordinate_to_intrinsic A.symm eta T B hTB
      (bestPhaseSupremum T) C (best_phase_supremum_specification hdim T).1
      hC hForward hLower
  exact (best_phase_supremum_specification hdimD B).2.2.2
    ((‖xi‖⁻¹ : ℝ) • xi) (bestPhaseSupremum T/C) hUnit
    ((increment_covector_restriction_lower_smul_iff B xi ‖xi‖⁻¹
      (bestPhaseSupremum T/C) (inv_ne_zero hn.ne')).mpr hTransport)
end Linear

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) : M → Type _)]
private local instance originalMarginTangentNormed (x : M) : NormedAddCommGroup (TangentSpace 𝓙 x) := inferInstance
private local instance originalMarginTangentSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓙 x) := inferInstance
private local instance originalMarginTangentInner (x : M) : InnerProductSpace ℝ (TangentSpace 𝓙 x) := inferInstance

/-- The paper's actual true-phase margin, measured in the fixed auxiliary
tangent norm, supplies the coordinate factory margin.  `C` bounds the square
of the actual forward chart differential; it is not a derivative of `F`. -/
theorem increment_original_true_phase_to_coordinate
    (hdim : 2 ≤ m+1)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (z : X) (hz : z ∈ O) (hcoord : z.2 ∈ (e z.1).target)
    (C : ℝ) (hC : 0 < C)
    (hForward : ‖(actualIncrementChartDerivativeEquiv
      (e z.1) (he z.1) z.2 hcoord).symm.toContinuousLinearMap‖^2 ≤ C) :
    truePhaseMargin (F z.1) (hF z.1) ((e z.1).symm z.2) / C ≤
      bestPhaseSupremum (round4ActualPhaseOperatorInChart F e z) := by
  let x := (e z.1).symm z.2
  let A := actualIncrementChartDerivativeEquiv (e z.1) (he z.1) z.2 hcoord
  let T := (normalSpace (I := 𝓙) (F z.1) x).subtypeL.comp
    (trueSecondFormL (F z.1) (hF z.1) x)
  have hdimD : 2 ≤ Module.finrank ℝ D := by simpa using hdim
  have hdimT : 2 ≤ Module.finrank ℝ (TangentSpace 𝓙 x) := by
    rwa [(tangentSpaceCastModel 𝓙 x).toLinearEquiv.finrank_eq]
  have heq : bestPhaseSupremum T = truePhaseMargin (F z.1) (hF z.1) x :=
    (true_phase_margin_specification hdimD (F z.1) (hF z.1) x).2.2.2 T rfl
  have h := increment_best_phase_supremum_transport hdimT A
    (round4ActualPhaseOperatorInChart F e z) T
    (round4_actual_phase_operator_chart_transport F hF e he O hO hJoint z hz hcoord)
    C hC hForward
  rwa [heq] at h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_best_phase_supremum_transport
#print axioms GlobalEmbedding.Continuation.increment_original_true_phase_to_coordinate
