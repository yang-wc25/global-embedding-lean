import GlobalEmbedding.Paper.InitializationPhaseStability
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import GlobalEmbedding.Paper.SymmetricSquareMapNorm
import GlobalEmbedding.Paper.SymmetricSquareMapProduct
import GlobalEmbedding.Offline.PaperStageChartBridge

/-!
# Actual coordinate Hessians on the original symmetric-square quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:repair`
line 776 and the two-jet/phase-margin stability in `prop:initialization`.

The quotient and all its norms are the repository's original `SymmetricSquare`
with the canonical Hilbert tensor quotient norm. The lift below is a genuine
continuous linear operator on native continuous bilinear maps. It averages the
two arguments before descending; for an actual C² Hessian Schwarz symmetry
identifies this with the unchanged Hessian, with no extra factor.
-/

open Manifold Bundle GlobalEmbedding.Paper
open scoped TensorProduct ContDiff Topology

namespace GlobalEmbedding.Offline

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance actualJetSquareRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance actualJetSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Cache the native nested operator instances. These are exactly Mathlib's
-- operator norms; the explicit names avoid repeated instance-search expansion.
private noncomputable local instance actualBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

private noncomputable local instance actualBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ E] in
private theorem symmetricSquare_clm_ext {A B : SymmetricSquare E →L[ℝ] F}
    (h : ∀ v w, A (symmetricSquareProduct E v w) = B (symmetricSquareProduct E v w)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w => exact h v w
    | add a b ha hb =>
      change A (symmetricSquareQuotient E (a + b)) = B (symmetricSquareQuotient E (a + b))
      simp only [map_add]
      exact congrArg₂ (· + ·) ha hb

/-- The canonical descent of the symmetric part of an actual bilinear map.
It takes values in the unchanged original Hilbert quotient operator space. -/
noncomputable def symmetrizedHessianJet (B : E →L[ℝ] E →L[ℝ] F) :
    SymmetricSquare E →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    (symmetricBilinearDescend
      (((1 / 2 : ℝ) • (B + B.flip)).toLinearMap₁₂) (by
        intro v w
        change (1 / 2 : ℝ) • (B v w + B w v) = (1 / 2 : ℝ) • (B w v + B v w)
        rw [add_comm]))

/-- Product evaluation records the exact normalization of the symmetric part. -/
theorem symmetrizedHessianJet_product (B : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    symmetrizedHessianJet B (symmetricSquareProduct E v w) =
      (1 / 2 : ℝ) • (B v w + B w v) := by
  simp only [symmetrizedHessianJet, LinearMap.coe_toContinuousLinearMap',
    symmetricBilinearDescend_product]
  rfl

variable [FiniteDimensional ℝ F]

/-- The actual Hessian-to-quotient lift is continuous and linear. Its native
operator norm is consequently a fixed finite constant, depending only on these
fixed finite-dimensional normed spaces, not on the map or iteration index. -/
noncomputable def actualHessianLift :
    (E →L[ℝ] E →L[ℝ] F) →L[ℝ] (SymmetricSquare E →L[ℝ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := symmetrizedHessianJet
      map_add' := by
        intro A B
        apply symmetricSquare_clm_ext
        intro v w
        simp only [symmetrizedHessianJet_product, add_apply, smul_add]
        abel
      map_smul' := by
        intro c B
        apply symmetricSquare_clm_ext
        intro v w
        simp only [symmetrizedHessianJet_product, smul_apply,
          smul_add, smul_smul, RingHom.id_apply]
        simp only [mul_comm] }

/-- For a symmetric actual bilinear Hessian the lift evaluates to the Hessian
itself; symmetrization introduces no normalization change on the original quotient. -/
theorem actualHessianLift_product_of_symmetric (B : E →L[ℝ] E →L[ℝ] F)
    (hB : ∀ v w, B v w = B w v) (v w : E) :
    actualHessianLift B (symmetricSquareProduct E v w) = B v w := by
  change symmetrizedHessianJet B (symmetricSquareProduct E v w) = _
  rw [symmetrizedHessianJet_product, ← hB v w, ← two_smul ℝ (B v w), smul_smul]
  norm_num

/-- The difference bound uses the true operator norm of the fixed lift and the
true native bilinear operator norm of the Hessian difference. -/
theorem actualHessianLift_sub_norm_le (A B : E →L[ℝ] E →L[ℝ] F) :
    ‖actualHessianLift (E := E) (F := F) A - actualHessianLift (E := E) (F := F) B‖ ≤
      ‖actualHessianLift (E := E) (F := F)‖ *
        ‖A - B‖ := by
  rw [← map_sub]
  exact (actualHessianLift (E := E) (F := F)).le_opNorm (A - B)

/-- The fixed comparison constant is the actual operator norm of the lift. -/
noncomputable def actualHessianLiftConstant (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] : ℝ :=
  ‖actualHessianLift (E := E) (F := F)‖

theorem actualHessianLiftConstant_nonneg : 0 ≤ actualHessianLiftConstant E F :=
  ContinuousLinearMap.opNorm_nonneg _

/-- The actual coordinate Hessian, descended to the original symmetric square. -/
noncomputable def coordinateHessianJet (u : E → F) (x : E) : SymmetricSquare E →L[ℝ] F :=
  actualHessianLift (fderiv ℝ (fderiv ℝ u) x)

/-- Native real C² Schwarz symmetry identifies the quotient product values
with the actual second derivative, with its original normalization. -/
theorem coordinateHessianJet_product {u : E → F} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    coordinateHessianJet u x (symmetricSquareProduct E v w) =
      fderiv ℝ (fderiv ℝ u) x v w :=
  actualHessianLift_product_of_symmetric _ (hu.isSymmSndFDerivAt (by simp)) v w

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem second_fderiv_sub {u v : E → F} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ v) x =
      fderiv ℝ (fderiv ℝ (fun y ↦ u y - v y)) x := by
  ext a b
  have h := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) F ↦ A ![a, b])
    (iteratedFDeriv_sub_apply hu hv)
  simpa [iteratedFDeriv_two_apply, Pi.sub_def] using h.symm

/-- The true quotient Hessian difference is bounded by the true second
Fréchet derivative of the difference. No independently chosen second jet occurs. -/
theorem coordinateHessianJet_sub_norm_le {u v : E → F} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    ‖coordinateHessianJet u x - coordinateHessianJet v x‖ ≤
      actualHessianLiftConstant E F * ‖iteratedFDeriv ℝ 2 (fun y ↦ u y - v y) x‖ := by
  have h := actualHessianLift_sub_norm_le (fderiv ℝ (fderiv ℝ u) x)
    (fderiv ℝ (fderiv ℝ v) x)
  rw [second_fderiv_sub hu hv, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at h
  exact h

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The actual unprojected coordinate second jet on the original tangent
symmetric square, transported by the native fixed-chart tangent identification. -/
noncomputable def actualCoordinateSecondJet (u : M → F) (x : M) :
    SymmetricSquare (TangentSpace I x) →L[ℝ] F :=
  (coordinateHessianJet (u ∘ (extChartAt I x).symm) (extChartAt I x x)).comp
    (symmetricSquareMapL (tangentSpaceCastModel I x).toContinuousLinearMap)

/-- The constructed actual tangent jet has exactly the coordinate Hessian
values required by the original `TrueSecondFormProjectedJet` theorem. -/
theorem actualCoordinateSecondJet_product {u : M → F} {x : M}
    (hu : ContDiffAt ℝ 2 (u ∘ (extChartAt I x).symm) (extChartAt I x x))
    (v w : TangentSpace I x) :
    actualCoordinateSecondJet (I := I) u x (symmetricSquareProduct (TangentSpace I x) v w) =
      fderiv ℝ (fderiv ℝ (u ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w) := by
  rw [actualCoordinateSecondJet, ContinuousLinearMap.comp_apply, symmetricSquareMapL_product]
  exact coordinateHessianJet_product hu _ _

/-- The actual tangent second-jet difference has the precise chart-transport
factor squared, in the ORIGINAL Hilbert quotient norm. -/
theorem actualCoordinateSecondJet_sub_norm_le {u v : M → F} {x : M}
    (hu : ContDiffAt ℝ 2 (u ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hv : ContDiffAt ℝ 2 (v ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    ‖actualCoordinateSecondJet (I := I) u x - actualCoordinateSecondJet (I := I) v x‖ ≤
      actualHessianLiftConstant E F *
        ‖iteratedFDeriv ℝ 2 ((fun y ↦ u y - v y) ∘ (extChartAt I x).symm)
          (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ ^ 2 := by
  let T := (tangentSpaceCastModel I x).toContinuousLinearMap
  have hT : ‖symmetricSquareMapL T‖ ≤ ‖T‖ ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
    intro z
    simpa only [symmetricSquareMapL_apply] using symmetricSquareMap_norm_le T z
  have hH := coordinateHessianJet_sub_norm_le hu hv
  change ‖(coordinateHessianJet _ _).comp (symmetricSquareMapL T) -
      (coordinateHessianJet _ _).comp (symmetricSquareMapL T)‖ ≤ _
  rw [← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hH hT (norm_nonneg _) (mul_nonneg (actualHessianLiftConstant_nonneg)
      (norm_nonneg _)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- A genuine C² coordinate representative computes the actual ambient
manifold differential. This verifies its differentiability branch first. -/
theorem mvfderiv_eq_fderiv_extChartAt_of_contDiffAt {u : M → F} {x : M}
    (hu : ContDiffAt ℝ 2 (u ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    mvfderiv I u x =
      (fderiv ℝ (u ∘ (extChartAt I x).symm) (extChartAt I x x)).comp
        (tangentSpaceCastModel I x).toContinuousLinearMap := by
  have hman : ContMDiffAt I 𝓘(ℝ, F) 2 u x := by
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    exact hu.contDiffWithinAt
  have hmd := hman.mdifferentiableAt (by simp)
  ext v
  simp only [mvfderiv, hmd.mfderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp]
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ (extChartAt_target_subset_range _
    (mem_extChartAt_target x))) (hu.differentiableAt (by simp))]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Actual first-jet differences are controlled by the actual coordinate
derivative of the difference, with the true fixed-chart tangent norm factor. -/
theorem mvfderiv_sub_norm_le_of_contDiffAt {u v : M → F} {x : M}
    (hu : ContDiffAt ℝ 2 (u ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hv : ContDiffAt ℝ 2 (v ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    ‖mvfderiv I u x - mvfderiv I v x‖ ≤
      ‖iteratedFDeriv ℝ 1 ((fun y ↦ u y - v y) ∘ (extChartAt I x).symm)
        (extChartAt I x x)‖ * ‖(tangentSpaceCastModel I x).toContinuousLinearMap‖ := by
  rw [mvfderiv_eq_fderiv_extChartAt_of_contDiffAt hu,
    mvfderiv_eq_fderiv_extChartAt_of_contDiffAt hv, ← ContinuousLinearMap.sub_comp]
  have hsub := fderiv_fun_sub (hu.differentiableAt (by simp)) (hv.differentiableAt (by simp))
  have hsub' : fderiv ℝ (u ∘ (extChartAt I x).symm) (extChartAt I x x) -
      fderiv ℝ (v ∘ (extChartAt I x).symm) (extChartAt I x x) =
      fderiv ℝ ((fun y ↦ u y - v y) ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    simpa only [Function.comp_def] using hsub.symm
  rw [hsub', norm_iteratedFDeriv_one]
  exact ContinuousLinearMap.opNorm_comp_le _ _

#print axioms symmetrizedHessianJet_product
#print axioms actualHessianLift_product_of_symmetric
#print axioms actualHessianLift_sub_norm_le
#print axioms coordinateHessianJet_product
#print axioms coordinateHessianJet_sub_norm_le
#print axioms actualCoordinateSecondJet_product
#print axioms actualCoordinateSecondJet_sub_norm_le
#print axioms mvfderiv_eq_fderiv_extChartAt_of_contDiffAt
#print axioms mvfderiv_sub_norm_le_of_contDiffAt

end GlobalEmbedding.Offline
