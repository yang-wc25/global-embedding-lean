import GlobalEmbedding.Paper.CollarHolderTargetMap
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The actual complex little Hölder space through orthogonal real coordinates

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. An orthogonal real coordinate map identifies the complex Euclidean
value space with a real Euclidean value space. The original real Hölder norm and actual
smooth closure therefore give the complex-valued carrier without changing the norm formula.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Orthogonal real coordinates on the complex Euclidean value space.
Source: `prop:collar`, complexification. An orthonormal basis provides an actual real linear
isometry, so each derivative norm and each top-jet difference norm is preserved exactly. -/
noncomputable def collarComplexHolderCoordinates (N : ℕ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)))) := by
  let := InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin N))
  exact (stdOrthonormalBasis ℝ (EuclideanSpace ℂ (Fin N))).repr

/-- The actual complex-valued little Hölder carrier, represented in orthogonal real coordinates.
Source: `prop:collar`, complex coefficient space. This is the existing actual smooth closure
with its original norm, in the real dimension of the complex Euclidean target. -/
def CollarComplexHolderSpace (a N k : ℕ) (α : ℝ) :=
  LittlePeriodicCAlphaFunction a (Module.finrank ℝ (EuclideanSpace ℂ (Fin N))) k α

/-- The original normed additive group on the orthogonally realified actual carrier.
Source: `prop:collar`, complex coefficient space. -/
noncomputable instance collarComplexHolderNormedAddCommGroup {a N k : ℕ} {α : ℝ} :
    NormedAddCommGroup (CollarComplexHolderSpace a N k α) :=
  inferInstanceAs (NormedAddCommGroup
    (LittlePeriodicCAlphaFunction a (Module.finrank ℝ (EuclideanSpace ℂ (Fin N))) k α))

/-- The actual real scalar structure inherited from the realified carrier.
Source: `prop:collar`, complex coefficient space. -/
noncomputable instance collarComplexHolderRealNormedSpace {a N k : ℕ} {α : ℝ} :
    NormedSpace ℝ (CollarComplexHolderSpace a N k α) :=
  inferInstanceAs (NormedSpace ℝ
    (LittlePeriodicCAlphaFunction a (Module.finrank ℝ (EuclideanSpace ℂ (Fin N))) k α))

/-- Actual completeness inherited from the proved little-space completeness theorem.
Source: `prop:collar`, complex coefficient space. -/
instance collarComplexHolderCompleteSpace {a N k : ℕ} {α : ℝ} :
    CompleteSpace (CollarComplexHolderSpace a N k α) :=
  inferInstanceAs (CompleteSpace
    (LittlePeriodicCAlphaFunction a (Module.finrank ℝ (EuclideanSpace ℂ (Fin N))) k α))

/-- The actual complex Euclidean valued lift of a realified little Hölder element.
Source: `prop:collar`, complex coefficient space. -/
noncomputable def collarComplexHolderFunction {a N k : ℕ} {α : ℝ}
    (f : CollarComplexHolderSpace a N k α) :
    EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N) :=
  (collarComplexHolderCoordinates N).symm ∘
    f.val.toFun

/-- The complex-valued lift determines the actual realified carrier element.
Source: `prop:collar`, complex coefficient space. Apply the inverse coordinate isometry
pointwise, then use the proved injectivity of the actual real underlying-function map. -/
theorem collarComplexHolderFunction_injective {a N k : ℕ} {α : ℝ} :
    Function.Injective (collarComplexHolderFunction (a := a) (N := N) (k := k) (α := α)) := by
  intro f g h
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply (collarComplexHolderCoordinates N).symm.injective
  exact congrFun h x

/-- Multiplication of complex target values by c, expressed in the same orthogonal real
coordinates. Source: `prop:collar`, actual pointwise complex scalars. -/
noncomputable def collarComplexHolderScalarTarget (N : ℕ) (c : ℂ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)))) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)))) :=
  (collarComplexHolderCoordinates N).toLinearIsometry.toContinuousLinearMap.comp
    (((ContinuousLinearMap.lsmul ℝ ℂ) c).comp
      (collarComplexHolderCoordinates N).symm.toLinearIsometry.toContinuousLinearMap)

/-- Orthogonal coordinates preserve the norm bound for complex scalar multiplication.
Source: `prop:collar`. Pointwise isometry and norm_smul give the bound, including N=0. -/
theorem collarComplexHolderScalarTarget_norm_le (N : ℕ) (c : ℂ) :
    ‖collarComplexHolderScalarTarget N c‖ ≤ ‖c‖ := by
  apply (collarComplexHolderScalarTarget N c).opNorm_le_bound (norm_nonneg c)
  intro x
  simp only [collarComplexHolderScalarTarget, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.lsmul_apply,
    LinearIsometryEquiv.norm_map, norm_smul]
  exact le_rfl

/-- The actual bounded little-space operator inducing multiplication by c on target values.
Source: `prop:collar`. Its data come from the proved target-postcomposition theorem. -/
noncomputable def collarComplexHolderScalarOperator {a N k : ℕ} {α : ℝ} (c : ℂ) :
    CollarComplexHolderSpace a N k α →L[ℝ] CollarComplexHolderSpace a N k α :=
  Classical.choose (Classical.choose_spec
    (collar_holder_target_map (a := a) (k := k) (α := α)
      (collarComplexHolderScalarTarget N c)))

/-- The constructed scalar operator has exactly the prescribed pointwise complex values.
Source: `prop:collar`. Unfold the target-postcomposition identity and cancel the orthogonal
coordinate map with its inverse. -/
theorem collarComplexHolderScalarOperator_function {a N k : ℕ} {α : ℝ}
    (c : ℂ) (f : CollarComplexHolderSpace a N k α) :
    collarComplexHolderFunction (collarComplexHolderScalarOperator c f) =
      fun x ↦ c • collarComplexHolderFunction f x := by
  have hf := (Classical.choose_spec (Classical.choose_spec
    (collar_holder_target_map (a := a) (k := k) (α := α)
      (collarComplexHolderScalarTarget N c)))).2.2.1 f
  funext x
  change (collarComplexHolderCoordinates N).symm
    ((collarComplexHolderScalarOperator c f).val.toFun x) = _
  rw [show (collarComplexHolderScalarOperator c f).val.toFun =
    collarComplexHolderScalarTarget N c ∘ f.val.toFun from hf]
  simp only [Function.comp_apply, collarComplexHolderScalarTarget,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.lsmul_apply,
    LinearIsometryEquiv.symm_apply_apply,
    collarComplexHolderFunction]

/-- The actual scalar operator obeys the exact source-norm upper bound.
Source: `prop:collar`. Combine the proved target operator bound and postcomposition bound. -/
theorem collarComplexHolderScalarOperator_norm_le {a N k : ℕ} {α : ℝ} (c : ℂ) :
    ‖collarComplexHolderScalarOperator (a := a) (N := N) (k := k) (α := α) c‖ ≤ ‖c‖ :=
  (Classical.choose_spec (Classical.choose_spec
    (collar_holder_target_map (a := a) (k := k) (α := α)
      (collarComplexHolderScalarTarget N c)))).2.2.2.trans
        (collarComplexHolderScalarTarget_norm_le N c)

/-- The complex-valued lift of zero is zero.
Source: `prop:collar`, inherited pointwise vector operations. -/
theorem collarComplexHolderFunction_zero {a N k : ℕ} {α : ℝ} :
    collarComplexHolderFunction (0 : CollarComplexHolderSpace a N k α) = 0 := by
  funext x
  change (collarComplexHolderCoordinates N).symm
    ((0 : PeriodicCAlphaFunction a _ k α).toFun x) = 0
  rw [(periodicCAlpha_pointwise_operations a _ k α).1]
  exact (collarComplexHolderCoordinates N).symm.map_zero

/-- The complex-valued lift respects addition.
Source: `prop:collar`, inherited pointwise vector operations and linear coordinates. -/
theorem collarComplexHolderFunction_add {a N k : ℕ} {α : ℝ}
    (f g : CollarComplexHolderSpace a N k α) :
    collarComplexHolderFunction (f + g) =
      collarComplexHolderFunction f + collarComplexHolderFunction g := by
  funext x
  change (collarComplexHolderCoordinates N).symm ((f.val + g.val).toFun x) = _
  rw [(periodicCAlpha_pointwise_operations a _ k α).2.1]
  exact (collarComplexHolderCoordinates N).symm.map_add _ _

/-- The complex-valued lift respects the inherited real scalar action.
Source: `prop:collar`, inherited pointwise real operations and real linear coordinates. -/
theorem collarComplexHolderFunction_real_smul {a N k : ℕ} {α : ℝ}
    (r : ℝ) (f : CollarComplexHolderSpace a N k α) :
    collarComplexHolderFunction (r • f) = r • collarComplexHolderFunction f := by
  funext x
  change (collarComplexHolderCoordinates N).symm ((r • f.val).toFun x) = _
  rw [(periodicCAlpha_pointwise_operations a _ k α).2.2]
  exact (collarComplexHolderCoordinates N).symm.map_smul r _

/-- Actual pointwise complex scalar multiplication on the realified little closure.
Source: `prop:collar`. All module laws follow from their actual pointwise complex laws and
injectivity of the underlying-function map. The actual carrier and norm are unchanged. -/
noncomputable instance collarComplexHolderModule {a N k : ℕ} {α : ℝ} :
    Module ℂ (CollarComplexHolderSpace a N k α) where
  smul := fun c f ↦ collarComplexHolderScalarOperator c f
  one_smul f := by
    change collarComplexHolderScalarOperator 1 f = f
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, one_smul]
  mul_smul c d f := by
    change collarComplexHolderScalarOperator (c * d) f =
      collarComplexHolderScalarOperator c (collarComplexHolderScalarOperator d f)
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, mul_smul]
  smul_add c f g := by
    change collarComplexHolderScalarOperator c (f + g) =
      collarComplexHolderScalarOperator c f + collarComplexHolderScalarOperator c g
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, collarComplexHolderFunction_add,
      Pi.add_apply, smul_add]
    rfl
  smul_zero c := by
    change collarComplexHolderScalarOperator c 0 = 0
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, collarComplexHolderFunction_zero,
      Pi.zero_apply, smul_zero]
    rfl
  add_smul c d f := by
    change collarComplexHolderScalarOperator (c + d) f =
      collarComplexHolderScalarOperator c f + collarComplexHolderScalarOperator d f
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, collarComplexHolderFunction_add,
      add_smul]
    rfl
  zero_smul f := by
    change collarComplexHolderScalarOperator 0 f = 0
    apply collarComplexHolderFunction_injective
    simp only [collarComplexHolderScalarOperator_function, collarComplexHolderFunction_zero,
      zero_smul]
    rfl

/-- The actual complex scalar action preserves the source norm with its usual scalar factor.
Source: `prop:collar`. The scalar operator bound gives norm_smul_le; Mathlib then derives
the equality norm_smul using the inverse scalar, including the zero scalar case. -/
noncomputable instance collarComplexHolderNormedSpace {a N k : ℕ} {α : ℝ} :
    NormedSpace ℂ (CollarComplexHolderSpace a N k α) where
  norm_smul_le c f :=
    ((collarComplexHolderScalarOperator c).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (collarComplexHolderScalarOperator_norm_le c)
        (norm_nonneg f))


/-- Actual complex scalar multiplication is pointwise on the complex-valued lift.
Source: `prop:collar`, actual complex coefficient space. -/
theorem collarComplexHolderFunction_smul {a N k : ℕ} {α : ℝ}
    (c : ℂ) (f : CollarComplexHolderSpace a N k α) :
    collarComplexHolderFunction (c • f) = c • collarComplexHolderFunction f :=
  collarComplexHolderScalarOperator_function c f

/-- The inherited real scalar action agrees with restriction of the constructed complex action.
Source: `prop:collar`. Injectivity reduces compatibility to the usual scalar tower on the
actual complex Euclidean target values. -/
instance collarComplexHolderScalarTower {a N k : ℕ} {α : ℝ} :
    IsScalarTower ℝ ℂ (CollarComplexHolderSpace a N k α) where
  smul_assoc r c f := by
    apply collarComplexHolderFunction_injective
    rw [collarComplexHolderFunction_smul, collarComplexHolderFunction_real_smul,
      collarComplexHolderFunction_smul]
    exact smul_assoc r c (collarComplexHolderFunction f)

/-- The inherited realified norm is exactly the derivative-supremum plus flat-torus Hölder
formula of the actual complex-valued lift.

Source: `prop:collar`, complex coefficient space. The orthogonal target coordinates preserve
every iterated derivative norm and every difference of top jets. Consequently the actual
real supremum sets coincide term by term, including the empty quotient set, and so do their
finite sum and the full original norm. This is equality of formulas, not norm equivalence. -/
theorem collarComplexHolder_norm_formula {a N k : ℕ} {α : ℝ}
    (f : CollarComplexHolderSpace a N k α) :
    ‖f‖ =
      (∑ j ∈ Finset.range (k + 1), sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧
          r = ‖iteratedFDeriv ℝ j (collarComplexHolderFunction f) x‖}) +
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist
          (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r = ‖iteratedFDeriv ℝ k (collarComplexHolderFunction f) x -
          iteratedFDeriv ℝ k (collarComplexHolderFunction f) y‖ / d ^ α} := by
  have hjet (j : ℕ) (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (collarComplexHolderFunction f) x‖ =
        ‖iteratedFDeriv ℝ j f.val.toFun x‖ :=
    (collarComplexHolderCoordinates N).symm.norm_iteratedFDeriv_comp_left f.val.toFun x j
  have heq (x : EuclideanSpace ℝ (Fin a)) :
      iteratedFDeriv ℝ k (collarComplexHolderFunction f) x =
        ContinuousLinearMap.compContinuousMultilinearMap
          (collarComplexHolderCoordinates N).symm.toLinearIsometry.toContinuousLinearMap
          (iteratedFDeriv ℝ k f.val.toFun x) :=
    (collarComplexHolderCoordinates N).symm.toContinuousLinearEquiv.iteratedFDeriv_comp_left
  have hdiff (x y : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ k (collarComplexHolderFunction f) x -
        iteratedFDeriv ℝ k (collarComplexHolderFunction f) y‖ =
      ‖iteratedFDeriv ℝ k f.val.toFun x - iteratedFDeriv ℝ k f.val.toFun y‖ := by
    rw [heq x, heq y]
    let e := (collarComplexHolderCoordinates N).symm.toLinearIsometry
    have heq' : e.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k f.val.toFun x) -
        e.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k f.val.toFun y) =
        e.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k f.val.toFun x - iteratedFDeriv ℝ k f.val.toFun y) := by
      ext m
      simp
    rw [heq']
    exact e.norm_compContinuousMultilinearMap _
  simp_rw [hjet, hdiff]
  rfl

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarComplexHolderCoordinates
#print axioms GlobalEmbedding.Paper.collarComplexHolderScalarTarget_norm_le

#print axioms GlobalEmbedding.Paper.collarComplexHolderNormedSpace
#print axioms GlobalEmbedding.Paper.collarComplexHolderCompleteSpace
#print axioms GlobalEmbedding.Paper.collarComplexHolderScalarTower
#print axioms GlobalEmbedding.Paper.collarComplexHolder_norm_formula
