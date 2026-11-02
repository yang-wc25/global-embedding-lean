import GlobalEmbedding.Paper.LittlePeriodicCAlphaBilinear
import GlobalEmbedding.Paper.LittlePeriodicCAlphaCoordinateWordValue
import GlobalEmbedding.Paper.RealEuclideanOneIsometry
import GlobalEmbedding.Paper.EuclideanCoordinateSecondPartialsCommute
import GlobalEmbedding.Paper.LittlePeriodicCAlphaShiftedLaplacianLift
import GlobalEmbedding.Paper.CollarLittleHolderEvaluation

/-!
# Actual bounded bilinear operators in the balanced formulas

Source: `literature/parallelizable-stable-plus-one/main.tex`, formula (4.1),
lines 387–394. The input `W` is the explicitly exposed scalar inverse interface;
constructing the actual PDE inverse remains a separate obligation. All forcing
maps below are constructed from the original little spaces, derivatives, shifted
Laplacian and actual Euclidean inner product, with no assumed quadratic operator.
-/

open scoped ContDiff

noncomputable section
namespace GlobalEmbedding.Paper

variable {a N : ℕ} {α : ℝ}

/-- The genuine scalar inner product on order-zero little spaces. -/
def balancedZeroOrderDot (hα : α ≤ 1) :
    LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 0 α :=
  littlePeriodicCAlphaBilinear
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin N)) ℝ
      (EuclideanSpace ℝ (Fin 1)) realEuclideanOneIsometry.toContinuousLinearMap).comp
        (innerSL ℝ)) hα

/-- Actual first coordinate differentiation, followed by the genuine order-zero inclusion. -/
def balancedFirstDerivativeZero (hα : α ≤ 1) (i : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 0 α :=
  (littlePeriodicCAlphaRestrictOrder 0 (by omega) hα).comp
    (littlePeriodicCAlphaCoordinateWordDerivative [i] (by simp))

/-- Actual two-letter coordinate differentiation in the displayed order. -/
def balancedSecondDerivativeZero (i j : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a N 0 α :=
  littlePeriodicCAlphaCoordinateWordDerivative [i, j] (by simp)

/-- The literal forcing `(Lv)·D_i w + (Lw)·D_i v` in (4.1). -/
def balancedQuadraticFirstForcing (hα : α ≤ 1) (i : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 0 α :=
  let B := (balancedZeroOrderDot (N := N) hα).bilinearComp (littlePeriodicCAlphaShiftedLaplacian (N := N) hα)
    (balancedFirstDerivativeZero (N := N) hα i)
  B + B.flip

/-- The literal second forcing in (4.1), including both Hessian products and all
lower-order terms with their original signs and factor `1/2`. -/
def balancedQuadraticSecondForcing (hα : α ≤ 1) (i j : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 0 α :=
  let H (k : Fin a) := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (balancedSecondDerivativeZero (N := N) i k) (balancedSecondDerivativeZero (N := N) j k)
  let B := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (balancedFirstDerivativeZero (N := N) hα i) (balancedFirstDerivativeZero (N := N) hα j)
  let R := (balancedZeroOrderDot (N := N) hα).bilinearComp (littlePeriodicCAlphaShiftedLaplacian (N := N) hα)
    (balancedSecondDerivativeZero (N := N) i j)
  (∑ k, (H k + (H k).flip)) + (1 / 2 : ℝ) • (B + B.flip) - (R + R.flip)

/-- The actual bounded symmetric first operator `(1/2) W` applied to its actual
first forcing. This conditional construction does not assert existence of `W`. -/
def balancedQuadraticFirst
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.compL ℝ
    (LittlePeriodicCAlphaFunction a N 2 α) (LittlePeriodicCAlphaFunction a 1 0 α)
    (LittlePeriodicCAlphaFunction a 1 2 α) W).comp (balancedQuadraticFirstForcing (N := N) hα i)

/-- The actual bounded second operator `W` applied to its actual second forcing. -/
def balancedQuadraticSecond
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i j : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α :=
  (ContinuousLinearMap.compL ℝ
    (LittlePeriodicCAlphaFunction a N 2 α) (LittlePeriodicCAlphaFunction a 1 0 α)
    (LittlePeriodicCAlphaFunction a 1 2 α) W).comp (balancedQuadraticSecondForcing (N := N) hα i j)

/-- Symmetry of the first actual forcing is literal interchange of its two
summands, as in (4.1). -/
theorem balancedQuadraticFirstForcing_symmetric (hα : α ≤ 1) (i : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirstForcing hα i v w = balancedQuadraticFirstForcing hα i w v := by
  let B := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (littlePeriodicCAlphaShiftedLaplacian (N := N) hα) (balancedFirstDerivativeZero hα i)
  change B v w + B w v = B w v + B v w
  exact add_comm _ _

/-- Symmetry of the second actual forcing is termwise interchange of the
paired Hessian, gradient and shifted-Laplacian summands in (4.1). -/
theorem balancedQuadraticSecondForcing_symmetric (hα : α ≤ 1) (i j : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecondForcing hα i j v w =
      balancedQuadraticSecondForcing hα i j w v := by
  let H (k : Fin a) := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (balancedSecondDerivativeZero (N := N) i k) (balancedSecondDerivativeZero (N := N) j k)
  let B := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (balancedFirstDerivativeZero (N := N) hα i) (balancedFirstDerivativeZero (N := N) hα j)
  let R := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (littlePeriodicCAlphaShiftedLaplacian (N := N) hα) (balancedSecondDerivativeZero i j)
  change ((∑ k, (H k + (H k).flip)) + (1 / 2 : ℝ) • (B + B.flip) -
      (R + R.flip)) v w =
    ((∑ k, (H k + (H k).flip)) + (1 / 2 : ℝ) • (B + B.flip) -
      (R + R.flip)) w v
  simp only [add_apply, sub_apply, smul_apply, sum_apply, ContinuousLinearMap.flip_apply]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro k _
      exact add_comm _ _
    · congr 1
      exact add_comm _ _
  · exact add_comm _ _

/-- The first actual bounded quadratic operator is symmetric, for every
explicit bounded scalar inverse interface `W`. -/
theorem balancedQuadraticFirst_symmetric
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirst W hα i v w = balancedQuadraticFirst W hα i w v := by
  change (1 / 2 : ℝ) • W (balancedQuadraticFirstForcing hα i v w) =
    (1 / 2 : ℝ) • W (balancedQuadraticFirstForcing hα i w v)
  rw [balancedQuadraticFirstForcing_symmetric]

/-- The second actual bounded quadratic operator is symmetric, for every
explicit bounded scalar inverse interface `W`. -/
theorem balancedQuadraticSecond_symmetric
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i j : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecond W hα i j v w = balancedQuadraticSecond W hα i j w v := by
  change W (balancedQuadraticSecondForcing hα i j v w) =
    W (balancedQuadraticSecondForcing hα i j w v)
  rw [balancedQuadraticSecondForcing_symmetric]

/-- Exact original scalar value of the genuine order-zero inner product. -/
theorem balancedZeroOrderDot_value (hα : α ≤ 1)
    (v w : LittlePeriodicCAlphaFunction a N 0 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedZeroOrderDot hα v w).val.toFun x 0 = inner ℝ (v.val.toFun x) (w.val.toFun x) :=
  rfl

/-- The first forcing is exactly the original two terms of (4.1), on every
actual little input, not merely on a dense smooth subset. -/
theorem balancedQuadraticFirstForcing_value (hα : α ≤ 1) (i : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticFirstForcing hα i v w).val.toFun x 0 =
      inner ℝ ((littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun x)
        (euclideanCoordinateWordDerivative [i] w.val.toFun x) +
      inner ℝ ((littlePeriodicCAlphaShiftedLaplacian hα w).val.toFun x)
        (euclideanCoordinateWordDerivative [i] v.val.toFun x) := by
  let B := (balancedZeroOrderDot (N := N) hα).bilinearComp
    (littlePeriodicCAlphaShiftedLaplacian (N := N) hα) (balancedFirstDerivativeZero hα i)
  change ((B v w).val + (B w v).val).toFun x 0 = _
  rw [(periodicCAlpha_pointwise_operations a 1 0 α).2.1]
  rfl

/-- Every constructed quadratic operator has a bilinear norm bound uniform in
the finite coordinate indices. Take one plus the sum of their actual positive bilinear
bounds; each individual bound is at most this constant. Native bounded bilinear
evaluation provides the estimate. Empty coordinate families are allowed. Source: boundedness
of the two operators following (4.1). -/
theorem balancedQuadratic_uniform_bound
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (i : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α),
        ‖balancedQuadraticFirst W hα i v w‖ ≤ C * ‖v‖ * ‖w‖) ∧
      (∀ (i j : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α),
        ‖balancedQuadraticSecond W hα i j v w‖ ≤ C * ‖v‖ * ‖w‖) := by
  let Q₁ := balancedQuadraticFirst (N := N) W hα
  let Q₂ := balancedQuadraticSecond (N := N) W hα
  let b₁ (i : Fin a) := ((Q₁ i).isBoundedBilinearMap.bound).choose
  let b₂ (i j : Fin a) := ((Q₂ i j).isBoundedBilinearMap.bound).choose
  have hp₁ (i : Fin a) : 0 < b₁ i := ((Q₁ i).isBoundedBilinearMap.bound).choose_spec.1
  have hp₂ (i j : Fin a) : 0 < b₂ i j := ((Q₂ i j).isBoundedBilinearMap.bound).choose_spec.1
  let A := ∑ i, b₁ i
  let B := ∑ i, ∑ j, b₂ i j
  let C := 1 + A + B
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ ↦ (hp₁ i).le)
  have hB : 0 ≤ B := Finset.sum_nonneg
    (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ (hp₂ i j).le))
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_, ?_⟩
  · intro i v w
    have hi : b₁ i ≤ A := Finset.single_le_sum (fun j _ ↦ (hp₁ j).le) (Finset.mem_univ i)
    have hiC : b₁ i ≤ C := by dsimp [C]; linarith
    exact (((Q₁ i).isBoundedBilinearMap.bound).choose_spec.2 v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hiC (norm_nonneg v))
        (norm_nonneg w))
  · intro i j v w
    have hij : b₂ i j ≤ ∑ k, b₂ i k :=
      Finset.single_le_sum (fun k _ ↦ (hp₂ i k).le) (Finset.mem_univ j)
    have hi : (∑ k, b₂ i k) ≤ B := Finset.single_le_sum
      (fun l _ ↦ Finset.sum_nonneg (fun k _ ↦ (hp₂ l k).le)) (Finset.mem_univ i)
    have hiC : b₂ i j ≤ C := by dsimp [C]; linarith
    exact (((Q₂ i j).isBoundedBilinearMap.bound).choose_spec.2 v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hiC (norm_nonneg v))
        (norm_nonneg w))

/-- Exact classical lift of the actual first derivative used in the forcing. -/
theorem balancedFirstDerivativeZero_value (hα : α ≤ 1) (i : Fin a)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedFirstDerivativeZero hα i v).val.toFun x =
      euclideanCoordinateWordDerivative [i] v.val.toFun x := rfl

/-- Exact classical lift of the actual second derivative used in the forcing. -/
theorem balancedSecondDerivativeZero_value (i j : Fin a)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedSecondDerivativeZero i j v).val.toFun x =
      euclideanCoordinateWordDerivative [i, j] v.val.toFun x := rfl

/-- Apply the actual second forcing by evaluating its actual finite operator
sum. This spells out the original order-zero little forcing before applying W. -/
theorem balancedQuadraticSecondForcing_apply (hα : α ≤ 1) (i j : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecondForcing hα i j v w =
      (∑ k, (balancedZeroOrderDot hα (balancedSecondDerivativeZero i k v)
        (balancedSecondDerivativeZero j k w) +
        balancedZeroOrderDot hα (balancedSecondDerivativeZero i k w)
          (balancedSecondDerivativeZero j k v))) +
      (1 / 2 : ℝ) • (balancedZeroOrderDot hα (balancedFirstDerivativeZero hα i v)
        (balancedFirstDerivativeZero hα j w) +
        balancedZeroOrderDot hα (balancedFirstDerivativeZero hα i w)
          (balancedFirstDerivativeZero hα j v)) -
      (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
        (balancedSecondDerivativeZero i j w) +
        balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα w)
          (balancedSecondDerivativeZero i j v)) := by
  simp only [balancedQuadraticSecondForcing, add_apply, sub_apply, smul_apply,
    sum_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearComp_apply]

/-- The second forcing has exactly all original Hessian, first-derivative and
Laplacian terms of (4.1), with the literal half and signs, on every little input.
Native continuous scalar evaluation commutes with its finite sums and scalar
multiplication, and each derivative and inner product has its proved exact lift. -/
theorem balancedQuadraticSecondForcing_value (hα : α ≤ 1) (i j : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticSecondForcing hα i j v w).val.toFun x 0 =
      (∑ k, (inner ℝ (euclideanCoordinateWordDerivative [i, k] v.val.toFun x)
        (euclideanCoordinateWordDerivative [j, k] w.val.toFun x) +
        inner ℝ (euclideanCoordinateWordDerivative [i, k] w.val.toFun x)
          (euclideanCoordinateWordDerivative [j, k] v.val.toFun x))) +
      (1 / 2 : ℝ) * (inner ℝ (euclideanCoordinateWordDerivative [i] v.val.toFun x)
        (euclideanCoordinateWordDerivative [j] w.val.toFun x) +
        inner ℝ (euclideanCoordinateWordDerivative [i] w.val.toFun x)
          (euclideanCoordinateWordDerivative [j] v.val.toFun x)) -
      (inner ℝ ((littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun x)
        (euclideanCoordinateWordDerivative [i, j] w.val.toFun x) +
        inner ℝ ((littlePeriodicCAlphaShiftedLaplacian hα w).val.toFun x)
          (euclideanCoordinateWordDerivative [i, j] v.val.toFun x)) := by
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (N := 1) (k := 0) (α := α) x
  let e := realEuclideanOneIsometry.symm.toContinuousLinearMap.comp ev
  have he (f : LittlePeriodicCAlphaFunction a 1 0 α) : e f = f.val.toFun x 0 := by
    change realEuclideanOneIsometry.symm (ev f) = _
    rw [hev]
    rfl
  rw [← he, balancedQuadraticSecondForcing_apply]
  simp only [map_sub, map_add, map_sum, map_smul]
  simp only [smul_eq_mul, he, balancedZeroOrderDot_value, balancedFirstDerivativeZero_value,
    balancedSecondDerivativeZero_value]

/-- The actual scalar inner-product forcing is symmetric in its vector inputs. -/
theorem balancedZeroOrderDot_symmetric (hα : α ≤ 1)
    (v w : LittlePeriodicCAlphaFunction a N 0 α) :
    balancedZeroOrderDot hα v w = balancedZeroOrderDot hα w v := by
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [balancedZeroOrderDot_value, balancedZeroOrderDot_value]
  exact real_inner_comm _ _

/-- The actual second derivative operators commute on every original little
C2 input by the already proved genuine C2 Schwarz theorem. -/
theorem balancedSecondDerivativeZero_commute (i j : Fin a)
    (v : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedSecondDerivativeZero i j v = balancedSecondDerivativeZero j i v := by
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  exact euclideanCoordinateWordDerivative_pair_commute v.val.toFun v.val.contDiff i j x

/-- The second forcing is also symmetric in its coordinate indices. Actual
inner-product symmetry exchanges the paired terms; actual C2 Schwarz exchanges
the final mixed derivatives. This supports one entry per symmetric index pair. -/
theorem balancedQuadraticSecondForcing_index_symmetric (hα : α ≤ 1) (i j : Fin a)
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecondForcing hα i j v w =
      balancedQuadraticSecondForcing hα j i v w := by
  rw [balancedQuadraticSecondForcing_apply, balancedQuadraticSecondForcing_apply]
  have hH :
      (∑ k, (balancedZeroOrderDot hα (balancedSecondDerivativeZero i k v)
        (balancedSecondDerivativeZero j k w) +
        balancedZeroOrderDot hα (balancedSecondDerivativeZero i k w)
          (balancedSecondDerivativeZero j k v))) =
      ∑ k, (balancedZeroOrderDot hα (balancedSecondDerivativeZero j k v)
        (balancedSecondDerivativeZero i k w) +
        balancedZeroOrderDot hα (balancedSecondDerivativeZero j k w)
          (balancedSecondDerivativeZero i k v)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [balancedZeroOrderDot_symmetric hα (balancedSecondDerivativeZero i k v)
      (balancedSecondDerivativeZero j k w),
      balancedZeroOrderDot_symmetric hα (balancedSecondDerivativeZero i k w)
        (balancedSecondDerivativeZero j k v)]
    exact add_comm _ _
  have hB :
      balancedZeroOrderDot hα (balancedFirstDerivativeZero hα i v)
        (balancedFirstDerivativeZero hα j w) +
        balancedZeroOrderDot hα (balancedFirstDerivativeZero hα i w)
          (balancedFirstDerivativeZero hα j v) =
      balancedZeroOrderDot hα (balancedFirstDerivativeZero hα j v)
        (balancedFirstDerivativeZero hα i w) +
        balancedZeroOrderDot hα (balancedFirstDerivativeZero hα j w)
          (balancedFirstDerivativeZero hα i v) := by
    rw [balancedZeroOrderDot_symmetric hα (balancedFirstDerivativeZero hα i v)
      (balancedFirstDerivativeZero hα j w),
      balancedZeroOrderDot_symmetric hα (balancedFirstDerivativeZero hα i w)
        (balancedFirstDerivativeZero hα j v)]
    exact add_comm _ _
  rw [hH, hB, balancedSecondDerivativeZero_commute j i w,
    balancedSecondDerivativeZero_commute j i v]

/-- The actual second quadratic operator takes values in symmetric second-index
data; no assumed symmetry of a supplied quadratic operator is used. -/
theorem balancedQuadraticSecond_index_symmetric
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i j : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecond W hα i j v w = balancedQuadraticSecond W hα j i v w := by
  change W (balancedQuadraticSecondForcing hα i j v w) =
    W (balancedQuadraticSecondForcing hα j i v w)
  rw [balancedQuadraticSecondForcing_index_symmetric]

#print axioms balancedQuadraticFirst_symmetric
#print axioms balancedQuadraticSecond_symmetric
#print axioms balancedQuadratic_uniform_bound
#print axioms balancedQuadraticFirstForcing_value
#print axioms balancedQuadraticSecondForcing_value
#print axioms balancedQuadraticSecond_index_symmetric

end GlobalEmbedding.Paper
