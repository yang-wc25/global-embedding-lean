import GlobalEmbedding.Paper.BalancedQuadraticTranslation
import GlobalEmbedding.Paper.BalancedQuadraticEuclideanCalculus
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverse
import GlobalEmbedding.Paper.SmoothPeriodicLittleMembership
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSmoothDense

/-!
# Translation and differential identities for the actual balanced operators

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1)–(4.2),
lines387–402. All Q operators below act on entire original little functions.
Only the explicit actual scalar W interface remains conditional; its existence
and inverse/regularity properties are supplied by the separate PDE construction.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual order-one bilinear left side of(4.2): differentiate the two
constructed nonlocal Qs and include the actual second Q into order one. -/
noncomputable def balancedQuadraticDerivativeOperator {a N : ℕ} {α : ℝ}
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i j : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 1 α :=
  let post := ContinuousLinearMap.compL ℝ (LittlePeriodicCAlphaFunction a N 2 α)
    (LittlePeriodicCAlphaFunction a 1 2 α) (LittlePeriodicCAlphaFunction a 1 1 α)
  (post (littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single i 1))).comp
      (balancedQuadraticFirst (N := N) W hα j) +
    (post (littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single j 1))).comp
      (balancedQuadraticFirst (N := N) W hα i) +
    (post (littlePeriodicCAlphaRestrictOrder 1 (by omega) hα)).comp
      (balancedQuadraticSecond (N := N) W hα i j)

/-- The actual order-one gradient pairing on the right side of(4.2). -/
noncomputable def balancedQuadraticGradientOperator {a N : ℕ} {α : ℝ}
    (hα : α ≤ 1) (i j : Fin a) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 1 α :=
  (littlePeriodicCAlphaBilinear
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin N)) ℝ
      (EuclideanSpace ℝ (Fin 1)) realEuclideanOneIsometry.toContinuousLinearMap).comp
        (innerSL ℝ)) hα).bilinearComp
      (littlePeriodicCAlphaDirectionalDerivative (N := N) (k := 1) (EuclideanSpace.single i 1))
      (littlePeriodicCAlphaDirectionalDerivative (N := N) (k := 1) (EuclideanSpace.single j 1))

/-- Exact original lift of the actual order-one differentiated-Q expression. -/
theorem balancedQuadraticDerivativeOperator_value {a N : ℕ} {α : ℝ}
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (i j : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α)
    (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticDerivativeOperator W hα i j v w).val.toFun x =
      euclideanCoordinateWordDerivative [i] (balancedQuadraticFirst W hα j v w).val.toFun x +
      euclideanCoordinateWordDerivative [j] (balancedQuadraticFirst W hα i v w).val.toFun x +
      (balancedQuadraticSecond W hα i j v w).val.toFun x := by
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (N := 1) (k := 1) (α := α) x
  rw [← hev]
  change ev (littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single i 1)
      (balancedQuadraticFirst W hα j v w) +
    littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single j 1)
      (balancedQuadraticFirst W hα i v w) +
    littlePeriodicCAlphaRestrictOrder 1 (by omega) hα (balancedQuadraticSecond W hα i j v w)) = _
  rw [map_add, map_add, hev, hev, hev]
  rfl

/-- Exact original scalar gradient pairing, with the native scalar isometry. -/
theorem balancedQuadraticGradientOperator_value {a N : ℕ} {α : ℝ}
    (hα : α ≤ 1) (i j : Fin a) (v w : LittlePeriodicCAlphaFunction a N 2 α)
    (x : EuclideanSpace ℝ (Fin a)) :
    (balancedQuadraticGradientOperator hα i j v w).val.toFun x =
      realEuclideanOneIsometry (inner ℝ (euclideanCoordinateWordDerivative [i] v.val.toFun x)
        (euclideanCoordinateWordDerivative [j] w.val.toFun x)) := rfl

/-- On the diagonal the literal half in first Q cancels the paired first
forcing terms, leaving W applied to the original single product. -/
theorem balancedQuadraticFirst_diagonal {a N : ℕ} {α : ℝ}
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hα : α ≤ 1) (j : Fin a) (v : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirst W hα j v v =
      W (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
        (balancedFirstDerivativeZero hα j v)) := by
  let A := balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
    (balancedFirstDerivativeZero hα j v)
  change (1 / 2 : ℝ) • W (A + A) = W A
  rw [map_add, ← two_smul ℝ (W A), smul_smul]
  norm_num

/-- The exact vector-valued lift of the actual scalar product. -/
theorem balancedZeroOrderDot_lift {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v w : LittlePeriodicCAlphaFunction a N 0 α) :
    (balancedZeroOrderDot hα v w).val.toFun =
      fun x ↦ realEuclideanOneIsometry (inner ℝ (v.val.toFun x) (w.val.toFun x)) := rfl

/-- The actual original shifted Laplacian preserves genuine smooth lifts,
using its literal finite coordinate-word formula and the imported word theorem. -/
theorem balancedShiftedLaplacian_smooth_lift {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (hv : ContDiff ℝ ∞ v.val.toFun) :
    ContDiff ℝ ∞ (littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun := by
  have heq : (littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun =
      fun x ↦ (∑ k : Fin a, euclideanCoordinateWordDerivative [k, k] v.val.toFun x) -
        v.val.toFun x := funext (balancedShiftedLaplacian_word_value hα v)
  rw [heq]
  exact (ContDiff.sum (fun k _ ↦
    (euclideanCoordinateWordDerivative_smooth_periodic [k, k] v.val.toFun hv v.val.periodic).1)).sub hv

/-- The genuine single product underlying diagonal first Q is genuinely smooth
on a smooth periodic input. Its actual lift is the scalar isometry of the native
inner product of the smooth original L lift and smooth first coordinate lift. -/
theorem balancedQuadraticSingleForcing_smooth {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (hv : ContDiff ℝ ∞ v.val.toFun) (j : Fin a) :
    ContDiff ℝ ∞ (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
      (balancedFirstDerivativeZero hα j v)).val.toFun := by
  rw [balancedZeroOrderDot_lift]
  have hD : ContDiff ℝ ∞ (balancedFirstDerivativeZero hα j v).val.toFun := by
    exact (euclideanCoordinateWordDerivative_smooth_periodic [j] v.val.toFun hv v.val.periodic).1
  exact realEuclideanOneIsometry.toLinearIsometry.toContinuousLinearMap.contDiff.comp
    ((balancedShiftedLaplacian_smooth_lift hα v hv).inner ℝ hD)

/-- Differentiate the actual single first forcing, using the genuine inner-product
rule and the exact original coordinate derivatives. -/
theorem balancedQuadraticSingleForcing_derivative {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (hv : ContDiff ℝ ∞ v.val.toFun)
    (i j : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [i]
      (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
        (balancedFirstDerivativeZero hα j v)).val.toFun x =
      realEuclideanOneIsometry
        (inner ℝ ((littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun x)
          (euclideanCoordinateWordDerivative [i, j] v.val.toFun x) +
        inner ℝ (euclideanCoordinateWordDerivative [i]
          (littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun x)
          (euclideanCoordinateWordDerivative [j] v.val.toFun x)) := by
  rw [balancedZeroOrderDot_lift]
  exact balancedEuclideanDot_derivative _ _ (balancedShiftedLaplacian_smooth_lift hα v hv)
    (euclideanCoordinateWordDerivative_smooth_periodic [j] v.val.toFun hv v.val.periodic).1 i x

/-- The exact smooth forcing cancellation in the actual order-zero space.
The prescribed g_i and g_j are genuine representatives of derivatives of the
single first forcings, and p is a genuine order-two representative of the gradient
product. Native product differentiation and the actual L-gradient expansion give
this equality; it assumes neither the desired Q identity nor inverse commutation. -/
theorem balancedQuadraticForcing_cancellation {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (hv : ContDiff ℝ ∞ v.val.toFun)
    (i j : Fin a) (gi gj : LittlePeriodicCAlphaFunction a 1 0 α)
    (hgi : gi.val.toFun = euclideanCoordinateWordDerivative [i]
      (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
        (balancedFirstDerivativeZero hα j v)).val.toFun)
    (hgj : gj.val.toFun = euclideanCoordinateWordDerivative [j]
      (balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
        (balancedFirstDerivativeZero hα i v)).val.toFun)
    (p : LittlePeriodicCAlphaFunction a 1 2 α)
    (hp : p.val.toFun = (balancedQuadraticGradientOperator hα i j v v).val.toFun) :
    gi + gj + balancedQuadraticSecondForcing hα i j v v =
      littlePeriodicCAlphaShiftedLaplacian hα p := by
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply PiLp.ext
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (N := 1) (k := 0) (α := α) x
  have hadd : (gi + gj + balancedQuadraticSecondForcing hα i j v v).val.toFun x =
      gi.val.toFun x + gj.val.toFun x +
        (balancedQuadraticSecondForcing hα i j v v).val.toFun x := by
    rw [← hev, map_add, map_add, hev, hev, hev]
  rw [hadd, PiLp.add_apply, PiLp.add_apply, hgi, hgj,
    balancedQuadraticSingleForcing_derivative hα v hv i j,
    balancedQuadraticSingleForcing_derivative hα v hv j i]
  have hgrad : (balancedQuadraticGradientOperator hα i j v v).val.toFun =
      fun y ↦ realEuclideanOneIsometry (inner ℝ
        (euclideanCoordinateWordDerivative [i] v.val.toFun y)
        (euclideanCoordinateWordDerivative [j] v.val.toFun y)) :=
    funext (balancedQuadraticGradientOperator_value hα i j v v)
  have hL : (littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun =
      balancedEuclideanShiftedLaplacian v.val.toFun :=
    funext (balancedShiftedLaplacian_word_value hα v)
  have hr := congrArg (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0)
    (balancedEuclideanShiftedLaplacian_gradientDot v.val.toFun hv v.val.periodic i j x)
  rw [balancedShiftedLaplacian_word_value hα p x, hp, hgrad]
  change _ = balancedEuclideanShiftedLaplacian
    (fun y ↦ realEuclideanOneIsometry (inner ℝ
      (euclideanCoordinateWordDerivative [i] v.val.toFun y)
      (euclideanCoordinateWordDerivative [j] v.val.toFun y))) x 0
  rw [hr, balancedQuadraticSecondForcing_value, hL,
    euclideanCoordinateWordDerivative_pair_commute v.val.toFun v.val.contDiff j i x]
  have hs (r : ℝ) : realEuclideanOneIsometry r 0 = r := rfl
  simp only [hs, Finset.sum_add_distrib]
  ring

/-- Formula(4.2) for genuine smooth periodic inputs and a true two-sided inverse.
Choose genuine little representatives for the two differentiated forcings and the
gradient product. Actual inverse/derivative commutation identifies their images;
the preceding exact source cancellation and the actual left inverse close the
identity in the actual order-one space. -/
theorem balancedQuadraticIdentity_smooth {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (hv : ContDiff ℝ ∞ v.val.toFun)
    (i j : Fin a) :
    balancedQuadraticDerivativeOperator W hα i j v v =
      balancedQuadraticGradientOperator hα i j v v := by
  let A (k : Fin a) := balancedZeroOrderDot hα (littlePeriodicCAlphaShiftedLaplacian hα v)
    (balancedFirstDerivativeZero hα k v)
  have hA (k : Fin a) : ContDiff ℝ ∞ (A k).val.toFun :=
    balancedQuadraticSingleForcing_smooth hα v hv k
  have hDi := euclideanCoordinateWordDerivative_smooth_periodic [i]
    (A j).val.toFun (hA j) (A j).val.periodic
  have hDj := euclideanCoordinateWordDerivative_smooth_periodic [j]
    (A i).val.toFun (hA i) (A i).val.periodic
  obtain ⟨gi, hgi⟩ := smooth_periodic_little_membership _ hDi.1 hDi.2 hα 0
  obtain ⟨gj, hgj⟩ := smooth_periodic_little_membership _ hDj.1 hDj.2 hα 0
  have hWi := littlePeriodic_shiftedLaplacian_inverse_word hα W hWL hLW
    (A j) (hA j) [i] gi hgi
  have hWj := littlePeriodic_shiftedLaplacian_inverse_word hα W hWL hLW
    (A i) (hA i) [j] gj hgj
  let P := balancedQuadraticGradientOperator hα i j v v
  have hP : P.val.toFun = fun x ↦ realEuclideanOneIsometry (inner ℝ
      (euclideanCoordinateWordDerivative [i] v.val.toFun x)
      (euclideanCoordinateWordDerivative [j] v.val.toFun x)) :=
    funext (balancedQuadraticGradientOperator_value hα i j v v)
  have hPs : ContDiff ℝ ∞ P.val.toFun := by
    rw [hP]
    exact balancedEuclideanDot_contDiff _ _
      (euclideanCoordinateWordDerivative_smooth_periodic [i] v.val.toFun hv v.val.periodic).1
      (euclideanCoordinateWordDerivative_smooth_periodic [j] v.val.toFun hv v.val.periodic).1
  obtain ⟨p, hp⟩ := smooth_periodic_little_membership P.val.toFun hPs P.val.periodic hα 2
  have hsum := congrArg W
    (balancedQuadraticForcing_cancellation hα v hv i j gi gj hgi hgj p hp)
  rw [map_add, map_add, hWL] at hsum
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  rw [balancedQuadraticDerivativeOperator_value,
    balancedQuadraticFirst_diagonal W hα j v, balancedQuadraticFirst_diagonal W hα i v]
  change euclideanCoordinateWordDerivative [i] (W (A j)).val.toFun x +
    euclideanCoordinateWordDerivative [j] (W (A i)).val.toFun x +
    (W (balancedQuadraticSecondForcing hα i j v v)).val.toFun x = P.val.toFun x
  rw [← hWi, ← hWj]
  obtain ⟨ev, hev, _⟩ := collar_little_holder_evaluation (N := 1) (k := 2) (α := α) x
  have hadd : (W gi + W gj + W (balancedQuadraticSecondForcing hα i j v v)).val.toFun x =
      (W gi).val.toFun x + (W gj).val.toFun x +
        (W (balancedQuadraticSecondForcing hα i j v v)).val.toFun x := by
    rw [← hev, map_add, map_add, hev, hev, hev]
  rw [← hadd, hsum, hp]

/-- Formula(4.2) in the actual little C1 space for every actual little C2 input.
Both sides are diagonals of bounded bilinear maps into the original order-one
space. They agree on actual smooth periodic elements by the exact preceding
calculation, hence agree everywhere by actual smooth density and continuity. -/
theorem balancedQuadraticIdentity_of_inverse {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (i j : Fin a) (v : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDerivativeOperator W hα i j v v =
      balancedQuadraticGradientOperator hα i j v v := by
  have hdiag (B : LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 1 α) :
      Continuous (fun u ↦ B u u) := B.continuous₂.comp₂ continuous_id continuous_id
  have hleft := hdiag (balancedQuadraticDerivativeOperator (N := N) W hα i j)
  have hright := hdiag (balancedQuadraticGradientOperator (N := N) hα i j)
  have heq := Continuous.ext_on (littlePeriodicCAlpha_smooth_dense a N 2 α) hleft hright
    (fun u hu ↦ balancedQuadraticIdentity_smooth hα W hWL hLW u hu i j)
  exact congrFun heq v

/-- Actual original formula(4.2) with the fully proved canonical scalar inverse.
No inverse, derivative commutation or desired quadratic identity is assumed.
The conclusion is equality in the original little C1 space, including dimension0. -/
theorem balancedQuadraticIdentity {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (i j : Fin a) (v : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDerivativeOperator
      (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le i j v v =
      balancedQuadraticGradientOperator hα1.le i j v v :=
  balancedQuadraticIdentity_of_inverse hα1.le
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1) i j v

/-- Pointwise reading of the genuine order-one identity with actual coordinate
Frechet derivatives and the actual nonlocal Q evaluated only after construction. -/
theorem balancedQuadraticIdentity_value {a N : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (i j : Fin a)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [i]
        (balancedQuadraticFirst (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
          hα1.le j v v).val.toFun x +
      euclideanCoordinateWordDerivative [j]
        (balancedQuadraticFirst (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
          hα1.le i v v).val.toFun x +
      (balancedQuadraticSecond (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1)
        hα1.le i j v v).val.toFun x =
      realEuclideanOneIsometry (inner ℝ
        (euclideanCoordinateWordDerivative [i] v.val.toFun x)
        (euclideanCoordinateWordDerivative [j] v.val.toFun x)) := by
  rw [← balancedQuadraticDerivativeOperator_value, balancedQuadraticIdentity hα0 hα1,
    balancedQuadraticGradientOperator_value]

#print axioms balancedQuadraticForcing_cancellation
#print axioms balancedQuadraticIdentity_smooth
#print axioms balancedQuadraticIdentity_of_inverse
#print axioms balancedQuadraticIdentity
#print axioms balancedQuadraticIdentity_value
#print axioms balancedQuadraticDerivativeOperator_value
#print axioms balancedQuadraticGradientOperator_value
#print axioms balancedQuadraticFirst_diagonal
#print axioms balancedQuadraticSingleForcing_smooth

end GlobalEmbedding.Paper
