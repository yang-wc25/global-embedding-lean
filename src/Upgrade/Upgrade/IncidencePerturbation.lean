import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

/-!
# Native derivatives of the actual normalized incidence equations

Source: `thm:upgrade`, equation (10.1) and the supported-coincidence operation.
The endpoints have separate coordinate domains, so they may lie in different
charts or components. The equations below are composed with an actual coordinate second form
`B` and the actual value family `F`.  They do not assert that an arbitrary `B`
is geometric: callers must use the identified true second form.  Both value
endpoints remain in every formula.  Fast-angle-dependent vectors are evaluated
only after differentiation; no derivatives of their coefficients are taken.
-/

noncomputable section

open Function

namespace GlobalEmbedding.Upgrade

variable {P X Y T R V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal incidence equations, with the two distinct probe scales. -/
def scaledIncidence (B : P → X → T) (F : P → X → V) (H : P → Y → V)
    (equation : T → R) (sigma a : ℝ) (u : P) (x : X) (y : Y) : R × V :=
  (sigma⁻¹ • equation (B u x), a⁻¹ • (F u x - H u y))

/-- Parameter differentiation of the same actual incidence map.  The normal
equation is differentiated at the current second form, not at the reference
form, and the global value response at the second point is retained. -/
theorem hasFDerivAt_scaledIncidence_parameter
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y)
    (hB : DifferentiableAt ℝ (fun w ↦ B w x) u)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hx : DifferentiableAt ℝ (fun w ↦ F w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ H w y) u) :
    HasFDerivAt (fun w ↦ scaledIncidence B F H equation sigma a w x y)
      ((sigma⁻¹ • (fderiv ℝ equation (B u x)).comp
          (fderiv ℝ (fun w ↦ B w x) u)).prod
        (a⁻¹ • (fderiv ℝ (fun w ↦ F w x) u -
          fderiv ℝ (fun w ↦ H w y) u))) u := by
  exact ((hR.hasFDerivAt.comp u hB.hasFDerivAt).const_smul sigma⁻¹).prodMk
    ((hx.hasFDerivAt.sub hy.hasFDerivAt).const_smul a⁻¹)

/-- Exact first-source differentiation.  The source coordinate frame is
already inside `B` and `F`, so its derivatives are included automatically. -/
theorem hasFDerivAt_scaledIncidence_source
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y)
    (hB : DifferentiableAt ℝ (B u) x)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hF : DifferentiableAt ℝ (F u) x) :
    HasFDerivAt (fun z ↦ scaledIncidence B F H equation sigma a u z y)
      ((sigma⁻¹ • (fderiv ℝ equation (B u x)).comp (fderiv ℝ (B u) x)).prod
        (a⁻¹ • fderiv ℝ (F u) x)) x := by
  exact ((hR.hasFDerivAt.comp x hB.hasFDerivAt).const_smul sigma⁻¹).prodMk
    ((hF.hasFDerivAt.sub_const (H u y)).const_smul a⁻¹)

/-- Multiplying a first-source column by the value scale produces the actual
tangent column.  Its incidence component carries precisely `a / sigma`.
This is the source of `t^(12/5)` in the paper. -/
theorem scaledIncidence_source_column
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (ha : a ≠ 0) (u : P) (x : X) (y : Y) (v : X)
    (hB : DifferentiableAt ℝ (B u) x)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hF : DifferentiableAt ℝ (F u) x) :
    fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • v) =
      ((a / sigma) • fderiv ℝ equation (B u x) (fderiv ℝ (B u) x v),
        fderiv ℝ (F u) x v) := by
  rw [(hasFDerivAt_scaledIncidence_source B F H equation sigma a u x y hB hR hF).fderiv]
  ext <;> simp [smul_smul, ha, div_eq_mul_inv, mul_comm]

/-- A bounded spatial derivative of the actual incidence equation controls
the first-source error.  `D` is the reference tangent derivative; all current
source-frame changes remain in the literal derivative of `B u`. -/
theorem scaledIncidence_source_error_le
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (ha : a ≠ 0) (u : P) (x : X) (y : Y) (v : X)
    (hB : DifferentiableAt ℝ (B u) x)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hF : DifferentiableAt ℝ (F u) x)
    (D : X →L[ℝ] V) (K delta : ℝ)
    (hbound : ‖(fderiv ℝ equation (B u x)).comp (fderiv ℝ (B u) x)‖ ≤ K)
    (hclose : ‖fderiv ℝ (F u) x - D‖ ≤ delta) :
    ‖fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • v) -
        (0, D v)‖ ≤ max (|a / sigma| * K) delta * ‖v‖ := by
  rw [scaledIncidence_source_column B F H equation sigma a ha u x y v hB hR hF]
  apply (norm_prod_le_iff).mpr
  constructor
  · simp only [Prod.fst_sub, Prod.fst, sub_zero, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |a / sigma| * (K * ‖v‖) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ v).trans
          (mul_le_mul_of_nonneg_right hbound (norm_nonneg v))) (abs_nonneg _)
      _ ≤ max (|a / sigma| * K) delta * ‖v‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)
  · simp only [Prod.snd_sub, Prod.snd]
    calc
      ‖fderiv ℝ (F u) x v - D v‖ ≤ delta * ‖v‖ :=
        (ContinuousLinearMap.le_opNorm (fderiv ℝ (F u) x - D) v).trans
          (mul_le_mul_of_nonneg_right hclose (norm_nonneg v))
      _ ≤ max (|a / sigma| * K) delta * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)

end GlobalEmbedding.Upgrade
