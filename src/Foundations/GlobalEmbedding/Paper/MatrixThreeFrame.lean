import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual positively oriented three-dimensional matrix frame

Source: `main.tex`, prop:matrix, equation (3.2) and its following reflection and
connection calculations (lines 303–338). DAG: `matrix-three-frame`.
The columns are exactly `[v, e₃ cos θ − Jv sin θ, −e₃ sin θ − Jv cos θ]`.
-/

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace GlobalEmbedding.Paper

/-- The literal matrix in source equation (3.2), with v=(s,t). -/
def matrixThreeFrame (s t θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s, t * Real.sin θ, t * Real.cos θ;
     t, -s * Real.sin θ, -s * Real.cos θ;
     0, Real.cos θ, -Real.sin θ]

/-- The columns of the actual frame are orthonormal. Expanding their nine inner
products uses precisely unit length of v and the trigonometric square identity. -/
theorem matrixThreeFrame_transpose_mul (s t θ : ℝ) (hunit : s ^ 2 + t ^ 2 = 1) :
    (matrixThreeFrame s t θ).transpose * matrixThreeFrame s t θ = 1 := by
  have hs := congrArg (fun x : ℝ ↦ x * Real.sin θ ^ 2) hunit
  have hc := congrArg (fun x : ℝ ↦ x * Real.cos θ ^ 2) hunit
  have hsc := congrArg (fun x : ℝ ↦ x * (Real.sin θ * Real.cos θ)) hunit
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixThreeFrame, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The actual frame has positive orientation: its determinant is exactly one,
including at s=0 or t=0. Expand the genuine three-by-three determinant and factor
it as (s²+t²)(sin²θ+cos²θ). -/
theorem matrixThreeFrame_det (s t θ : ℝ) (hunit : s ^ 2 + t ^ 2 = 1) :
    (matrixThreeFrame s t θ).det = 1 := by
  calc
    (matrixThreeFrame s t θ).det =
        (s ^ 2 + t ^ 2) * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
      simp [matrixThreeFrame, Matrix.det_fin_three]
      nlinarith [congrArg (fun x : ℝ ↦ s ^ 2 * x) (Real.sin_sq_add_cos_sq θ),
        congrArg (fun x : ℝ ↦ t ^ 2 * x) (Real.sin_sq_add_cos_sq θ)]
    _ = 1 := by rw [hunit, Real.sin_sq_add_cos_sq]; ring

/-- The paper's actual frame belongs to Mathlib's actual special orthogonal
matrix group, by the proved transpose identity and determinant one. -/
theorem matrixThreeFrame_mem_SO (s t θ : ℝ) (hunit : s ^ 2 + t ^ 2 = 1) :
    matrixThreeFrame s t θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  exact Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (matrixThreeFrame_transpose_mul s t θ hunit),
      matrixThreeFrame_det s t θ hunit⟩

/-- Ambient reflection in the second coordinate, as in the source. -/
def matrixThreeReflection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The source's column reflection D. -/
def matrixThreeColumnReflection : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- Actual coordinate reflection has exactly the source's two-sided signs.
This is direct entrywise multiplication, using odd sine and even cosine. -/
theorem matrixThreeFrame_reflection (s t θ : ℝ) :
    matrixThreeFrame s (-t) (-θ) =
      matrixThreeReflection * matrixThreeFrame s t θ * matrixThreeColumnReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixThreeFrame, matrixThreeReflection, matrixThreeColumnReflection,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual entrywise derivative of (3.2) when Xs=-κt, Xt=κs and Xθ=a.
The genuine orbit chain rule will specialize this algebraic formula. -/
def matrixThreeFrameVelocity (s t θ κ a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-κ * t, κ * s * Real.sin θ + t * Real.cos θ * a,
       κ * s * Real.cos θ - t * Real.sin θ * a;
     κ * s, κ * t * Real.sin θ - s * Real.cos θ * a,
       κ * t * Real.cos θ + s * Real.sin θ * a;
     0, -Real.sin θ * a, -Real.cos θ * a]

/-- Genuine scalar chain rules differentiate the actual matrix-valued frame.
The two planar derivatives are the actual curvature equations, not independent
formal matrix derivatives. Apply the native Pi derivative theorem twice and the
usual product/sine/cosine rules to all nine literal entries. -/
theorem matrixThreeFrame_hasDerivAt {s t θ : ℝ → ℝ} {x κ a : ℝ}
    (hs : HasDerivAt s (-κ * t x) x) (ht : HasDerivAt t (κ * s x) x)
    (hθ : HasDerivAt θ a x) :
    HasDerivAt (fun y ↦ matrixThreeFrame (s y) (t y) (θ y))
      (matrixThreeFrameVelocity (s x) (t x) (θ x) κ a) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [matrixThreeFrame, matrixThreeFrameVelocity]
  · exact hs
  · convert ht.mul hθ.sin using 1
    ring
  · convert ht.mul hθ.cos using 1
    ring
  · exact ht
  · convert hs.neg.mul hθ.sin using 1
    simp only [Pi.neg_apply]
    ring
  · convert hs.neg.mul hθ.cos using 1
    simp only [Pi.neg_apply]
    ring
  · exact hasDerivAt_const x 0
  · exact hθ.cos
  · convert hθ.sin.neg using 1
    · ext y
      rfl
    · simp

/-- The exact skew connection, retaining signs and order for the angular cone. -/
def matrixThreeConnection (θ κ a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, κ * Real.sin θ, κ * Real.cos θ;
     -κ * Real.sin θ, 0, -a;
     -κ * Real.cos θ, a, 0]

/-- The velocity is the actual frame times its stated connection. Expanding the
nine entries needs only the sine/cosine identity, and no unit hypothesis. -/
theorem matrixThreeFrameVelocity_eq_mul (s t θ κ a : ℝ) :
    matrixThreeFrameVelocity s t θ κ a =
      matrixThreeFrame s t θ * matrixThreeConnection θ κ a := by
  have hs := congrArg (fun x : ℝ ↦ κ * t * x) (Real.sin_sq_add_cos_sq θ)
  have ht := congrArg (fun x : ℝ ↦ κ * s * x) (Real.sin_sq_add_cos_sq θ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixThreeFrameVelocity, matrixThreeFrame, matrixThreeConnection,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

/-- The literal transpose product is the stated skew connection: substitute the
proved velocity factorization and cancel the actual orthonormal frame. -/
theorem matrixThreeFrame_connection (s t θ κ a : ℝ) (hunit : s ^ 2 + t ^ 2 = 1) :
    (matrixThreeFrame s t θ).transpose * matrixThreeFrameVelocity s t θ κ a =
      matrixThreeConnection θ κ a := by
  rw [matrixThreeFrameVelocity_eq_mul, ← Matrix.mul_assoc,
    matrixThreeFrame_transpose_mul s t θ hunit, one_mul]

/-- At zero curvature and zero angle derivative the actual velocity vanishes,
entry by entry, exactly as needed for XQ=0 on the curvature-zero set. -/
theorem matrixThreeFrameVelocity_zero (s t θ : ℝ) :
    matrixThreeFrameVelocity s t θ 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixThreeFrameVelocity]

#print axioms matrixThreeFrame_hasDerivAt
#print axioms matrixThreeFrame_mem_SO
#print axioms matrixThreeFrame_reflection
#print axioms matrixThreeFrame_connection
#print axioms matrixThreeFrameVelocity_zero
end GlobalEmbedding.Paper
