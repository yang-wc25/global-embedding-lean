import GlobalEmbedding.Paper.BalancedQuadraticOperators
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverseTranslation
import GlobalEmbedding.Paper.EuclideanCoordinateWordTranslation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-! Actual whole-function balanced Q translation; extracted unchanged proved bodies. -/

namespace GlobalEmbedding.Paper

/-- The actual original L lift is exactly the displayed coordinate-word sum.
This is the already-proved original lift, with the native unit-vector identity. -/
theorem balancedShiftedLaplacian_word_value {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (v : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (littlePeriodicCAlphaShiftedLaplacian hα v).val.toFun x =
      (∑ k : Fin a, euclideanCoordinateWordDerivative [k, k] v.val.toFun x) - v.val.toFun x := by
  simpa only [EuclideanSpace.basisFun_apply, euclideanCoordinateWordDerivative] using
    littlePeriodicCAlphaShiftedLaplacian_lift hα v x

/-- The exact first forcing commutes with simultaneous actual torus translation.
Lift the torus shift, use its exact source formula, and translate every actual
coordinate derivative, including the two derivatives in the actual L. -/
theorem balancedQuadraticFirstForcing_translate {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (i : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirstForcing hα i (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticFirstForcing hα i v w) := by
  obtain ⟨u, rfl⟩ := periodic_flat_torus_projection.surjective h
  simp only [littlePeriodicCAlphaTorusTranslate_lift]
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply PiLp.ext
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  change (balancedQuadraticFirstForcing hα i (littlePeriodicCAlphaTranslateIsometry u v)
    (littlePeriodicCAlphaTranslateIsometry u w)).val.toFun x 0 =
      (balancedQuadraticFirstForcing hα i v w).val.toFun (x + u) 0
  have hv : (littlePeriodicCAlphaTranslateIsometry u v).val.toFun =
      fun y ↦ v.val.toFun (y + u) := rfl
  have hw : (littlePeriodicCAlphaTranslateIsometry u w).val.toFun =
      fun y ↦ w.val.toFun (y + u) := rfl
  simp only [balancedQuadraticFirstForcing_value, balancedShiftedLaplacian_word_value,
    hv, hw, euclideanCoordinateWordDerivative_translate]

/-- The exact second forcing commutes with simultaneous actual torus translation.
Its source formula contains only the actual at-most-two-letter derivatives,
inner products and actual L, so the same every-lift identities apply termwise. -/
theorem balancedQuadraticSecondForcing_translate {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (i j : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecondForcing hα i j (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticSecondForcing hα i j v w) := by
  obtain ⟨u, rfl⟩ := periodic_flat_torus_projection.surjective h
  simp only [littlePeriodicCAlphaTorusTranslate_lift]
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply PiLp.ext
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  change (balancedQuadraticSecondForcing hα i j (littlePeriodicCAlphaTranslateIsometry u v)
    (littlePeriodicCAlphaTranslateIsometry u w)).val.toFun x 0 =
      (balancedQuadraticSecondForcing hα i j v w).val.toFun (x + u) 0
  have hv : (littlePeriodicCAlphaTranslateIsometry u v).val.toFun =
      fun y ↦ v.val.toFun (y + u) := rfl
  have hw : (littlePeriodicCAlphaTranslateIsometry u w).val.toFun =
      fun y ↦ w.val.toFun (y + u) := rfl
  simp only [balancedQuadraticSecondForcing_value, balancedShiftedLaplacian_word_value,
    hv, hw, euclideanCoordinateWordDerivative_translate]

/-- Actual first Q is equivariant whenever its explicit whole-function scalar W
is equivariant; native translation linearity handles the literal factor1/2. -/
theorem balancedQuadraticFirst_translate {a N : ℕ} {α : ℝ}
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hW : ∀ (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
      (f : LittlePeriodicCAlphaFunction a 1 0 α),
      W (littlePeriodicCAlphaTorusTranslate h f) = littlePeriodicCAlphaTorusTranslate h (W f))
    (hα : α ≤ 1) (i : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirst W hα i (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticFirst W hα i v w) := by
  change (1 / 2 : ℝ) • W (balancedQuadraticFirstForcing hα i
      (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w)) =
    littlePeriodicCAlphaTorusTranslate h ((1 / 2 : ℝ) • W (balancedQuadraticFirstForcing hα i v w))
  rw [balancedQuadraticFirstForcing_translate hα i h v w, hW, map_smul]

/-- Actual second Q is equivariant whenever its explicit whole-function scalar W
is equivariant. No pointwise replacement quadratic map is used. -/
theorem balancedQuadraticSecond_translate {a N : ℕ} {α : ℝ}
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hW : ∀ (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
      (f : LittlePeriodicCAlphaFunction a 1 0 α),
      W (littlePeriodicCAlphaTorusTranslate h f) = littlePeriodicCAlphaTorusTranslate h (W f))
    (hα : α ≤ 1) (i j : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecond W hα i j (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticSecond W hα i j v w) := by
  change W (balancedQuadraticSecondForcing hα i j
      (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w)) =
    littlePeriodicCAlphaTorusTranslate h (W (balancedQuadraticSecondForcing hα i j v w))
  rw [balancedQuadraticSecondForcing_translate hα i j h v w, hW]

/-- Actual first Q equivariance from just the actual two inverse identities.
The imported PDE uniqueness interface proves W equivariance; none is assumed. -/
theorem balancedQuadraticFirst_translate_of_inverse {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (i : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticFirst W hα i (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticFirst W hα i v w) :=
  balancedQuadraticFirst_translate W
    (littlePeriodic_shiftedLaplacian_inverse_translate hα W hWL hLW) hα i h v w

/-- Actual second Q equivariance from just the actual two inverse identities. -/
theorem balancedQuadraticSecond_translate_of_inverse {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (W : LittlePeriodicCAlphaFunction a 1 0 α →L[ℝ] LittlePeriodicCAlphaFunction a 1 2 α)
    (hWL : ∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u)
    (hLW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f)
    (i j : Fin a) (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticSecond W hα i j (littlePeriodicCAlphaTorusTranslate h v)
      (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticSecond W hα i j v w) :=
  balancedQuadraticSecond_translate W
    (littlePeriodic_shiftedLaplacian_inverse_translate hα W hWL hLW) hα i j h v w

#print axioms balancedQuadraticFirst_translate_of_inverse
#print axioms balancedQuadraticSecond_translate_of_inverse

end GlobalEmbedding.Paper
