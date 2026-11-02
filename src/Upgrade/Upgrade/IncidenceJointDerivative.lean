import Upgrade.IncidencePerturbation

/-!
# The full native derivative of the two-point incidence map

The parameter and first-source columns are columns of one and the same joint
derivative. Both source charts are retained. The vectors depending on the fast
angles are inserted only after that derivative has been taken.
-/

noncomputable section

namespace GlobalEmbedding.Upgrade

variable {P X Y W T R V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Parameter columns in the actual full derivative, with both endpoints fixed. -/
theorem fderiv_joint_parameter_column (J : P × (X × Y) → W)
    (u : P) (x : X) (y : Y) (hJ : DifferentiableAt ℝ J (u, x, y)) (d : P) :
    fderiv ℝ J (u, x, y) (d, 0, 0) =
      fderiv ℝ (fun w ↦ J (w, x, y)) u d := by
  have hi : HasFDerivAt (fun w : P ↦ (w, x, y))
      ((ContinuousLinearMap.id ℝ P).prod 0) u :=
    (hasFDerivAt_id u).prodMk (hasFDerivAt_const (x, y) u)
  have h := hJ.hasFDerivAt.comp u hi
  simpa [Function.comp_def, Prod.zero_eq_mk] using (congrArg (fun L ↦ L d) h.fderiv).symm

/-- First-source columns in the same full derivative. -/
theorem fderiv_joint_first_source_column (J : P × (X × Y) → W)
    (u : P) (x : X) (y : Y) (hJ : DifferentiableAt ℝ J (u, x, y)) (v : X) :
    fderiv ℝ J (u, x, y) (0, v, 0) =
      fderiv ℝ (fun z ↦ J (u, z, y)) x v := by
  have hi : HasFDerivAt (fun z : X ↦ (u, z, y))
      ((0 : X →L[ℝ] P).prod ((ContinuousLinearMap.id ℝ X).prod 0)) x :=
    (hasFDerivAt_const u x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  have h := hJ.hasFDerivAt.comp x hi
  simpa [Function.comp_def] using (congrArg (fun L ↦ L v) h.fderiv).symm

/-- Second-source columns are also literal columns of the same derivative. -/
theorem fderiv_joint_second_source_column (J : P × (X × Y) → W)
    (u : P) (x : X) (y : Y) (hJ : DifferentiableAt ℝ J (u, x, y)) (v : Y) :
    fderiv ℝ J (u, x, y) (0, 0, v) =
      fderiv ℝ (fun z ↦ J (u, x, z)) y v := by
  have hi : HasFDerivAt (fun z : Y ↦ (u, x, z))
      ((0 : Y →L[ℝ] P).prod ((0 : Y →L[ℝ] X).prod (ContinuousLinearMap.id ℝ Y))) y :=
    (hasFDerivAt_const u y).prodMk
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))
  have h := hJ.hasFDerivAt.comp y hi
  simpa [Function.comp_def] using (congrArg (fun L ↦ L v) h.fderiv).symm

/-- The original normalized incidence equation on the product of parameter
space and two possibly different source charts. -/
def jointScaledIncidence (B : P → X → T) (F : P → X → V) (H : P → Y → V)
    (equation : T → R) (sigma a : ℝ) (z : P × (X × Y)) : R × V :=
  scaledIncidence B F H equation sigma a z.1 z.2.1 z.2.2

/-- No separate rank hypothesis is hidden in the passage from a parameter
response to the full incidence derivative. -/
theorem jointScaledIncidence_parameter_column
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y) (d : P)
    (hJ : DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)) :
    fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y) (d, 0, 0) =
      fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u d :=
  fderiv_joint_parameter_column _ u x y hJ d

/-- The actual first-source column has the small Schur/equation component
`a / sigma`, including derivatives of the changing source frame. -/
theorem jointScaledIncidence_source_column
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (ha : a ≠ 0) (u : P) (x : X) (y : Y) (v : X)
    (hJ : DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y))
    (hB : DifferentiableAt ℝ (B u) x)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hF : DifferentiableAt ℝ (F u) x) :
    fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y) (0, a • v, 0) =
      ((a / sigma) • fderiv ℝ equation (B u x) (fderiv ℝ (B u) x v),
        fderiv ℝ (F u) x v) := by
  rw [fderiv_joint_first_source_column _ u x y hJ]
  exact scaledIncidence_source_column B F H equation sigma a ha u x y v hB hR hF

/-- Injectivity and incidence zeros are not altered by the two nonzero
normalizing factors. This applies equally to Schur and supported equations. -/
theorem jointScaledIncidence_eq_zero_iff
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (hsigma : sigma ≠ 0) (ha : a ≠ 0) (z : P × (X × Y)) :
    jointScaledIncidence B F H equation sigma a z = 0 ↔
      equation (B z.1 z.2.1) = 0 ∧ F z.1 z.2.1 = H z.1 z.2.2 := by
  simp [jointScaledIncidence, scaledIncidence, Prod.ext_iff, hsigma, ha, sub_eq_zero]

end GlobalEmbedding.Upgrade
