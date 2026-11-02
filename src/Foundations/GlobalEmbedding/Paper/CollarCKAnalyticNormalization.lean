import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual analytic normalization of the first-order CK data

Source: Gantumur, `notes2.pdf`, Theorem 18 (printed p. 9), and Corollary 20.
Translate the initial point, subtract the actual analytic initial function, and then subtract
the normal linear term with the constant coefficient given by the original initial RHS.
The original nested product, Euclidean spatial directions and native Fréchet derivative are used.
This module neither assumes nor constructs a CK solution or a collar.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {n m : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "V" => (Fin m → ℝ)
local notation "P" => (Fin n → Fin m → ℝ)
local notation "D" => (X × ℝ × V × P)

/-- The actual spatial first jet of the initial datum, in the original CK coordinate directions.
Source: Gantumur, Corollary 20, reduction to zero analytic initial data. -/
def collarCKInitialSpatialJet (v₀ : X → V) (x : X) : P :=
  fun i ↦ fderiv ℝ v₀ x (EuclideanSpace.single i 1)

/-- The constant normal linear coefficient is the original RHS at the actual initial jet.
Source: Gantumur, Theorem 18, normalization before the coefficient recursion. -/
def collarCKInitialRHS (G : D → V) (v₀ : X → V) (x₀ : X) : V :=
  G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)

/-- The normalized actual analytic RHS; no normalized map is an extra input.
Source: Gantumur, Theorem 18 and Corollary 20. -/
def collarCKNormalizedRHS (G : D → V) (v₀ : X → V) (x₀ : X) : D → V :=
  fun z ↦ G (x₀ + z.1, z.2.1,
    z.2.2.1 + v₀ (x₀ + z.1) + z.2.1 • collarCKInitialRHS G v₀ x₀,
    z.2.2.2 + collarCKInitialSpatialJet v₀ (x₀ + z.1)) -
      collarCKInitialRHS G v₀ x₀

/-- Analytic initial data have an analytic actual spatial jet.
Source: the initial-data reduction in Gantumur, Corollary 20.
Apply native analyticity of the Fréchet derivative, compose with bounded evaluation at each
fixed Euclidean basis vector, and assemble the finitely many coordinates. -/
theorem collarCKInitialSpatialJet_analyticAt (v₀ : X → V) (x₀ : X)
    (hv₀ : AnalyticAt ℝ v₀ x₀) :
    AnalyticAt ℝ (collarCKInitialSpatialJet v₀) x₀ := by
  apply AnalyticAt.pi
  intro i
  exact ((ContinuousLinearMap.apply ℝ V (EuclideanSpace.single i 1)).analyticAt _).comp
    hv₀.fderiv

/-- Normalization preserves actual analyticity and makes the actual RHS vanish at the origin.
Source: Gantumur, Theorem 18, normalization, and Corollary 20.
The spatial jet is analytic by the preceding theorem. Compose translated initial data and its
jet with coordinate projections, add the unknown, jet, and constant normal linear term, and
compose with the original analytic RHS. The inserted zero point is the original initial jet,
so subtracting its actual RHS gives zero. No solution or vanishing original jet is assumed. -/
theorem collarCKNormalizedRHS_analyticAt (G : D → V) (v₀ : X → V) (x₀ : X)
    (hv₀ : AnalyticAt ℝ v₀ x₀)
    (hG : AnalyticAt ℝ G (x₀, 0, v₀ x₀, collarCKInitialSpatialJet v₀ x₀)) :
    AnalyticAt ℝ (collarCKNormalizedRHS G v₀ x₀) 0 ∧
      collarCKNormalizedRHS G v₀ x₀ 0 = 0 := by
  have hx : AnalyticAt ℝ (fun z : D ↦ x₀ + z.1) 0 :=
    analyticAt_const.add analyticAt_fst
  have hr : AnalyticAt ℝ (fun z : D ↦ z.2.1) 0 :=
    analyticAt_fst.comp analyticAt_snd
  have hw : AnalyticAt ℝ (fun z : D ↦ z.2.2.1) 0 :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hp : AnalyticAt ℝ (fun z : D ↦ z.2.2.2) 0 :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  have hv := hv₀.comp_of_eq hx (by simp)
  have hJ := (collarCKInitialSpatialJet_analyticAt v₀ x₀ hv₀).comp_of_eq hx (by simp)
  have hin : AnalyticAt ℝ (fun z : D ↦ (x₀ + z.1, z.2.1,
      z.2.2.1 + v₀ (x₀ + z.1) + z.2.1 • collarCKInitialRHS G v₀ x₀,
      z.2.2.2 + collarCKInitialSpatialJet v₀ (x₀ + z.1))) 0 :=
    hx.prod (hr.prod ((hw.add hv |>.add (hr.smul analyticAt_const)).prod (hp.add hJ)))
  refine ⟨?_, ?_⟩
  · exact (hG.comp_of_eq hin (by simp)).sub analyticAt_const
  · simp [collarCKNormalizedRHS, collarCKInitialRHS]

/-- Normalize an actual candidate unknown, including the constant normal linear correction.
Source: Gantumur, Theorem 18 and Corollary 20. -/
def collarCKNormalizeUnknown (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) : ℝ × X → V :=
  fun z ↦ u (z.1, x₀ + z.2) - v₀ (x₀ + z.2) -
    z.1 • collarCKInitialRHS G v₀ x₀

/-- Restore an actual unknown from normalized coordinates.
Source: Gantumur, Theorem 18 and Corollary 20. -/
def collarCKRestoreUnknown (G : D → V) (v₀ : X → V) (x₀ : X)
    (w : ℝ × X → V) : ℝ × X → V :=
  fun z ↦ w (z.1, z.2 - x₀) + v₀ z.2 + z.1 • collarCKInitialRHS G v₀ x₀

/-- The actual transformations are inverse, by translation and additive cancellation.
Source: Gantumur, initial-data normalization. -/
theorem collarCKRestoreUnknown_normalize (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) :
    collarCKRestoreUnknown G v₀ x₀ (collarCKNormalizeUnknown G v₀ x₀ u) = u := by
  funext z
  simp [collarCKRestoreUnknown, collarCKNormalizeUnknown]
  abel

/-- The reverse actual transformation is also an inverse, by the same cancellation.
Source: Gantumur, initial-data normalization. -/
theorem collarCKNormalizeUnknown_restore (G : D → V) (v₀ : X → V) (x₀ : X)
    (w : ℝ × X → V) :
    collarCKNormalizeUnknown G v₀ x₀ (collarCKRestoreUnknown G v₀ x₀ w) = w := by
  funext z
  simp [collarCKRestoreUnknown, collarCKNormalizeUnknown, add_sub_cancel_left]
  abel

/-- Zero initial values in normalized coordinates mean precisely the original initial values.
Source: Gantumur, Corollary 20. At normal coordinate zero the linear correction vanishes. -/
theorem collarCKNormalizeUnknown_initial_iff (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) (y : X) :
    collarCKNormalizeUnknown G v₀ x₀ u (0, y) = 0 ↔
      u (0, x₀ + y) = v₀ (x₀ + y) := by
  simp [collarCKNormalizeUnknown, sub_eq_zero]

/-- Normalizing an analytic candidate preserves actual joint analyticity.
Source: Gantumur, initial-data reduction. Compose with the affine spatial translation and
subtract the analytic initial datum and constant normal linear term. -/
theorem collarCKNormalizeUnknown_analyticAt (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) (r : ℝ) (y : X)
    (hu : AnalyticAt ℝ u (r, x₀ + y)) (hv₀ : AnalyticAt ℝ v₀ (x₀ + y)) :
    AnalyticAt ℝ (collarCKNormalizeUnknown G v₀ x₀ u) (r, y) := by
  have hx : AnalyticAt ℝ (fun z : ℝ × X ↦ x₀ + z.2) (r, y) :=
    analyticAt_const.add analyticAt_snd
  exact ((hu.comp_of_eq (analyticAt_fst.prod hx) rfl).sub
    (hv₀.comp_of_eq hx rfl)).sub
    (analyticAt_fst.smul analyticAt_const)

/-- Restoring an analytic normalized candidate preserves actual joint analyticity.
Source: Gantumur, initial-data reduction. Translate back and add the same analytic terms. -/
theorem collarCKRestoreUnknown_analyticAt (G : D → V) (v₀ : X → V) (x₀ : X)
    (w : ℝ × X → V) (r : ℝ) (x : X)
    (hw : AnalyticAt ℝ w (r, x - x₀)) (hv₀ : AnalyticAt ℝ v₀ x) :
    AnalyticAt ℝ (collarCKRestoreUnknown G v₀ x₀ w) (r, x) := by
  have hx : AnalyticAt ℝ (fun z : ℝ × X ↦ z.2 - x₀) (r, x) :=
    analyticAt_snd.sub analyticAt_const
  exact ((hw.comp_of_eq (analyticAt_fst.prod hx) rfl).add
    (hv₀.comp analyticAt_snd)).add
    (analyticAt_fst.smul analyticAt_const)

/-- The actual joint derivative under normalization, with the constant normal correction.
Source: Gantumur, Theorem 18 and Corollary 20. The affine translation has identity derivative;
the initial datum contributes only its spatial derivative, and `r*b` contributes only in
the normal direction. Apply the native chain, subtraction and scalar product rules. -/
theorem collarCKNormalizeUnknown_hasFDerivAt (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) (r : ℝ) (y : X)
    (hu : DifferentiableAt ℝ u (r, x₀ + y))
    (hv₀ : DifferentiableAt ℝ v₀ (x₀ + y)) :
    HasFDerivAt (collarCKNormalizeUnknown G v₀ x₀ u)
      (fderiv ℝ u (r, x₀ + y) -
        (fderiv ℝ v₀ (x₀ + y)).comp (ContinuousLinearMap.snd ℝ ℝ X) -
        (ContinuousLinearMap.fst ℝ ℝ X).smulRight (collarCKInitialRHS G v₀ x₀)) (r, y) := by
  have ht : HasFDerivAt (fun z : ℝ × X ↦ (z.1, x₀ + z.2))
      (ContinuousLinearMap.id ℝ (ℝ × X)) (r, y) := by
    simpa [Prod.add_def] using (hasFDerivAt_id (r, y)).const_add (0, x₀)
  have hs : HasFDerivAt (fun z : ℝ × X ↦ x₀ + z.2)
      (ContinuousLinearMap.snd ℝ ℝ X) (r, y) :=
    hasFDerivAt_snd.const_add x₀
  have hv := hv₀.hasFDerivAt.comp (r, y) hs
  simpa [collarCKNormalizeUnknown] using
    ((hu.hasFDerivAt.comp (r, y) ht).sub hv).sub
      (hasFDerivAt_fst.smul_const (collarCKInitialRHS G v₀ x₀))

/-- Actual normal and all spatial derivative identities of the normalized unknown.
Source: Gantumur, initial-data normalization. Evaluate the joint derivative above on the literal
normal direction and each original Euclidean spatial basis direction. -/
theorem collarCKNormalizeUnknown_derivatives (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) (r : ℝ) (y : X)
    (hu : DifferentiableAt ℝ u (r, x₀ + y))
    (hv₀ : DifferentiableAt ℝ v₀ (x₀ + y)) :
    fderiv ℝ (collarCKNormalizeUnknown G v₀ x₀ u) (r, y) (1, 0) =
      fderiv ℝ u (r, x₀ + y) (1, 0) - collarCKInitialRHS G v₀ x₀ ∧
    ∀ i, fderiv ℝ (collarCKNormalizeUnknown G v₀ x₀ u) (r, y)
        (0, EuclideanSpace.single i 1) =
      fderiv ℝ u (r, x₀ + y) (0, EuclideanSpace.single i 1) -
        collarCKInitialSpatialJet v₀ (x₀ + y) i := by
  rw [(collarCKNormalizeUnknown_hasFDerivAt G v₀ x₀ u r y hu hv₀).fderiv]
  simp [collarCKInitialSpatialJet]

/-- The original PDE at a point is exactly the normalized PDE at the translated point.
Source: Gantumur, Theorem 18 and Corollary 20. Substitute the actual value and derivative
identities into the literal normalized RHS; spatial initial jets cancel, and the same constant
is subtracted from both sides of the normal equation. Differentiability is needed only to
state this transformation for a candidate, not supplied as a desired CK solution. -/
theorem collarCKNormalizeUnknown_equation_iff (G : D → V) (v₀ : X → V) (x₀ : X)
    (u : ℝ × X → V) (r : ℝ) (y : X)
    (hu : DifferentiableAt ℝ u (r, x₀ + y))
    (hv₀ : DifferentiableAt ℝ v₀ (x₀ + y)) :
    let w := collarCKNormalizeUnknown G v₀ x₀ u
    (fderiv ℝ w (r, y) (1, 0) = collarCKNormalizedRHS G v₀ x₀
      (y, r, w (r, y), fun i ↦ fderiv ℝ w (r, y) (0, EuclideanSpace.single i 1))) ↔
    (fderiv ℝ u (r, x₀ + y) (1, 0) = G (x₀ + y, r, u (r, x₀ + y),
      fun i ↦ fderiv ℝ u (r, x₀ + y) (0, EuclideanSpace.single i 1))) := by
  dsimp only
  obtain ⟨hr, hx⟩ := collarCKNormalizeUnknown_derivatives G v₀ x₀ u r y hu hv₀
  rw [hr]
  have hjet : (fun i ↦ fderiv ℝ (collarCKNormalizeUnknown G v₀ x₀ u) (r, y)
      (0, EuclideanSpace.single i 1)) + collarCKInitialSpatialJet v₀ (x₀ + y) =
      (fun i ↦ fderiv ℝ u (r, x₀ + y) (0, EuclideanSpace.single i 1)) := by
    funext i
    simp [hx i]
  have hvalue : collarCKNormalizeUnknown G v₀ x₀ u (r, y) + v₀ (x₀ + y) +
      r • collarCKInitialRHS G v₀ x₀ = u (r, x₀ + y) := by
    dsimp [collarCKNormalizeUnknown]
    abel
  change _ = G (x₀ + y, r, _, _) - _ ↔ _
  rw [hjet, hvalue, sub_left_inj]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKInitialSpatialJet
#print axioms GlobalEmbedding.Paper.collarCKInitialRHS
#print axioms GlobalEmbedding.Paper.collarCKNormalizedRHS
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown
#print axioms GlobalEmbedding.Paper.collarCKRestoreUnknown
#print axioms GlobalEmbedding.Paper.collarCKInitialSpatialJet_analyticAt
#print axioms GlobalEmbedding.Paper.collarCKNormalizedRHS_analyticAt
#print axioms GlobalEmbedding.Paper.collarCKRestoreUnknown_normalize
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_restore
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_initial_iff
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_analyticAt
#print axioms GlobalEmbedding.Paper.collarCKRestoreUnknown_analyticAt
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_hasFDerivAt
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_derivatives
#print axioms GlobalEmbedding.Paper.collarCKNormalizeUnknown_equation_iff
