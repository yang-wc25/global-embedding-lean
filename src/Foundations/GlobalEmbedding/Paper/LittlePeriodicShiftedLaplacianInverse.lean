import GlobalEmbedding.Paper.BalancedInverseShiftedAprioriEstimate
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverseFromEstimate
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianInverseSmooth

/-!
# The actual bounded inverse of the original periodic shifted Laplacian

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines382–386.
DAG node: `balanced-inverse`.

The genuine shifted Schauder estimate discharges the actual estimate-to-inverse theorem.
The resulting inverse acts on the original little spaces, in every finite real source
and target dimension. Its translation, smoothness and all derivative properties follow
from the actual inverse identities and the genuine smooth periodic PDE construction.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual shifted Laplacian has a bounded two-sided inverse on the original little
spaces, with a constant uniform in the forcing. Apply the genuine ambient shifted estimate
to each actual little2 u and its actual image Lu; the exact lift formula supplies the PDE.
The proved dense-range and closed-range construction then gives the actual inverse.
Source: periodic Schauder inverse in the proof of `lem:balanced`. -/
theorem littlePeriodic_shiftedLaplacian_inverse_exists
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 α,
      (∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα1.le u) = u) ∧
      (∀ f, littlePeriodicCAlphaShiftedLaplacian hα1.le (W f) = f) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖W f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hest⟩ := periodicCAlpha_shifted_apriori_estimate (a := a) (N := N) hα0 hα1
  have hb (u : LittlePeriodicCAlphaFunction a N 2 α) :
      ‖u‖ ≤ C * ‖littlePeriodicCAlphaShiftedLaplacian hα1.le u‖ :=
    hest u.val (littlePeriodicCAlphaShiftedLaplacian hα1.le u).val
      (fun x ↦ (littlePeriodicCAlphaShiftedLaplacian_lift hα1.le u x).symm)
  obtain ⟨W, hWL, hLW, hWb, _, _⟩ :=
    littlePeriodic_shiftedLaplacian_inverse_of_estimate hα1.le C hC hb
  exact ⟨W, hWL, hLW, C, hC, hWb⟩

/-- The actual original periodic inverse W=L⁻¹, chosen from the fully proved existence
of a bounded two-sided inverse. The chosen data come from proved existence; no PDE
solvability is postulated. Source: `lem:balanced`, proof line384. -/
noncomputable def littlePeriodicCAlphaShiftedLaplacianInverse
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    LittlePeriodicCAlphaFunction a N 0 α →L[ℝ] LittlePeriodicCAlphaFunction a N 2 α :=
  (littlePeriodic_shiftedLaplacian_inverse_exists (a := a) (N := N) hα0 hα1).choose

/-- W is the actual left inverse of L. Source: `lem:balanced`, periodic inverse. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_left
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (u : LittlePeriodicCAlphaFunction a N 2 α) :
    littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1
      (littlePeriodicCAlphaShiftedLaplacian hα1.le u) = u :=
  (littlePeriodic_shiftedLaplacian_inverse_exists (a := a) (N := N) hα0 hα1).choose_spec.1 u

/-- W is the actual right inverse of L. Source: `lem:balanced`, periodic inverse. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_right
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) :
    littlePeriodicCAlphaShiftedLaplacian hα1.le
      (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f) = f :=
  (littlePeriodic_shiftedLaplacian_inverse_exists (a := a) (N := N) hα0 hα1).choose_spec.2.1 f

/-- The actual inverse gains two derivatives with a constant depending only on the
fixed dimensions and exponent. The constant precedes all forcings.
Source: periodic Schauder bound in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_bound
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : LittlePeriodicCAlphaFunction a N 0 α,
      ‖littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f‖ ≤ C * ‖f‖ :=
  (littlePeriodic_shiftedLaplacian_inverse_exists (a := a) (N := N) hα0 hα1).choose_spec.2.2

/-- Each actual little forcing has a unique actual little2 solution.
The right inverse gives existence; applying the left inverse identifies any solution.
Source: unique periodic shifted solution in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_unique_solution
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) :
    ∃! u : LittlePeriodicCAlphaFunction a N 2 α,
      littlePeriodicCAlphaShiftedLaplacian hα1.le u = f := by
  refine ⟨littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f,
    littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1 f, ?_⟩
  intro u hu
  rw [← littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1 u, hu]

/-- Any actual right inverse equals the constructed inverse, with no additional norm
or smoothness assumption on it. Source: uniqueness in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_unique
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N 2 α)
    (hW : ∀ f, littlePeriodicCAlphaShiftedLaplacian hα1.le (W f) = f) :
    W = littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 := by
  ext f
  rw [← littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1 (W f), hW]

/-- The actual constructed inverse commutes with every actual torus translation.
Apply the proved inverse translation theorem to its actual inverse identities.
Source: independence of fiber origins in `lem:balanced`, proof line385. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_translate
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (f : LittlePeriodicCAlphaFunction a N 0 α) :
    littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1
        (littlePeriodicCAlphaTorusTranslate h f) =
      littlePeriodicCAlphaTorusTranslate h
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f) :=
  littlePeriodic_shiftedLaplacian_inverse_translate hα1.le _
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1) h f

/-- The actual constructed inverse maps genuinely smooth lifts to genuinely smooth lifts.
Its true left inverse and the actual smooth PDE preimage prove this property.
Source: smooth periodic inverse in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_smooth
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun) :
    ContDiff ℝ ∞ (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f).val.toFun :=
  littlePeriodic_shiftedLaplacian_inverse_smooth hα1.le _
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1) f hf

/-- The actual constructed inverse commutes with arbitrary directional differentiation
on smooth lifts, for any actual little representative of the forcing derivative.
Source: all smooth derivatives in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_directional
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (v : EuclideanSpace ℝ (Fin a)) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = fun x ↦ fderiv ℝ f.val.toFun x v) :
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 g).val.toFun =
      fun x ↦ fderiv ℝ (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f).val.toFun x v :=
  littlePeriodic_shiftedLaplacian_inverse_directional hα1.le _
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1) f hf v g hg

/-- The actual constructed inverse commutes with every finite coordinate-word derivative
on smooth lifts. Source: all smooth derivatives in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_word
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (word : List (Fin a)) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = euclideanCoordinateWordDerivative word f.val.toFun) :
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 g).val.toFun =
      euclideanCoordinateWordDerivative word
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f).val.toFun :=
  littlePeriodic_shiftedLaplacian_inverse_word hα1.le _
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1) f hf word g hg

/-- The actual constructed inverse commutes with every genuine Finsupp multiindex
coordinate derivative on smooth lifts, without a degree bound.
Source: all smooth derivatives in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlphaShiftedLaplacianInverse_multiindex
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun)
    (β : Fin a →₀ ℕ) (g : LittlePeriodicCAlphaFunction a N 0 α)
    (hg : g.val.toFun = euclideanCoordinateMultiindexDerivative β f.val.toFun) :
    (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 g).val.toFun =
      euclideanCoordinateMultiindexDerivative β
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1 f).val.toFun :=
  littlePeriodic_shiftedLaplacian_inverse_multiindex hα1.le _
    (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
    (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1) f hf β g hg

#print axioms littlePeriodic_shiftedLaplacian_inverse_exists
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_left
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_right
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_bound
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_unique_solution
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_unique
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_translate
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_smooth
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_directional
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_word
#print axioms littlePeriodicCAlphaShiftedLaplacianInverse_multiindex

end GlobalEmbedding.Paper
