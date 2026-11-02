import GlobalEmbedding.Paper.BalancedQuadraticDataOperator
import GlobalEmbedding.Paper.BalancedQuadraticTranslation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTorusTranslateLift

/-!
# Actual translation of the whole-function balanced data operator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines384–418.
DAG node: `balanced-quadratic-data-translation`.
-/

namespace GlobalEmbedding.Paper

/-- Actual coordinate translation identities imply the actual assembled identity.
Choose a Euclidean representative of the torus shift and use original lift injectivity.
The unique existing finite data enumeration and exact whole-function coordinate formula
reduce the two lifted data values to the corresponding actual scalar coordinate identity.
This implication is only the finite assembly step; the final scalar identities are
supplied by the separately proved actual scalar Q translation theorems.
Source: Qcal fiber-origin independence in the proof of `lem:balanced`. -/
theorem balancedQuadraticDataOperator_translate_of_components
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α)
    (hc : ∀ r : BalancedPairingIndex a,
      balancedQuadraticDataComponent hα0 hα1 r
          (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w) =
        littlePeriodicCAlphaTorusTranslate h (balancedQuadraticDataComponent hα0 hα1 r v w)) :
    balancedQuadraticDataOperator hα0 hα1
        (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticDataOperator hα0 hα1 v w) := by
  obtain ⟨t, rfl⟩ := periodic_flat_torus_projection.surjective h
  simp only [littlePeriodicCAlphaTorusTranslate_lift] at hc ⊢
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  apply PiLp.ext
  intro j
  obtain ⟨r, rfl⟩ := (Fintype.equivFin (BalancedPairingIndex a)).surjective j
  change (balancedQuadraticDataOperator hα0 hα1
      (littlePeriodicCAlphaTranslateIsometry t v)
      (littlePeriodicCAlphaTranslateIsometry t w)).val.toFun x
        (Fintype.equivFin (BalancedPairingIndex a) r) =
    (balancedQuadraticDataOperator hα0 hα1 v w).val.toFun (x + t)
      (Fintype.equivFin (BalancedPairingIndex a) r)
  rw [balancedQuadraticDataOperator_coordinate, balancedQuadraticDataOperator_coordinate]
  exact congrArg (fun f : LittlePeriodicCAlphaFunction a 1 2 α ↦ f.val.toFun x 0) (hc r)

/-- The actual assembled whole-function Qcal commutes with every torus shift.
Apply coordinate injectivity, split the unique first/once-indexed-second data type,
and use the actual scalar Q translation theorems with the actual canonical PDE
inverse and its proved two-sided inverse identities. Translation linearity moves
the literal −1 and 1/2 factors. No inverse or equivariance hypothesis is assumed.
Source: Qcal fiber-origin independence in `lem:balanced`. -/
theorem balancedQuadraticDataOperator_translate
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h : PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))
    (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDataOperator hα0 hα1
        (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h (balancedQuadraticDataOperator hα0 hα1 v w) := by
  apply balancedQuadraticDataOperator_translate_of_components hα0 hα1 h v w
  intro r
  cases r with
  | inl i =>
    change (-1 : ℝ) • balancedQuadraticFirst
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le i
        (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h ((-1 : ℝ) • balancedQuadraticFirst
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le i v w)
    rw [balancedQuadraticFirst_translate_of_inverse hα1.le _
      (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
      (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1), map_smul]
  | inr ij =>
    change (1 / 2 : ℝ) • balancedQuadraticSecond
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le ij.val.1 ij.val.2
        (littlePeriodicCAlphaTorusTranslate h v) (littlePeriodicCAlphaTorusTranslate h w) =
      littlePeriodicCAlphaTorusTranslate h ((1 / 2 : ℝ) • balancedQuadraticSecond
        (littlePeriodicCAlphaShiftedLaplacianInverse hα0 hα1) hα1.le ij.val.1 ij.val.2 v w)
    rw [balancedQuadraticSecond_translate_of_inverse hα1.le _
      (littlePeriodicCAlphaShiftedLaplacianInverse_left hα0 hα1)
      (littlePeriodicCAlphaShiftedLaplacianInverse_right hα0 hα1), map_smul]

/-- Every Euclidean representative gives the same actual Qcal transport identity.
Specialize torus equivariance to the projected shift and use the true every-lift
translation formula on both input and output original little spaces.
Source: Qcal transport between local fiber origins in `lem:balanced`. -/
theorem balancedQuadraticDataOperator_translate_euclidean
    {a N : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (t : EuclideanSpace ℝ (Fin a)) (v w : LittlePeriodicCAlphaFunction a N 2 α) :
    balancedQuadraticDataOperator hα0 hα1
        (littlePeriodicCAlphaTranslateIsometry t v) (littlePeriodicCAlphaTranslateIsometry t w) =
      littlePeriodicCAlphaTranslateIsometry t (balancedQuadraticDataOperator hα0 hα1 v w) := by
  simpa only [littlePeriodicCAlphaTorusTranslate_lift] using
    balancedQuadraticDataOperator_translate hα0 hα1
      (WithLp.toLp 2 (fun i : Fin a ↦ (t i : AddCircle (1 : ℝ)))) v w

#print axioms balancedQuadraticDataOperator_translate_of_components
#print axioms balancedQuadraticDataOperator_translate
#print axioms balancedQuadraticDataOperator_translate_euclidean

end GlobalEmbedding.Paper
