import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# The actual inverse of a shift along a real action

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, line261.
The inverse is constructed from the unique zero of the actual scalar orbit lift.
No global inverse or normalized final map is supplied as an assumption.
-/

namespace GlobalEmbedding.Paper

/-- The genuine scalar lift of the orbit shift `z ↦ R (h z) z`. -/
def planarOrbitShiftLift {Q : Type*} (R : ℝ → Q → Q) (h : Q → ℝ) (z : Q) : ℝ → ℝ :=
  fun t ↦ t + h (R t z)

/-- The actual scalar lift as an order isomorphism, once its strict monotonicity
and surjectivity have been proved. -/
noncomputable def planarOrbitShiftLiftIso {Q : Type*} (R : ℝ → Q → Q) (h : Q → ℝ)
    (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) (z : Q) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (hmono z) (hsurj z)

/-- The root defining the genuine inverse orbit shift. -/
noncomputable def planarOrbitShiftRoot {Q : Type*} (R : ℝ → Q → Q) (h : Q → ℝ)
    (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) (z : Q) : ℝ :=
  (planarOrbitShiftLiftIso R h hmono hsurj z).symm 0

/-- The selected scalar root solves its literal orbit-shift equation. -/
theorem planarOrbitShiftRoot_spec {Q : Type*} (R : ℝ → Q → Q) (h : Q → ℝ)
    (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) (z : Q) :
    planarOrbitShiftRoot R h hmono hsurj z +
      h (R (planarOrbitShiftRoot R h hmono hsurj z) z) = 0 :=
  (planarOrbitShiftLiftIso R h hmono hsurj z).apply_symm_apply 0

/-- The actual global equivalence of an orbit shift, constructed by solving
its genuine scalar equation. The action laws and scalar root uniqueness prove
both inverse identities, without any freeness or compactness assumption. -/
noncomputable def planarOrbitShiftEquiv {Q : Type*} (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (h : Q → ℝ) (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) : Q ≃ Q where
  toFun z := R (h z) z
  invFun z := R (planarOrbitShiftRoot R h hmono hsurj z) z
  left_inv z := by
    have ht : planarOrbitShiftLift R h (R (h z) z) (-h z) = 0 := by
      simp only [planarOrbitShiftLift, ← hadd, neg_add_cancel, hzero, neg_add_cancel]
    have he : planarOrbitShiftRoot R h hmono hsurj (R (h z) z) = -h z := by
      apply (hmono (R (h z) z)).injective
      exact (planarOrbitShiftRoot_spec R h hmono hsurj (R (h z) z)).trans ht.symm
    change R (planarOrbitShiftRoot R h hmono hsurj (R (h z) z)) (R (h z) z) = z
    rw [he, ← hadd, neg_add_cancel, hzero]
  right_inv z := by
    change R (h (R (planarOrbitShiftRoot R h hmono hsurj z) z))
      (R (planarOrbitShiftRoot R h hmono hsurj z) z) = z
    rw [← hadd, add_comm]
    rw [planarOrbitShiftRoot_spec R h hmono hsurj, hzero]

/-- The inverse on a whole orbit is evaluation of the actual scalar inverse,
followed by the actual action. This is the formula used to differentiate the
normalized map and prove orbit analyticity. -/
theorem planarOrbitShiftEquiv_symm_orbit {Q : Type*} (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (h : Q → ℝ) (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) (z : Q) (s : ℝ) :
    (planarOrbitShiftEquiv R hzero hadd h hmono hsurj).symm (R s z) =
      R ((planarOrbitShiftLiftIso R h hmono hsurj z).symm s) z := by
  apply (planarOrbitShiftEquiv R hzero hadd h hmono hsurj).injective
  rw [Equiv.apply_symm_apply]
  change R s z = R (h (R _ z)) (R _ z)
  rw [← hadd, add_comm]
  exact congrArg (fun t ↦ R t z)
    ((planarOrbitShiftLiftIso R h hmono hsurj z).apply_symm_apply s).symm

/-- Half-period invariance of h implies that the actual inverse commutes with
half-period action. The period is represented literally by the real number1/2. -/
theorem planarOrbitShiftEquiv_symm_half {Q : Type*} (R : ℝ → Q → Q)
    (hzero : ∀ z, R 0 z = z) (hadd : ∀ s t z, R (s + t) z = R s (R t z))
    (h : Q → ℝ) (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z))
    (hhalf : ∀ z, h (R (1 / 2 : ℝ) z) = h z) (z : Q) :
    (planarOrbitShiftEquiv R hzero hadd h hmono hsurj).symm (R (1 / 2 : ℝ) z) =
      R (1 / 2 : ℝ) ((planarOrbitShiftEquiv R hzero hadd h hmono hsurj).symm z) := by
  let e := planarOrbitShiftEquiv R hzero hadd h hmono hsurj
  have hc (y : Q) : e (R (1 / 2 : ℝ) y) = R (1 / 2 : ℝ) (e y) := by
    change R (h (R (1 / 2 : ℝ) y)) (R (1 / 2 : ℝ) y) =
      R (1 / 2 : ℝ) (R (h y) y)
    rw [hhalf, ← hadd, ← hadd, add_comm (h y)]
  apply e.injective
  rw [e.apply_symm_apply, hc, e.apply_symm_apply]

/-- The genuine scalar orbit inverse is analytic wherever the actual orbit
lift is analytic with nonzero derivative. Native analytic inverse-function
calculus applies to the identity inverse∘lift; no analytic inverse is assumed. -/
theorem planarOrbitShiftLiftIso_symm_analyticAt {Q : Type*} (R : ℝ → Q → Q)
    (h : Q → ℝ) (hmono : ∀ z, StrictMono (planarOrbitShiftLift R h z))
    (hsurj : ∀ z, Function.Surjective (planarOrbitShiftLift R h z)) (z : Q) (s : ℝ)
    (ha : AnalyticAt ℝ (planarOrbitShiftLift R h z)
      ((planarOrbitShiftLiftIso R h hmono hsurj z).symm s))
    (hd : deriv (planarOrbitShiftLift R h z)
      ((planarOrbitShiftLiftIso R h hmono hsurj z).symm s) ≠ 0) :
    AnalyticAt ℝ (planarOrbitShiftLiftIso R h hmono hsurj z).symm s := by
  let e := planarOrbitShiftLiftIso R h hmono hsurj z
  have he : (e.symm : ℝ → ℝ) ∘ planarOrbitShiftLift R h z = id := by
    funext t
    exact e.symm_apply_apply t
  have hac : AnalyticAt ℝ ((e.symm : ℝ → ℝ) ∘ planarOrbitShiftLift R h z) (e.symm s) := by
    rw [he]
    exact analyticAt_id
  have hi := (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp hac
  change AnalyticAt ℝ (e.symm : ℝ → ℝ) (e (e.symm s)) at hi
  simpa only [e.apply_symm_apply] using hi

#print axioms planarOrbitShiftEquiv
#print axioms planarOrbitShiftEquiv_symm_orbit
#print axioms planarOrbitShiftEquiv_symm_half
#print axioms planarOrbitShiftLiftIso_symm_analyticAt

end GlobalEmbedding.Paper
