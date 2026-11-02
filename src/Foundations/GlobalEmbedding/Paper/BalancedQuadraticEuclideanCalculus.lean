import GlobalEmbedding.Paper.EuclideanCoordinateSecondPartialsCommute
import GlobalEmbedding.Paper.EuclideanCoordinateWordSmoothPeriodic
import GlobalEmbedding.Paper.RealEuclideanOneIsometry
import GlobalEmbedding.Paper.EuclideanCoordinateLaplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Actual Euclidean differential calculus for the balanced identity

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.2) and its
expansion, lines398–402. Every derivative here is the actual coordinate Frechet
derivative in the original word realization; no formal derivation is supplied.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The genuine scalar inner product, retained in the actual isometric Fin1
scalar value model, preserves smooth lifts. -/
theorem balancedEuclideanDot_contDiff {a N : ℕ}
    (f g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ realEuclideanOneIsometry (inner ℝ (f x) (g x))) :=
  realEuclideanOneIsometry.toLinearIsometry.toContinuousLinearMap.contDiff.comp (hf.inner ℝ hg)

/-- The actual first derivative of the genuine scalar inner product is its
original two-term product rule, in the isometric scalar value model. Native
inner differentiation and postcomposition by the actual scalar isometry prove
the equality at each actual coordinate vector. -/
theorem balancedEuclideanDot_derivative {a N : ℕ}
    (f g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [i]
        (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) x =
      realEuclideanOneIsometry
        (inner ℝ (f x) (euclideanCoordinateWordDerivative [i] g x) +
          inner ℝ (euclideanCoordinateWordDerivative [i] f x) (g x)) := by
  have hfx := hf.differentiable (by simp) x
  have hgx := hg.differentiable (by simp) x
  have hinner := hfx.hasFDerivAt.inner ℝ hgx.hasFDerivAt
  have hcomp := realEuclideanOneIsometry.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp x hinner
  simp only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap] at hcomp
  change fderiv ℝ (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) x
      (EuclideanSpace.single i 1) = _
  exact congrArg (fun T ↦ T (EuclideanSpace.single i 1)) hcomp.fderiv

/-- The literal actual shifted coordinate Laplacian on Euclidean lifts. On the
original periodic little space its value is exactly the already-constructed L.
This is a notation-level abbreviation for actual derivatives, not extra data. -/
noncomputable abbrev balancedEuclideanShiftedLaplacian {a N : ℕ}
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) :=
  fun x ↦ (∑ k : Fin a, euclideanCoordinateWordDerivative [k, k] f x) - f x

/-- The actual three-letter words `kki` and `ikk` agree for smooth periodic
lifts. Apply the existing C2 Schwarz theorem first to f and then to its smooth
k-derivative, using the imported actual all-word smoothness theorem. -/
theorem balancedCoordinateWord_triple_commute {a N : ℕ}
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x (m : Fin a → ℤ), f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = f x)
    (i k : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [k, k, i] f x =
      euclideanCoordinateWordDerivative [i, k, k] f x := by
  have hki : euclideanCoordinateWordDerivative [k, i] f =
      euclideanCoordinateWordDerivative [i, k] f :=
    funext (euclideanCoordinateWordDerivative_pair_commute f (hf.of_le (by simp)) k i)
  calc
    euclideanCoordinateWordDerivative [k, k, i] f x =
        euclideanCoordinateWordDerivative [k, i, k] f x := by
      change fderiv ℝ (euclideanCoordinateWordDerivative [k, i] f) x
          (EuclideanSpace.single k 1) =
        fderiv ℝ (euclideanCoordinateWordDerivative [i, k] f) x
          (EuclideanSpace.single k 1)
      rw [hki]
    _ = euclideanCoordinateWordDerivative [i, k, k] f x := by
      have hk := (euclideanCoordinateWordDerivative_smooth_periodic [k] f hf hp).1
      exact euclideanCoordinateWordDerivative_pair_commute
        (euclideanCoordinateWordDerivative [k] f) (hk.of_le (by simp)) k i x

/-- Actual coordinate differentiation commutes with the actual shifted
coordinate Laplacian on smooth periodic lifts. Finite derivative sums and
subtraction use native Frechet rules; the preceding actual third-word equality
exchanges the inner coordinate derivative through each second derivative. -/
theorem balancedEuclideanShiftedLaplacian_derivative {a N : ℕ}
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x (m : Fin a → ℤ), f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = f x)
    (i : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [i] (balancedEuclideanShiftedLaplacian f) x =
      balancedEuclideanShiftedLaplacian (euclideanCoordinateWordDerivative [i] f) x := by
  have hs (k : Fin a) :=
    (euclideanCoordinateWordDerivative_smooth_periodic [k, k] f hf hp).1
  have hsum : ContDiff ℝ ∞
      (fun y ↦ ∑ k : Fin a, euclideanCoordinateWordDerivative [k, k] f y) :=
    ContDiff.sum (fun k _ ↦ hs k)
  change fderiv ℝ (fun y ↦ (∑ k : Fin a, euclideanCoordinateWordDerivative [k, k] f y) - f y)
      x (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_sub (hsum.differentiable (by simp) x) (hf.differentiable (by simp) x),
    fderiv_fun_sum (fun k _ ↦ (hs k).differentiable (by simp) x)]
  simp only [sub_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (balancedCoordinateWord_triple_commute f hf hp i k x).symm

/-- The actual repeated coordinate derivative of the genuine scalar product.
Differentiate the first product rule as an equality of actual functions. The
imported word theorem gives smooth first derivatives, native fderiv-add and two
first product rules give four terms, and the equal mixed terms combine. -/
theorem balancedEuclideanDot_second_derivative {a N : ℕ}
    (f g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ x (m : Fin a → ℤ), f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = f x)
    (hpg : ∀ x (m : Fin a → ℤ), g (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = g x)
    (k : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative [k, k]
        (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) x =
      realEuclideanOneIsometry
        (inner ℝ (euclideanCoordinateWordDerivative [k, k] f x) (g x) +
          2 * inner ℝ (euclideanCoordinateWordDerivative [k] f x)
            (euclideanCoordinateWordDerivative [k] g x) +
          inner ℝ (f x) (euclideanCoordinateWordDerivative [k, k] g x)) := by
  let df := euclideanCoordinateWordDerivative [k] f
  let dg := euclideanCoordinateWordDerivative [k] g
  have hdf := (euclideanCoordinateWordDerivative_smooth_periodic [k] f hf hpf).1
  have hdg := (euclideanCoordinateWordDerivative_smooth_periodic [k] g hg hpg).1
  have heq : euclideanCoordinateWordDerivative [k]
      (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) =
      fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (dg y)) +
        realEuclideanOneIsometry (inner ℝ (df y) (g y)) := by
    funext y
    rw [balancedEuclideanDot_derivative f g hf hg k y, map_add]
  change fderiv ℝ (euclideanCoordinateWordDerivative [k]
      (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y)))) x
      (EuclideanSpace.single k 1) = _
  rw [heq, fderiv_fun_add
    ((balancedEuclideanDot_contDiff f dg hf hdg).differentiable (by simp) x)
    ((balancedEuclideanDot_contDiff df g hdf hg).differentiable (by simp) x)]
  change euclideanCoordinateWordDerivative [k]
      (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (dg y))) x +
      euclideanCoordinateWordDerivative [k]
      (fun y ↦ realEuclideanOneIsometry (inner ℝ (df y) (g y))) x = _
  rw [balancedEuclideanDot_derivative f dg hf hdg,
    balancedEuclideanDot_derivative df g hdf hg, ← map_add]
  congr 1
  change (inner ℝ (f x) (euclideanCoordinateWordDerivative [k, k] g x) +
      inner ℝ (euclideanCoordinateWordDerivative [k] f x)
        (euclideanCoordinateWordDerivative [k] g x)) +
      (inner ℝ (euclideanCoordinateWordDerivative [k] f x)
        (euclideanCoordinateWordDerivative [k] g x) +
      inner ℝ (euclideanCoordinateWordDerivative [k, k] f x) (g x)) = _
  ring

/-- The genuine shifted coordinate Laplacian satisfies its exact product
formula. Sum the preceding actual second-derivative identity, commute the real
scalar isometry through finite sums and subtraction, and expand inner products
of the actual Laplacian sums. The extra positive product term comes from the
shift by minus identity. Source: expansion following formula(4.2). -/
theorem balancedEuclideanShiftedLaplacian_dot {a N : ℕ}
    (f g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ x (m : Fin a → ℤ), f (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = f x)
    (hpg : ∀ x (m : Fin a → ℤ), g (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = g x)
    (x : EuclideanSpace ℝ (Fin a)) :
    balancedEuclideanShiftedLaplacian
        (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) x =
      realEuclideanOneIsometry
        (inner ℝ (balancedEuclideanShiftedLaplacian f x) (g x) +
          inner ℝ (f x) (balancedEuclideanShiftedLaplacian g x) +
          2 * (∑ k : Fin a, inner ℝ (euclideanCoordinateWordDerivative [k] f x)
            (euclideanCoordinateWordDerivative [k] g x)) + inner ℝ (f x) (g x)) := by
  change (∑ k : Fin a, euclideanCoordinateWordDerivative [k, k]
      (fun y ↦ realEuclideanOneIsometry (inner ℝ (f y) (g y))) x) -
    realEuclideanOneIsometry (inner ℝ (f x) (g x)) = _
  simp_rw [balancedEuclideanDot_second_derivative f g hf hg hpf hpg]
  rw [← map_sum, ← map_sub]
  congr 1
  simp only [balancedEuclideanShiftedLaplacian, inner_sub_left, inner_sub_right,
    sum_inner, inner_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The exact genuine expansion used after formula(4.2): apply the preceding
Laplacian product formula to the two coordinate derivatives of v, commute the
actual shifted Laplacian with these derivatives, and use actual C2 Schwarz to
write the Hessian terms in the source's `i k`, `j k` order. -/
theorem balancedEuclideanShiftedLaplacian_gradientDot {a N : ℕ}
    (v : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hv : ContDiff ℝ ∞ v)
    (hp : ∀ x (m : Fin a → ℤ), v (x + WithLp.toLp 2 (fun i ↦ (m i : ℝ))) = v x)
    (i j : Fin a) (x : EuclideanSpace ℝ (Fin a)) :
    balancedEuclideanShiftedLaplacian
      (fun y ↦ realEuclideanOneIsometry
        (inner ℝ (euclideanCoordinateWordDerivative [i] v y)
          (euclideanCoordinateWordDerivative [j] v y))) x =
    realEuclideanOneIsometry
      (inner ℝ (euclideanCoordinateWordDerivative [i] (balancedEuclideanShiftedLaplacian v) x)
          (euclideanCoordinateWordDerivative [j] v x) +
        inner ℝ (euclideanCoordinateWordDerivative [j] (balancedEuclideanShiftedLaplacian v) x)
          (euclideanCoordinateWordDerivative [i] v x) +
        2 * (∑ k : Fin a, inner ℝ (euclideanCoordinateWordDerivative [i, k] v x)
          (euclideanCoordinateWordDerivative [j, k] v x)) +
        inner ℝ (euclideanCoordinateWordDerivative [i] v x)
          (euclideanCoordinateWordDerivative [j] v x)) := by
  have hi := euclideanCoordinateWordDerivative_smooth_periodic [i] v hv hp
  have hj := euclideanCoordinateWordDerivative_smooth_periodic [j] v hv hp
  rw [balancedEuclideanShiftedLaplacian_dot
    (euclideanCoordinateWordDerivative [i] v) (euclideanCoordinateWordDerivative [j] v)
    hi.1 hj.1 hi.2 hj.2]
  rw [← balancedEuclideanShiftedLaplacian_derivative v hv hp i x,
    ← balancedEuclideanShiftedLaplacian_derivative v hv hp j x]
  congr 1
  have hsum :
      (∑ k : Fin a, inner ℝ
        (euclideanCoordinateWordDerivative [k] (euclideanCoordinateWordDerivative [i] v) x)
        (euclideanCoordinateWordDerivative [k] (euclideanCoordinateWordDerivative [j] v) x)) =
      ∑ k : Fin a, inner ℝ (euclideanCoordinateWordDerivative [i, k] v x)
        (euclideanCoordinateWordDerivative [j, k] v x) := by
    apply Finset.sum_congr rfl
    intro k _
    change inner ℝ (euclideanCoordinateWordDerivative [k, i] v x)
        (euclideanCoordinateWordDerivative [k, j] v x) = _
    rw [euclideanCoordinateWordDerivative_pair_commute v (hv.of_le (by simp)) k i,
      euclideanCoordinateWordDerivative_pair_commute v (hv.of_le (by simp)) k j]
  rw [hsum, real_inner_comm (euclideanCoordinateWordDerivative [i] v x)
    (euclideanCoordinateWordDerivative [j] (balancedEuclideanShiftedLaplacian v) x)]

#print axioms balancedEuclideanDot_derivative
#print axioms balancedEuclideanShiftedLaplacian_derivative
#print axioms balancedEuclideanShiftedLaplacian_dot
#print axioms balancedEuclideanShiftedLaplacian_gradientDot

end GlobalEmbedding.Paper
