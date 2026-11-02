import GlobalEmbedding.Paper.CollarComplexHolderSpace
import GlobalEmbedding.Paper.CollarSmoothHolderSlice
import GlobalEmbedding.Paper.CollarMultilinearCoefficientLift

/-!
# Actual complex multilinear little Hölder coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Uniform spatial jet estimates construct the actual complex continuous
multilinear coefficients needed by the source Taylor series.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Smooth periodic complex pointwise multilinear coefficients with uniform spatial jet product
bounds construct actual complex continuous multilinear coefficients in the actual little space.

Source: Proposition `prop:collar`, proof lines 530–534, coefficient Taylor expansions with three
spatial derivatives. Orthogonal real target coordinates preserve every spatial jet norm.
For each parameter tuple the real smooth-slice theorem therefore constructs the actual little
space element with the required norm bound. Its complex-valued lift is the given coefficient
function. The lift map is complex linear by the proved actual pointwise complex action and is
injective. The multilinear lifting theorem transports the pointwise multilinearity to the actual
complex little space and derives continuity and operator norm from the product-norm estimate.
No slice membership, coefficient continuity or completeness hypothesis is supplied.
-/
theorem collar_complex_multilinear_coefficient
    {n a N k : ℕ} {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    (G : MultilinearMap ℂ E
      (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)))
    (hsmooth : ∀ m, ContDiff ℝ ∞ (G m))
    (hperiodic : ∀ (m : (i : Fin n) → E i) (x : EuclideanSpace ℝ (Fin a))
      (t : Fin a → ℤ), G m (x + toLp 2 (fun i ↦ (t i : ℝ))) = G m x)
    (C : ℕ → ℝ) (hCnonneg : ∀ j ≤ k + 1, 0 ≤ C j)
    (hjet : ∀ (m : (i : Fin n) → E i) (j : ℕ), j ≤ k + 1 →
      ∀ x : EuclideanSpace ℝ (Fin a), (∀ i, x i ∈ Icc (0 : ℝ) 1) →
        ‖iteratedFDeriv ℝ j (G m) x‖ ≤ C j * ∏ i : Fin n, ‖m i‖)
    (α : ℝ) (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ∃ p : ContinuousMultilinearMap ℂ E (CollarComplexHolderSpace a N k α),
      (∀ m, collarComplexHolderFunction (p m) = G m) ∧
      ‖p‖ ≤ (∑ j ∈ Finset.range (k + 1), C j) + C (k + 1) * D ^ (1 - α) := by
  let H := CollarComplexHolderSpace a N k α
  let ι : H →ₗ[ℂ] (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)) :=
    { toFun := collarComplexHolderFunction
      map_add' := collarComplexHolderFunction_add
      map_smul' := collarComplexHolderFunction_smul }
  have hι : Function.Injective ι := collarComplexHolderFunction_injective
  let K : ℝ := (∑ j ∈ Finset.range (k + 1), C j) + C (k + 1) * D ^ (1 - α)
  have hD : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hK : 0 ≤ K :=
    add_nonneg (Finset.sum_nonneg (fun j hj ↦
      hCnonneg j (Finset.mem_range.mp hj).le))
      (mul_nonneg (hCnonneg (k + 1) le_rfl) (Real.rpow_nonneg hD _))
  let e := collarComplexHolderCoordinates N
  have hlift (m : (i : Fin n) → E i) :
      ∃ h : H, ι h = G m ∧ ‖h‖ ≤ K * ∏ i : Fin n, ‖m i‖ := by
    have hperiod : ∀ (x : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
        (e ∘ G m) (x + toLp 2 (fun i ↦ (t i : ℝ))) = (e ∘ G m) x := by
      intro x t
      simp only [Function.comp_apply, hperiodic]
    have hbounds : ∀ j ≤ k + 1, ∀ x : EuclideanSpace ℝ (Fin a),
        (∀ i, x i ∈ Icc (0 : ℝ) 1) →
        ‖iteratedFDeriv ℝ j (e ∘ G m) x‖ ≤ C j * ∏ i : Fin n, ‖m i‖ := by
      intro j hj x hx
      rw [e.norm_iteratedFDeriv_comp_left]
      exact hjet m j hj x hx
    obtain ⟨f, hf, hnorm⟩ := collar_smooth_holder_slice (e ∘ G m)
      (e.toContinuousLinearEquiv.contDiff.comp (hsmooth m)) hperiod
      (fun j ↦ C j * ∏ i : Fin n, ‖m i‖) hbounds hα D hdiam
    refine ⟨f, ?_, hnorm.trans_eq ?_⟩
    · funext x
      change e.symm (f.val.toFun x) = G m x
      rw [hf]
      exact e.symm_apply_apply _
    · dsimp only [K]
      rw [← Finset.sum_mul]
      ring
  have hex (m : (i : Fin n) → E i) : ∃ h : H, ι h = G m :=
    (hlift m).imp (fun h hh ↦ hh.1)
  have hnorm (m : (i : Fin n) → E i) (h : H) (hh : ι h = G m) :
      ‖h‖ ≤ K * ∏ i : Fin n, ‖m i‖ := by
    obtain ⟨u, hu, hbound⟩ := hlift m
    have heq : h = u := hι (hh.trans hu.symm)
    simpa only [heq] using hbound
  exact collar_multilinear_coefficient_lift ι hι G hex K hK hnorm

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_complex_multilinear_coefficient
