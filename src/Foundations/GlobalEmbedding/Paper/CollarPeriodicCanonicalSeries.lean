import GlobalEmbedding.Paper.CollarCompactTaylorBounds
import GlobalEmbedding.Paper.CollarCanonicalPointwiseSeries
import Mathlib.Topology.Order.Compact

/-!
# Uniform canonical Taylor sums on the actual periodic orbit slice

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Compactness of the actual fundamental cube and integer periodicity give
one parameter radius and a zero-spatial-jet coefficient bound on the full real orbit lift.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- The canonical parameter Taylor coefficients of the actual jointly analytic periodic source
family have one positive parameter convergence radius at every real spatial point, and a
uniform weighted zero-spatial-jet product-norm bound. Higher spatial jet estimates are separate.

Source: Proposition `prop:collar`, proof lines 530–534. The canonical coefficient construction
supplies actual smooth periodic multilinear data. The complexified image of the real fundamental
cube at the fixed parameter is compact. The compact Taylor theorem supplies a common positive
radius, actual normalized Taylor sums and full normalized derivative operator bounds there.
Restrict those derivatives to parameter directions to obtain the coefficient product-norm bound.
Every real spatial lift is an integer translate of its fractional-part representative in the
cube. Actual periodicity of the coefficients and original function transfers both the norm
estimate and the actual sums to the full lift. This does not assert the missing higher jet bounds.
-/
theorem collar_periodic_canonical_series {b a N : ℕ}
    (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (z₀ : EuclideanSpace ℂ (Fin b))
    (hg : ∀ x : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℂ g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w) :
    ∃ G : (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin b))
        (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)),
      (∀ n m x, G n m x = (n.factorial : ℂ)⁻¹ •
        iteratedFDeriv ℂ n g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))
          (fun i ↦ (m i, 0))) ∧
      (∀ n m, ContDiff ℝ ∞ (G n m)) ∧
      (∀ n m (x : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
        G n m (x + toLp 2 (fun i ↦ (t i : ℝ))) = G n m x) ∧
      ∃ ρ : ℝ≥0, 0 < ρ ∧ ∃ M : ℝ≥0,
        (∀ n m x, ‖G n m x‖ * (ρ : ℝ) ^ n ≤ (M : ℝ) * ∏ i : Fin n, ‖m i‖) ∧
        (∀ x : EuclideanSpace ℝ (Fin a),
          ∀ z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin b)) (ρ : ℝ≥0∞),
            HasSum (fun n : ℕ ↦ G n (fun _ : Fin n ↦ z) x)
              (g (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))) := by
  obtain ⟨G, hG, hsmooth, hper, _⟩ := collar_canonical_pointwise_series g z₀ hg hperiodic
  let φ (v : Fin a → ℝ) := (z₀, toLp 2 (fun i : Fin a ↦ (v i : ℂ)))
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hφ : Continuous φ := continuous_const.prodMk
    ((PiLp.continuous_toLp _ _).comp
      (continuous_pi (fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i))))
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKg : AnalyticOnNhd ℂ g K := by
    rintro w ⟨v, _, rfl⟩
    exact hg (toLp 2 v)
  obtain ⟨ρ, hρ, M, hnorm, hsum⟩ := collar_compact_taylor_bounds g K hK hKg
  have hmem (x : EuclideanSpace ℝ (Fin a)) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
      (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) ∈ K :=
    ⟨ofLp x, ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩, rfl⟩
  have hreduce (x : EuclideanSpace ℝ (Fin a)) :
      ∃ (y : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
        (∀ i, y i ∈ Icc (0 : ℝ) 1) ∧ y + toLp 2 (fun i ↦ (t i : ℝ)) = x := by
    refine ⟨toLp 2 (fun i ↦ Int.fract (x i)), fun i ↦ ⌊x i⌋, ?_, ?_⟩
    · exact fun i ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · ext i
      simp only [PiLp.add_apply, Int.fract_add_floor]
  have hnormcube (n : ℕ) (m : Fin n → EuclideanSpace ℂ (Fin b))
      (x : EuclideanSpace ℝ (Fin a)) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
      ‖G n m x‖ * (ρ : ℝ) ^ n ≤ (M : ℝ) * ∏ i : Fin n, ‖m i‖ := by
    have hD : ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n g
        (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ * (ρ : ℝ) ^ n ≤ (M : ℝ) := by
      exact_mod_cast hnorm _ (hmem x hx) n
    have hval : ‖G n m x‖ ≤ ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n g
        (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ * ∏ i : Fin n, ‖m i‖ := by
      rw [hG]
      simpa using
        ((n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n g
          (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))).le_opNorm (fun i ↦ (m i, 0))
    calc
      _ ≤ (_ * ∏ i : Fin n, ‖m i‖) * (ρ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hval (pow_nonneg ρ.coe_nonneg n)
      _ = (_ * (ρ : ℝ) ^ n) * ∏ i : Fin n, ‖m i‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
  refine ⟨G, hG, hsmooth, hper, ρ, hρ, M, ?_, ?_⟩
  · intro n m x
    obtain ⟨y, t, hy, hxy⟩ := hreduce x
    rw [← hxy, hper]
    exact hnormcube n m y hy
  · intro x z hz
    obtain ⟨y, t, hy, hxy⟩ := hreduce x
    have hzjoint : (z, (0 : EuclideanSpace ℂ (Fin a))) ∈
        Metric.eball (0 : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
          (ρ : ℝ≥0∞) := by
      simpa [Metric.mem_eball, Prod.edist_eq] using hz
    have hs : HasSum (fun n : ℕ ↦ G n (fun _ : Fin n ↦ z) y)
        (g (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ)))) := by
      simpa only [hG, Prod.mk_add_mk, add_zero] using hsum _ (hmem y hy) _ hzjoint
    have hpoint : (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ))) +
        (0, toLp 2 (fun i ↦ (t i : ℂ))) =
        (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) := by
      rw [← hxy]
      ext i <;> simp
    have htarget := hperiodic (z₀ + z, toLp 2 (fun i : Fin a ↦ (y i : ℂ))) t
    rw [hpoint] at htarget
    rw [htarget]
    apply hs.congr_fun
    intro n
    rw [← hxy, hper]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_periodic_canonical_series
