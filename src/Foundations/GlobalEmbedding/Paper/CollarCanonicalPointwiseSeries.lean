import GlobalEmbedding.Paper.CollarCanonicalTaylorCoefficients

/-!
# Pointwise sums of the actual canonical parameter coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This constructs actual pointwise Taylor sums. The radius here can depend
on the real spatial point; a uniform radius and mixed-jet bounds remain separate obligations.
-/

open WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- The canonical smooth periodic parameter coefficients actually sum to the given function
at every real spatial point on some positive parameter ball, whose radius can depend on that point.

Source: Proposition `prop:collar`, proof lines 530–534. Choose the actual canonical coefficients
from the normalized joint-derivative construction at each degree. At each real slice point,
joint analyticity supplies a genuine power series on some positive joint ball. Mathlib's
normalized-derivative Taylor sum identifies its diagonal terms with the canonical coefficients.
Restrict increments to (z,0); the product max norm equals the parameter norm, so a smaller
positive finite radius gives the asserted actual pointwise sum. This proves convergence, not
only formal coefficient identities, and does not assert a spatially uniform radius.
-/
theorem collar_canonical_pointwise_series {b a N : ℕ}
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
      (∀ x : EuclideanSpace ℝ (Fin a), ∃ ρ : ℝ≥0, 0 < ρ ∧
        ∀ z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin b)) (ρ : ℝ≥0∞),
          HasSum (fun n : ℕ ↦ G n (fun _ : Fin n ↦ z) x)
            (g (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))) := by
  choose G hG hsmooth hper using collar_canonical_taylor_coefficients g z₀ hg hperiodic
  refine ⟨G, hG, hsmooth, hper, ?_⟩
  intro x
  obtain ⟨p, r, hp⟩ := hg x
  obtain ⟨ρ, hρ, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  refine ⟨ρ, by exact_mod_cast hρ, ?_⟩
  intro z hz
  have hzjoint : (z, (0 : EuclideanSpace ℂ (Fin a))) ∈
      Metric.eball (0 : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
        (ρ : ℝ≥0∞) := by
    simpa [Metric.mem_eball, Prod.edist_eq] using hz
  have hsum := hp.hasSum_iteratedFDeriv ((Metric.eball_subset_eball hr.le) hzjoint)
  simpa only [hG, Prod.mk_add_mk, add_zero] using hsum

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_canonical_pointwise_series
