import GlobalEmbedding.Paper.CollarPeriodicCanonicalSeries
import GlobalEmbedding.Paper.CollarEvaluatedComplexJetBound
import Mathlib.Topology.Order.Compact

/-!
# Uniform spatial jet bounds for the actual canonical parameter coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. All finite spatial coefficient jet bounds are extracted from genuine
joint analyticity on the actual compact periodic slice.
-/

open Set WithLp
open scoped ContDiff NNReal ENNReal Topology

namespace GlobalEmbedding.Paper

/-- Canonical coefficients of the actual jointly analytic periodic family have uniform weighted
spatial jet product bounds through any fixed finite order, on one common positive parameter
radius on which their actual pointwise Taylor series also sum to the original family.

Source: Proposition `prop:collar`, proof lines 530–534, Taylor convergence with three spatial
derivatives. For each spatial order j, the full joint jet D^j g is analytic near the actual
compact fundamental-domain slice. Compact Taylor bounds give a positive radius and a bound
on its normalized nth derivatives, uniformly in n and slice point. The evaluated complex-jet
estimate bounds the jth real spatial coefficient jet by the joint (n+j)th derivative. The exact
iterated-jet norm identity identifies that norm with D^n(D^j g), so the normalization is the
same n!, with no additional factorial loss. Take the positive minimum of the finitely many jet
radii and the actual pointwise Taylor radius. Shrinking preserves all weighted bounds and sums.
-/
theorem collar_canonical_mixed_jet_bounds {b a N k : ℕ}
    (g : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) →
      EuclideanSpace ℂ (Fin N))
    (z₀ : EuclideanSpace ℂ (Fin b))
    (hg : ∀ x : EuclideanSpace ℝ (Fin a),
      AnalyticAt ℂ g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))
    (hperiodic : ∀ (w : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))
      (t : Fin a → ℤ), g (w + (0, toLp 2 (fun i ↦ (t i : ℂ)))) = g w) :
    ∃ G : (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n ↦ EuclideanSpace ℂ (Fin b))
        (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℂ (Fin N)),
      (∀ n m, ContDiff ℝ ∞ (G n m)) ∧
      (∀ n m (x : EuclideanSpace ℝ (Fin a)) (t : Fin a → ℤ),
        G n m (x + toLp 2 (fun i ↦ (t i : ℝ))) = G n m x) ∧
      ∃ ρ : ℝ≥0, 0 < ρ ∧ ∃ M : ℕ → ℝ≥0,
        (∀ n j, j ≤ k + 1 → ∀ (m : Fin n → EuclideanSpace ℂ (Fin b))
          (x : EuclideanSpace ℝ (Fin a)), (∀ i, x i ∈ Icc (0 : ℝ) 1) →
          ‖iteratedFDeriv ℝ j (G n m) x‖ * (ρ : ℝ) ^ n ≤
            (M j : ℝ) * ∏ i : Fin n, ‖m i‖) ∧
        (∀ x : EuclideanSpace ℝ (Fin a),
          ∀ z ∈ Metric.eball (0 : EuclideanSpace ℂ (Fin b)) (ρ : ℝ≥0∞),
            HasSum (fun n : ℕ ↦ G n (fun _ : Fin n ↦ z) x)
              (g (z₀ + z, toLp 2 (fun i : Fin a ↦ (x i : ℂ))))) := by
  classical
  obtain ⟨G, hG, hsmooth, hper, r₀, hr₀, _, _, hpoint⟩ :=
    collar_periodic_canonical_series g z₀ hg hperiodic
  let φ (v : Fin a → ℝ) := (z₀, toLp 2 (fun i : Fin a ↦ (v i : ℂ)))
  let K := φ '' Icc (0 : Fin a → ℝ) 1
  have hφ : Continuous φ := continuous_const.prodMk
    ((PiLp.continuous_toLp _ _).comp
      (continuous_pi (fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i))))
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKg : AnalyticOnNhd ℂ g K := by
    rintro w ⟨v, _, rfl⟩
    exact hg (toLp 2 v)
  have hTaylor (j : ℕ) := collar_compact_taylor_bounds (iteratedFDeriv ℂ j g) K hK
    (hKg.iteratedFDeriv j)
  choose r hr M hM _hsum using hTaylor
  have ht : (Finset.range (k + 2)).Nonempty := ⟨0, by simp⟩
  let ρ : ℝ≥0 := min r₀ ((Finset.range (k + 2)).inf' ht r)
  have hρ : 0 < ρ := lt_min hr₀ ((Finset.lt_inf'_iff ht).mpr (fun j _ ↦ hr j))
  have hρj (j : ℕ) (hj : j ≤ k + 1) : ρ ≤ r j :=
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.mpr (by omega)))
  let J : EuclideanSpace ℝ (Fin a) →L[ℝ]
      (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a)) :=
    ({ toFun := fun x ↦ (0, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))
       map_add' := by intro x y; ext i <;> simp
       map_smul' := by intro c x; ext i <;> simp } :
      EuclideanSpace ℝ (Fin a) →ₗ[ℝ]
        (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a))).toContinuousLinearMap
  have hJnorm (x : EuclideanSpace ℝ (Fin a)) : ‖J x‖ = ‖x‖ := by
    change ‖((0 : EuclideanSpace ℂ (Fin b)),
      (toLp 2 (fun i : Fin a ↦ (x i : ℂ)) : EuclideanSpace ℂ (Fin a)))‖ = ‖x‖
    simp [EuclideanSpace.norm_eq]
  have hJ : ‖J‖ ≤ 1 := J.opNorm_le_bound zero_le_one
    (fun x ↦ by simpa only [hJnorm, one_mul] using (le_rfl : ‖x‖ ≤ ‖x‖))
  let c : EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin a) := (z₀, 0)
  have hJpoint (x : EuclideanSpace ℝ (Fin a)) :
      c + J x = (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) := by
    ext i <;> simp [c, J]
  have heval (n j : ℕ) (m : Fin n → EuclideanSpace ℂ (Fin b))
      (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (G n m) x‖ ≤ (∏ i : Fin n, ‖m i‖) *
        ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n (iteratedFDeriv ℂ j g)
          (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ := by
    have hgJ : AnalyticAt ℂ g (c + J x) := by rw [hJpoint]; exact hg x
    have hb := collar_evaluated_complex_jet_bound g c J hJ x hgJ n j
      (fun i : Fin n ↦ (m i, (0 : EuclideanSpace ℂ (Fin a))))
    have hfunc : (fun y ↦ (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n g
        (c + J y) (fun i ↦ (m i, (0 : EuclideanSpace ℂ (Fin a))))) = G n m := by
      funext y
      rw [hJpoint]
      exact (hG n m y).symm
    rw [hfunc, hJpoint] at hb
    have hprod : (∏ i : Fin n, ‖(m i, (0 : EuclideanSpace ℂ (Fin a)))‖) =
        ∏ i : Fin n, ‖m i‖ := by simp
    rw [hprod] at hb
    have hmix : ‖iteratedFDeriv ℂ n (iteratedFDeriv ℂ j g)
        (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ =
        ‖iteratedFDeriv ℂ (n + j) g (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ := by
      exact (collar_iterated_jet_norm (𝕜 := ℂ) g
        (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) j n).trans
        (congrArg (fun l : ℕ ↦ ‖iteratedFDeriv ℂ l g
          (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖) (Nat.add_comm j n))
    apply hb.trans_eq
    rw [norm_smul, hmix]
    ring
  refine ⟨G, hsmooth, hper, ρ, hρ, M, ?_, ?_⟩
  · intro n j hj m x hx
    have hmem : (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ))) ∈ K :=
      ⟨ofLp x, ⟨fun i ↦ (hx i).1, fun i ↦ (hx i).2⟩, rfl⟩
    have hweight : ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n (iteratedFDeriv ℂ j g)
        (z₀, toLp 2 (fun i : Fin a ↦ (x i : ℂ)))‖ * (ρ : ℝ) ^ n ≤ (M j : ℝ) := by
      exact_mod_cast ((mul_le_mul_of_nonneg_left (pow_le_pow_left' (hρj j hj) n) zero_le).trans
        (hM j _ hmem n))
    calc
      _ ≤ ((∏ i : Fin n, ‖m i‖) * _) * (ρ : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (heval n j m x) (pow_nonneg ρ.coe_nonneg n)
      _ = (∏ i : Fin n, ‖m i‖) * (_ * (ρ : ℝ) ^ n) := by ring
      _ ≤ (∏ i : Fin n, ‖m i‖) * (M j : ℝ) :=
        mul_le_mul_of_nonneg_left hweight (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
      _ = _ := mul_comm _ _
  · intro x z hz
    exact hpoint x z ((Metric.eball_subset_eball
      (show (ρ : ℝ≥0∞) ≤ (r₀ : ℝ≥0∞) by exact_mod_cast (min_le_left r₀ _))) hz)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_canonical_mixed_jet_bounds
