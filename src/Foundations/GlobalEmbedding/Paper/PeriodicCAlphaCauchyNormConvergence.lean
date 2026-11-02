import GlobalEmbedding.Paper.PeriodicCAlphaJetMap
import GlobalEmbedding.Paper.PeriodicCAlphaQuotientBound

/-!
# Full Holder-norm convergence from the Cauchy condition and actual jet limits

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-cauchy-norm-convergence`.
-/

open Filter Set WithLp
open scoped Topology BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- If an actual Holder-norm Cauchy sequence has pointwise jet limits through k equal to those
of an actual Holder element f, it converges to f in the full actual Holder norm.

Proof: choose a Cauchy tail with norm differences below epsilon divided by twice the number
of norm summands. The global jet and Holder quotient bounds control every pointwise
quantity of each difference. Pass the second sequence index to the actual jet limit, keeping
the first index fixed. Take each finite real supremum and sum the k+2 bounds, obtaining at
most epsilon/2 in the actual norm. Source: `lem:balanced`, ambient completeness expansion. -/
theorem periodicCAlpha_cauchy_norm_tendsto {a N k : ℕ} {α : ℝ}
    (u : ℕ → PeriodicCAlphaFunction a N k α) (hu : CauchySeq u)
    (f : PeriodicCAlphaFunction a N k α)
    (hlim : ∀ j ≤ k, ∀ x, Tendsto (fun n ↦ iteratedFDeriv ℝ j (u n).toFun x)
      atTop (𝓝 (iteratedFDeriv ℝ j f.toFun x))) :
    Tendsto u atTop (𝓝 f) := by
  have hsub (v w : PeriodicCAlphaFunction a N k α) (j : ℕ) (hj : j ≤ k)
      (x : EuclideanSpace ℝ (Fin a)) :
      iteratedFDeriv ℝ j (v - w).toFun x =
        iteratedFDeriv ℝ j v.toFun x - iteratedFDeriv ℝ j w.toFun x := by
    exact congrArg (fun G : EuclideanSpace ℝ (Fin a) →ᵇ
        ((EuclideanSpace ℝ (Fin a)) [×j]→L[ℝ] EuclideanSpace ℝ (Fin N)) ↦ G x)
      ((periodicCAlphaJetMap (a := a) (N := N) (k := k) (α := α) j hj).map_sub v w)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (2 * ((k : ℝ) + 2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.mp hu δ hδ
  have hnorm (n : ℕ) (hn : n₀ ≤ n) (m : ℕ) (hm : n₀ ≤ m) :
      ‖u n - u m‖ ≤ δ := by
    simpa only [dist_eq_norm] using (hn₀ n hn m hm).le
  refine ⟨n₀, ?_⟩
  intro n hn
  have hjbound (j : ℕ) (hj : j ≤ k) (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (u n - f).toFun x‖ ≤ δ := by
    rw [hsub (u n) f j hj x]
    apply le_of_tendsto ((tendsto_const_nhds.sub (hlim j hj x)).norm)
    filter_upwards [eventually_ge_atTop n₀] with m hm
    rw [← hsub (u n) (u m) j hj x]
    exact (periodicCAlpha_global_jet_bound (u n - u m) j hj x).trans (hnorm n hn m hm)
  have hqbound (x y : EuclideanSpace ℝ (Fin a))
      (hd : 0 < dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))) :
      ‖iteratedFDeriv ℝ k (u n - f).toFun x - iteratedFDeriv ℝ k (u n - f).toFun y‖ /
          dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
            (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ^ α ≤ δ := by
    rw [hsub (u n) f k le_rfl x, hsub (u n) f k le_rfl y]
    apply le_of_tendsto
      (((tendsto_const_nhds.sub (hlim k le_rfl x)).sub
        (tendsto_const_nhds.sub (hlim k le_rfl y))).norm.div_const _)
    filter_upwards [eventually_ge_atTop n₀] with m hm
    rw [← hsub (u n) (u m) k le_rfl x, ← hsub (u n) (u m) k le_rfl y]
    exact (periodicCAlpha_quotient_bound (u n - u m) x y hd).trans (hnorm n hn m hm)
  have htotal : periodicCAlphaNorm (u n - f) ≤ ((k : ℝ) + 2) * δ := by
    unfold periodicCAlphaNorm
    calc
      _ ≤ (∑ j ∈ Finset.range (k + 1), δ) + δ := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j hj
          apply Real.sSup_le _ hδ.le
          rintro r ⟨x, hx, rfl⟩
          exact hjbound j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x
        · apply Real.sSup_le _ hδ.le
          rintro r ⟨x, y, hd, rfl⟩
          exact hqbound x y hd
      _ = _ := by simp; ring
  rw [dist_eq_norm]
  change periodicCAlphaNorm (u n - f) < ε
  apply lt_of_le_of_lt htotal
  calc
    ((k : ℝ) + 2) * δ = ε / 2 := by
      have hk : (k : ℝ) + 2 ≠ 0 := by positivity
      dsimp [δ]
      field_simp
    _ < ε := by linarith

#print axioms periodicCAlpha_cauchy_norm_tendsto

end GlobalEmbedding.Paper
