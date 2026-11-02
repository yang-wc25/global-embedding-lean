import GlobalEmbedding.Paper.PeriodicCAlphaCauchyJetLimits
import GlobalEmbedding.Paper.UniformJetTaylor

/-!
# Actual C^k periodic limits of periodic Hölder Cauchy sequences

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-cauchy-limit-regularity`.
-/

open Filter WithLp
open scoped Topology ContDiff BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- An actual Holder-norm Cauchy sequence has a genuine C^k periodic lift limit, with global
uniform convergence of every iterated derivative through k.

Proof: choose the bounded continuous jet limits, assemble them as finite formal tensor data,
and apply the uniform-jet Taylor theorem to identify them as the derivatives of a C^k value
function. The zeroth jet gives pointwise value convergence. Pass each integer-periodicity
equality to that value limit by uniqueness of limits.
Source: `lem:balanced`, actual periodic Hölder ambient-completeness expansion. -/
theorem periodicCAlpha_cauchy_limit_regularity {a N k : ℕ} {α : ℝ}
    (u : ℕ → PeriodicCAlphaFunction a N k α) (hu : CauchySeq u) :
    ∃ f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N),
      ContDiff ℝ k f ∧
      (∀ x (m : Fin a → ℤ), f (x + toLp 2 (fun i ↦ (m i : ℝ))) = f x) ∧
      (∀ j ≤ k, TendstoUniformly (fun n x ↦ iteratedFDeriv ℝ j (u n).toFun x)
        (iteratedFDeriv ℝ j f) atTop) ∧
      ∀ x, Tendsto (fun n ↦ (u n).toFun x) atTop (𝓝 (f x)) := by
  choose J hJ hJU using fun j : Fin (k + 1) ↦
    periodicCAlpha_cauchy_jet_limits u hu j.val (Nat.le_of_lt_succ j.isLt)
  let p : EuclideanSpace ℝ (Fin a) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin a)) (EuclideanSpace ℝ (Fin N)) :=
    fun x j ↦ if hj : j ≤ k then J ⟨j, Nat.lt_succ_of_le hj⟩ x else 0
  have hp (j : ℕ) (hj : j ≤ k) : Continuous (fun x ↦ p x j) := by
    simpa only [p, dite_eq_left hj] using (J ⟨j, Nat.lt_succ_of_le hj⟩).continuous
  have hpu (j : ℕ) (hj : j ≤ k) :
      TendstoUniformly (fun n x ↦ iteratedFDeriv ℝ j (u n).toFun x)
        (fun x ↦ p x j) atTop := by
    simpa only [p, dite_eq_left hj] using hJU ⟨j, Nat.lt_succ_of_le hj⟩
  let f := fun x ↦ (p x 0).curry0
  have ht := uniform_jet_limit_taylor k (fun n ↦ (u n).toFun) (fun n ↦ (u n).contDiff)
    p hp hpu
  have hval (x : EuclideanSpace ℝ (Fin a)) :
      Tendsto (fun n ↦ (u n).toFun x) atTop (𝓝 (f x)) := by
    have hc := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin a))
      (EuclideanSpace ℝ (Fin N))).continuous.tendsto (p x 0)
    simpa [f, iteratedFDeriv_zero_eq_comp, Function.comp_def,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curry0_uncurry0] using
      hc.comp ((hpu 0 (Nat.zero_le _)).tendsto_at x)
  refine ⟨f, ht.contDiff, ?_, ?_, hval⟩
  · intro x m
    apply tendsto_nhds_unique (hval (x + toLp 2 (fun i ↦ (m i : ℝ))))
    have heq : (fun n ↦ (u n).toFun (x + toLp 2 (fun i ↦ (m i : ℝ)))) =
        (fun n ↦ (u n).toFun x) := funext (fun n ↦ (u n).periodic x m)
    rw [heq]
    exact hval x
  · intro j hj
    have heq : (fun x ↦ p x j) = iteratedFDeriv ℝ j f :=
      funext (fun x ↦ ht.eq_iteratedFDeriv (by exact_mod_cast hj) x)
    simpa only [heq] using hpu j hj

#print axioms periodicCAlpha_cauchy_limit_regularity

end GlobalEmbedding.Paper
