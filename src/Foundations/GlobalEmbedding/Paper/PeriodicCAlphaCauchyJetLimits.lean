import GlobalEmbedding.Paper.PeriodicCAlphaJetMap

/-!
# Uniform jet limits of actual periodic Hölder Cauchy sequences

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382; ambient completeness expansion. DAG node: `balanced-holder-cauchy-jet-limits`.
-/

open Filter
open scoped Topology BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- Every jet through order k of an actual Holder-norm Cauchy sequence has a bounded continuous
limit, with both bounded-function norm convergence and global uniform convergence of the jets.

Proof: the actual jet map is continuous linear and therefore uniformly continuous, so it
sends the Cauchy sequence to a Cauchy sequence. The bounded continuous functions taking values
in the complete multilinear-map space are complete. Their norm convergence is equivalent to
global uniform convergence, giving both conclusions. No Holder completeness is assumed.
Source: `lem:balanced`, periodic Hölder ambient completeness expansion. -/
theorem periodicCAlpha_cauchy_jet_limits {a N k : ℕ} {α : ℝ}
    (u : ℕ → PeriodicCAlphaFunction a N k α) (hu : CauchySeq u)
    (j : ℕ) (hj : j ≤ k) :
    ∃ J : EuclideanSpace ℝ (Fin a) →ᵇ
        ((EuclideanSpace ℝ (Fin a)) [×j]→L[ℝ] EuclideanSpace ℝ (Fin N)),
      Tendsto (fun n ↦ periodicCAlphaJetMap j hj (u n)) atTop (𝓝 J) ∧
      TendstoUniformly (fun n x ↦ iteratedFDeriv ℝ j (u n).toFun x) J atTop := by
  have hLip := ContinuousLinearMap.lipschitzWith (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicCAlphaFunction a N k α)
    (F := EuclideanSpace ℝ (Fin a) →ᵇ
      ((EuclideanSpace ℝ (Fin a)) [×j]→L[ℝ] EuclideanSpace ℝ (Fin N)))
    (σ₁₂ := RingHom.id ℝ) (periodicCAlphaJetMap j hj)
  have huc := hLip.uniformContinuous
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete (huc.comp_cauchySeq hu)
  exact ⟨J, hJ, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hJ⟩

#print axioms periodicCAlpha_cauchy_jet_limits

end GlobalEmbedding.Paper
