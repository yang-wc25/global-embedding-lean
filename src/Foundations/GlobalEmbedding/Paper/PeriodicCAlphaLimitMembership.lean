import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import GlobalEmbedding.Paper.PeriodicCAlphaQuotientBound

/-!
# Holder membership of bounded pointwise jet limits

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-limit-membership`.
-/

open Filter Set WithLp
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A genuine C^k periodic lift which is a pointwise jet limit of actual Holder elements
with uniformly bounded norms has an actual Holder-carrier representative.

Proof: the actual global jet and quotient bounds are uniform in the sequence index. Pass
them to the pointwise jet limits, using continuity of norms and of division by each fixed
positive-distance power. These are precisely the raw carrier's finite derivative and Holder
bounds. Source: `lem:balanced`, actual ambient Holder completeness expansion. -/
theorem periodicCAlpha_limit_membership {a N k : ℕ} {α : ℝ}
    (u : ℕ → PeriodicCAlphaFunction a N k α)
    (g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ k g)
    (hper : ∀ x (m : Fin a → ℤ), g (x + toLp 2 (fun i ↦ (m i : ℝ))) = g x)
    (hlim : ∀ j ≤ k, ∀ x, Tendsto (fun n ↦ iteratedFDeriv ℝ j (u n).toFun x)
      atTop (𝓝 (iteratedFDeriv ℝ j g x)))
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ f : PeriodicCAlphaFunction a N k α, f.toFun = g := by
  refine ⟨⟨g, hper, hg, ?_, ?_⟩, rfl⟩
  · intro j hj
    refine ⟨M, ?_⟩
    intro x hx
    apply le_of_tendsto (hlim j hj x).norm
    exact Eventually.of_forall (fun n ↦
      (periodicCAlpha_global_jet_bound (u n) j hj x).trans (hM n))
  · refine ⟨M, ?_⟩
    intro x y d hd
    apply le_of_tendsto (((hlim k le_rfl x).sub (hlim k le_rfl y)).norm.div_const (d ^ α))
    exact Eventually.of_forall (fun n ↦
      (periodicCAlpha_quotient_bound (u n) x y hd).trans (hM n))

#print axioms periodicCAlpha_limit_membership

end GlobalEmbedding.Paper
