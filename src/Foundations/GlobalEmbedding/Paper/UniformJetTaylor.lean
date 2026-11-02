import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Taylor compatibility of uniform finite-jet limits

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382, periodic Hölder ambient-completeness expansion.
DAG node: `balanced-holder-uniform-jet-taylor`.
-/

open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- Uniform limits of the jets of C^k maps, when each limiting jet is continuous, form actual
Taylor data through order k of the zeroth limiting value function.

Proof: for each m<k, curry the (m+1)-st jet by the standard linear isometry. Its uniform limit
is the derivative of the m-th limiting field by the uniform-limit-of-derivatives theorem.
The given continuity and these derivative identities are exactly the finite Taylor-data
axioms. Source: `lem:balanced`, periodic Hölder completeness expansion. -/
theorem uniform_jet_limit_taylor
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (u : ℕ → E → F) (hu : ∀ n, ContDiff ℝ k (u n))
    (p : E → FormalMultilinearSeries ℝ E F)
    (hp : ∀ m ≤ k, Continuous (fun x ↦ p x m))
    (hlim : ∀ m ≤ k, TendstoUniformly (fun n x ↦ iteratedFDeriv ℝ m (u n) x)
      (fun x ↦ p x m) atTop) :
    HasFTaylorSeriesUpTo (k : ℕ∞ω) (fun x ↦ (p x 0).curry0) p := by
  refine ⟨fun x ↦ rfl, ?_, ?_⟩
  · intro m hm x
    have hmk : m < k := by exact_mod_cast hm
    let I := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
    have hcurry := I.isometry.uniformContinuous.comp_tendstoUniformly
      (hlim (m + 1) (Nat.succ_le_of_lt hmk))
    have hder (n : ℕ) (y : E) :
        HasFDerivAt (iteratedFDeriv ℝ m (u n))
          (iteratedFDeriv ℝ (m + 1) (u n) y).curryLeft y :=
      (hu n).ftaylorSeries.fderiv m hm y
    exact hasFDerivAt_of_tendstoUniformly hcurry hder ((hlim m hmk.le).tendsto_at) x
  · intro m hm
    exact hp m (by exact_mod_cast hm)

#print axioms uniform_jet_limit_taylor

end GlobalEmbedding.Paper
