import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Norms of iterated jets

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Spatial derivatives of parameter coefficients require estimates for
iterated derivatives of the full joint parameter jets.
-/

namespace GlobalEmbedding.Paper

set_option backward.isDefEq.respectTransparency false in
/-- Iterating j derivatives of the nth jet preserves exactly the norm of the (n+j)th jet.

Source: Proposition `prop:collar`, proof lines 530–534, mixed coefficient jet estimates.
Induct on j. At j=0 use the norm identity for the zeroth derivative. In the successor step,
move one derivative to the inner function using norm_iteratedFDeriv_fderiv. The derivative of
the nth jet is the currying linear isometry applied to the (n+1)st jet. Composition with this
linear isometry preserves every further iterated derivative norm. Apply induction and the
identity (n+1)+j=n+(j+1). No differentiability, symmetry, finite dimension or completeness
hypothesis is required, because the currying identities hold for the total iterated derivative.
-/
theorem collar_iterated_jet_norm
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (x : E) (n j : ℕ) :
    ‖iteratedFDeriv 𝕜 j (iteratedFDeriv 𝕜 n f) x‖ =
      ‖iteratedFDeriv 𝕜 (n + j) f x‖ := by
  induction j generalizing n with
  | zero => simp only [norm_iteratedFDeriv_zero, Nat.add_zero]
  | succ j ih =>
    calc
      _ = ‖iteratedFDeriv 𝕜 j (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x‖ :=
        norm_iteratedFDeriv_fderiv.symm
      _ = ‖iteratedFDeriv 𝕜 j (iteratedFDeriv 𝕜 (n + 1) f) x‖ := by
        rw [fderiv_iteratedFDeriv]
        let I := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F
        have hI := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := 𝕜)
          (E := E) (F := E [×n + 1]→L[𝕜] F) (G := E →L[𝕜] E [×n]→L[𝕜] F)
          I (iteratedFDeriv 𝕜 (n + 1) f) x j
        exact hI
      _ = ‖iteratedFDeriv 𝕜 (n + 1 + j) f x‖ := ih (n + 1)
      _ = _ := congrArg (fun k : ℕ ↦ ‖iteratedFDeriv 𝕜 k f x‖)
        (by omega : n + 1 + j = n + (j + 1))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_iterated_jet_norm
