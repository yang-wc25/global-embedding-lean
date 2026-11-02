import GlobalEmbedding.Paper.SupportedRankGoodLiftedFamily
import GlobalEmbedding.Paper.SupportedRankLiftedSpanProduct
import GlobalEmbedding.Paper.SymmetricSquareFinrank

/-!
# The original supported data generate the full actual q+d lifted span

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1029. Every good neighborhood, evaluation equivalence and span estimate
is constructed from the SAME original B; none is added as an original hypothesis.
-/

namespace GlobalEmbedding.Paper

/-- The original onto/phase hypotheses and an actual supporting hyperplane produce
one actual open good family and the full `q+(n-1)` lifted-column span bound.

Proof: the accepted original quotient dimension theorem gives `dim ker B=n-1`.
The exact hyperplane condition gives the same positive support dimension. Realize
the original good covector by its actual Riesz point, construct its actual projected
point/open good family, and apply the sole SAME-Q syzygy/lifted provider to the
constructed actual doubled dual. The triangular expression is the original q.
Source: `prop:supported-rank`, the complete actual-data strong-span instantiation. -/
theorem supportedRank_original_lifted_data
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B) (hn : 3 ≤ Module.finrank ℝ V)
    (hW : Module.finrank ℝ W =
      Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + 1)
    (U : Submodule ℝ V) (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range) :
    ∃ x : V, ∃ Ω : Set U,
      LinearSecondFormGoodCovector B (innerₗ V x) ∧ IsOpen Ω ∧
        U.orthogonalProjectionOnto x ∈ Ω ∧ U.orthogonalProjectionOnto x ≠ 0 ∧
        (∀ z ∈ Ω, ∀ e : V, e ∈ Uᗮ → ∀ t : ℝ,
          LinearSecondFormGoodCovector B (innerₗ V ((z : V) + t • e))) ∧
        Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 + (Module.finrank ℝ V - 1) ≤
          Module.finrank ℝ (supportedRankLiftedSpan
            (supportedRankQuadraticEvaluation (supportedRankKernelQuadratic B U)) Ω) := by
  have hdK := symmetricSquare_surjective_kernel_finrank B hB hW
  have hdU : Module.finrank ℝ U = Module.finrank ℝ V - 1 := by omega
  have hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U := hdK.trans hdU.symm
  have hpos : 0 < Module.finrank ℝ U := by omega
  obtain ⟨ξ, hgξ⟩ := hphase
  obtain ⟨x, _, hg⟩ := supportedRank_good_covector_riesz B ξ hgξ
  obtain ⟨Ω, hΩ, hz, hz0, hgood⟩ :=
    supportedRank_exists_good_lifted_family B U hK x hg hdim hpos
  refine ⟨x, Ω, hg, hΩ, hz, hz0, hgood, ?_⟩
  let Q := supportedRankKernelQuadratic B U
  let J := supportedRankGoodKernelDualEquiv B U hK x hg hdim
  have hJ : ∀ v k, J v k = 2 * Q k (U.orthogonalProjectionOnto x) v :=
    supportedRankGoodKernelDualEquiv_apply B U hK x hg hdim
  have hspan := supportedRankLiftedSpan_quadratic_finrank Q
    (supportedRankKernelQuadratic_symm B U) Ω hΩ (U.orthogonalProjectionOnto x) hz hz0 J hJ
  have hleft : Module.finrank ℝ V * (Module.finrank ℝ V - 1) / 2 +
      (Module.finrank ℝ V - 1) =
      Module.finrank ℝ U * (Module.finrank ℝ U + 1) / 2 + Module.finrank ℝ U := by
    rw [← hU]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_comm (Module.finrank ℝ U + 1) (Module.finrank ℝ U)]
  rw [hleft]
  exact hspan

#print axioms supportedRank_original_lifted_data

end GlobalEmbedding.Paper
