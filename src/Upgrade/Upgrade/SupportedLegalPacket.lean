import GlobalEmbedding.Targets.SupportedKernelNormalRank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Fin.Basic

/-!
# Finite legal directions for the actual supported-kernel defining equation

Source: `thm:upgrade`, main.tex 1073--1083. The original strong
`legal_normal_rank_of_supported_kernels` already constructs the smooth defining
submersion. This consumer chooses exactly q legal columns from that SAME actual
equation, retaining their covectors and normal values. No supplied chart, rank,
independent family, or local geometric realization is an input.
-/

noncomputable section
open Module Set
open scoped ContDiff

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- The accepted full supported-rank theorem supplies a single actual defining
chart and q independent derivatives of literal legal second-form columns.
The native finite spanning-set theorem selects actual generators, not arbitrary
linear combinations, so each column remains eligible for local legal-wave
extension. The construction also applies at n=3, where it gives q=3 and makes
no assertion about eliminating all supported kernels. -/
theorem exists_supported_legal_equation_packet
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B)
    (hphase : LinearSecondFormPhaseRegular B.toLinearMap)
    (hsupported : HasSupportedKernel B.toLinearMap)
    (hn : 3 ≤ finrank ℝ V)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1) :
    let q := finrank ℝ V * (finrank ℝ V - 1) / 2
    ∃ chart : SupportedLocusLocalEquations
        {C : SymmetricSquare V →L[ℝ] W |
          Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
        {C : SymmetricSquare V →L[ℝ] W | HasSupportedKernel C.toLinearMap} B,
      ∃ (ξ : Fin q → V →ₗ[ℝ] ℝ) (ν : Fin q → W),
        (∀ i, LinearSecondFormGoodCovector B.toLinearMap (ξ i) ∧
          ν i ∈ supportedRankLegalValueSpace B.toLinearMap (ξ i)) ∧
        LinearIndependent ℝ (fun i ↦ (fderiv ℝ chart.equation B)
          (supportedRankLegalVariation (ξ i) (ν i)).toContinuousLinearMap) := by
  classical
  dsimp only
  obtain ⟨chart, hrank⟩ := (legal_normal_rank_of_supported_kernels hn hW).2
    B ⟨hB, hphase⟩ hsupported
  let S : Set (Fin chart.codim → ℝ) :=
    {v | ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
      ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
        v = (fderiv ℝ chart.equation B)
          (supportedRankLegalVariation ξ ν).toContinuousLinearMap}
  have hr : finrank ℝ V * (finrank ℝ V - 1) / 2 ≤
      finrank ℝ (Submodule.span ℝ S) := hrank
  obtain ⟨v, hv, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  let j : Fin (finrank ℝ V * (finrank ℝ V - 1) / 2) →
      Fin (finrank ℝ (Submodule.span ℝ S)) := Fin.castLE hr
  have hmem (i : Fin (finrank ℝ V * (finrank ℝ V - 1) / 2)) :
      ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ ∧
        ∃ ν : W, ν ∈ supportedRankLegalValueSpace B.toLinearMap ξ ∧
          v (j i) = (fderiv ℝ chart.equation B)
            (supportedRankLegalVariation ξ ν).toContinuousLinearMap := hv (j i)
  choose ξ hξ ν hν hcol using hmem
  refine ⟨chart, ξ, ν, fun i ↦ ⟨hξ i, hν i⟩, ?_⟩
  have hind : LinearIndependent ℝ (fun i ↦ v (j i)) :=
    hli.comp j (Fin.castLE_injective hr)
  simpa only [hcol] using hind

#print axioms exists_supported_legal_equation_packet

end GlobalEmbedding.Upgrade
