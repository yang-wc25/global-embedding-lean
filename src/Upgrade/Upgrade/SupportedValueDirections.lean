import GlobalEmbedding.Targets.QuadraticSaturation
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Actual legal value directions supplied by saturation

Source: `thm:upgrade`, main.tex 1076 and 1078--1085. The strong accepted
saturation classification is used unchanged. Its literal supremum of legal
value spaces yields generators which remain individual legal waves, so the
selected directions can be extended by the existing local legal-wave theorem.
-/

noncomputable section
open Module Set
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The accepted literal legal-value supremum equals the span of its actual
legal generators. This identity keeps the actual covector attached to each
normal vector, for subsequent local-wave construction. -/
theorem saturationLegalValueSpan_eq_generator_span (B : SymmetricSquare V →ₗ[ℝ] W) :
    saturationLegalValueSpan B = Submodule.span ℝ
      {ν : W | ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap ∧
        ν ∈ supportedRankLegalValueSpace B ξ.toLinearMap} := by
  apply le_antisymm
  · apply iSup_le
    intro ξ ν hν
    exact Submodule.subset_span ⟨ξ.val, ξ.property, hν⟩
  · apply Submodule.span_le.mpr
    rintro ν ⟨ξ, hξ, hν⟩
    have hle : supportedRankLegalValueSpace B ξ.toLinearMap ≤
        saturationLegalValueSpan B :=
      le_iSup (fun ξ : {ξ : V →L[ℝ] ℝ //
        LinearSecondFormGoodCovector B ξ.toLinearMap} ↦
        supportedRankLegalValueSpace B ξ.val.toLinearMap) ⟨ξ, hξ⟩
    exact hle hν

omit [FiniteDimensional ℝ V] in
/-- Select individual legal generators from the existing saturation span,
using the native finite basis-subset theorem. This is a finite selection
operation; it does not assume an incidence derivative rank. -/
theorem exists_legal_value_frame_of_saturation
    (B : SymmetricSquare V →ₗ[ℝ] W) {r : ℕ}
    (hr : r ≤ finrank ℝ (saturationLegalValueSpan B)) :
    ∃ (ξ : Fin r → V →L[ℝ] ℝ) (ν : Fin r → W),
      (∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap ∧
        ν i ∈ supportedRankLegalValueSpace B (ξ i).toLinearMap) ∧
      LinearIndependent ℝ ν := by
  classical
  let S : Set W := {ν | ∃ ξ : V →L[ℝ] ℝ,
    LinearSecondFormGoodCovector B ξ.toLinearMap ∧
      ν ∈ supportedRankLegalValueSpace B ξ.toLinearMap}
  have hr' : r ≤ finrank ℝ (Submodule.span ℝ S) := by
    rw [saturationLegalValueSpan_eq_generator_span] at hr
    exact hr
  obtain ⟨v, hv, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  let j : Fin r → Fin (finrank ℝ (Submodule.span ℝ S)) := Fin.castLE hr'
  have hmem (i : Fin r) : ∃ ξ : V →L[ℝ] ℝ,
      LinearSecondFormGoodCovector B ξ.toLinearMap ∧
        v (j i) ∈ supportedRankLegalValueSpace B ξ.toLinearMap := hv (j i)
  choose ξ hξ hν using hmem
  exact ⟨ξ, fun i ↦ v (j i), fun i ↦ ⟨hξ i, hν i⟩,
    hli.comp j (Fin.castLE_injective hr')⟩

/-- An actual full-rank supported second form supplies n individual,
independent legal value normals. In dimension three these are the three
value-normal columns for the JOINT supported-coincidence incidence. -/
theorem exists_supported_legal_value_frame
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hphase : LinearSecondFormPhaseRegular B) (honto : Function.Surjective B)
    (hn : 3 ≤ finrank ℝ V)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1)
    (hsupported : HasSupportedKernel B) :
    ∃ (ξ : Fin (finrank ℝ V) → V →L[ℝ] ℝ) (ν : Fin (finrank ℝ V) → W),
      (∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap ∧
        ν i ∈ supportedRankLegalValueSpace B (ξ i).toLinearMap) ∧
      LinearIndependent ℝ ν := by
  have hdim := symmetricSquare_surjective_kernel_finrank B honto hW
  have hd : 1 ≤ finrank ℝ B.ker := by omega
  obtain ⟨U, hU, hK⟩ := hsupported
  have hs := ((quadratic_saturation_and_legal_value_span B hphase hd).2.2.2
    honto hn hW).2.1 U hU hK
  apply exists_legal_value_frame_of_saturation B
  exact hs.2.1.ge

/-- Once the actual supported locus has been excluded, saturation supplies
n+1 individual legal value normals. This is the final coincidence operation's
geometric input, with no independent-normal-frame hypothesis added. -/
theorem exists_nonsupported_legal_value_frame
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hphase : LinearSecondFormPhaseRegular B) (honto : Function.Surjective B)
    (hn : 3 ≤ finrank ℝ V)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1)
    (hnonsupported : ¬ HasSupportedKernel B) :
    ∃ (ξ : Fin (finrank ℝ V + 1) → V →L[ℝ] ℝ)
      (ν : Fin (finrank ℝ V + 1) → W),
      (∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap ∧
        ν i ∈ supportedRankLegalValueSpace B (ξ i).toLinearMap) ∧
      LinearIndependent ℝ ν := by
  have hdim := symmetricSquare_surjective_kernel_finrank B honto hW
  have hd : 1 ≤ finrank ℝ B.ker := by omega
  apply exists_legal_value_frame_of_saturation B
  exact ((quadratic_saturation_and_legal_value_span B hphase hd).2.2.2
    honto hn hW).2.2 hnonsupported

#print axioms saturationLegalValueSpan_eq_generator_span
#print axioms exists_legal_value_frame_of_saturation
#print axioms exists_supported_legal_value_frame
#print axioms exists_nonsupported_legal_value_frame

end GlobalEmbedding.Upgrade
