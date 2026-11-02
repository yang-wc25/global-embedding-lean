import GlobalEmbedding.Paper.SymmetricSquareFinrank
import GlobalEmbedding.Paper.SupportedRankGoodLiftedFamily
import GlobalEmbedding.Paper.SupportedRankLocalSyzygySpan
import GlobalEmbedding.Paper.SymmetricSquareCovectorEvaluation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual original rank-q pointwise legal normal span

Source: `literature/parallelizable-stable-plus-one/main.tex`, `thm:upgrade`,
lines 1053–1057. This is only the genuine pointwise algebra child; actual local
wave extensions, cutoffs, distant-point support and Schur/probe incidence remain
obligations of the original parent. DAG: `upgrade-rank-q-pointwise-legal-span`.
-/

noncomputable section

open Module

namespace GlobalEmbedding.Paper

/-- At an actual original rank-q second form, its actual kernel has dimension n,
the perpendicular of its actual range inside the original normal fiber W is a
line, every original good covector has exactly that legal value space, and the
literal legal rank-normal blocks span the full Hom from the SAME kernel to line.

Proof: apply the sole original binary quotient dimension and native rank-nullity.
For a good covector, the actual injective restricted image and range B both have
dimension q, hence coincide. Choose the original phase witness and its Riesz point.
Apply the existing evaluation equivalence, doubled dual and actual open good
family with support U=top, whose dimension is the derived dim ker B=n. The sole
local quadratic evaluation span theorem gives the full dual of ker B. Identify
those functionals with literal original covector squares by the accepted operator
dictionary. Multiply by one nonzero vector of the actual normal line: the native
smulRight linear map is injective and, by equal dimensions, surjective. Its image
of the proved evaluation span lies in the stated actual legal block span.
No desired span, extra good point or local geometric extension is assumed.
Source: original `thm:upgrade`, main.tex1053–1057. -/
theorem upgradeRankQ_pointwise_legal_span
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hphase : LinearSecondFormPhaseRegular B)
    (hn : 3 ≤ finrank ℝ V)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1)
    (hrank : finrank ℝ B.range = finrank ℝ V * (finrank ℝ V - 1) / 2) :
    finrank ℝ B.ker = finrank ℝ V ∧
      finrank ℝ B.rangeᗮ = 1 ∧
      (∀ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B ξ →
        supportedRankLegalValueSpace B ξ = B.rangeᗮ) ∧
      Submodule.span ℝ
        {f : B.ker →ₗ[ℝ] B.rangeᗮ |
          ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B ξ ∧
            ∃ ν : B.rangeᗮ,
              f = ((supportedRankCovectorSquare ξ).domRestrict B.ker).smulRight ν} = ⊤ := by
  classical
  have hdK : finrank ℝ B.ker = finrank ℝ V := by
    have hr := B.finrank_range_add_finrank_ker
    rw [hrank, symmetricSquare_finrank] at hr
    have hc : (finrank ℝ V + 1).choose 2 =
        finrank ℝ V + (finrank ℝ V).choose 2 := by
      simpa only [Nat.choose_one_right, Nat.succ_eq_add_one] using
        Nat.choose_succ_succ (finrank ℝ V) 1
    rw [Nat.choose_two_right, Nat.choose_two_right] at hc
    simp only [Nat.add_sub_cancel] at hc
    rw [Nat.mul_comm (finrank ℝ V + 1) (finrank ℝ V)] at hc
    omega
  have hdL : finrank ℝ B.rangeᗮ = 1 := by
    have h := B.range.finrank_add_finrank_orthogonal
    rw [hrank, hW] at h
    omega
  have hlegal : ∀ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B ξ →
      supportedRankLegalValueSpace B ξ = B.rangeᗮ := by
    intro ξ hg
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hg.1
    have hq : finrank ℝ (SymmetricSquare ξ.ker) =
        finrank ℝ V * (finrank ℝ V - 1) / 2 := by
      rw [symmetricSquare_finrank, ← hk]
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm]
    have hi := LinearMap.finrank_range_of_inj
      (f := B.comp (symmetricSquareLinearMap ξ.ker.subtype)) hg.2
    have he : (B.comp (symmetricSquareLinearMap ξ.ker.subtype)).range = B.range :=
      Submodule.eq_of_le_of_finrank_eq (LinearMap.range_comp_le_range _ _) (hi.trans hq |>.trans
        hrank.symm)
    exact congrArg Submodule.orthogonal he
  refine ⟨hdK, hdL, hlegal, ?_⟩
  let U : Submodule ℝ V := ⊤
  have hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range := by
    intro k hk
    exact (symmetricSquare_mem_range_iff_operator_range U k).mpr le_top
  have hdim : finrank ℝ B.ker = finrank ℝ U := by simpa only [U, finrank_top] using hdK
  have hpos : 0 < finrank ℝ U := by simp only [U, finrank_top]; omega
  obtain ⟨ξ, hgξ⟩ := hphase
  obtain ⟨x, _, hg⟩ := supportedRank_good_covector_riesz B ξ hgξ
  obtain ⟨Ω, hΩ, hz, _, hgood⟩ :=
    supportedRank_exists_good_lifted_family B U hK x hg hdim hpos
  let Q := supportedRankKernelQuadratic B U
  let a := supportedRankQuadraticEvaluation Q
  let J := supportedRankGoodKernelDualEquiv B U hK x hg hdim
  have hJ : ∀ v k, J v k = 2 * Q k (U.orthogonalProjectionOnto x) v :=
    supportedRankGoodKernelDualEquiv_apply B U hK x hg hdim
  have hspan : Submodule.span ℝ (a '' Ω) = ⊤ :=
    supportedRank_local_evaluation_span Q (supportedRankKernelQuadratic_symm B U)
      Ω hΩ (U.orthogonalProjectionOnto x) hz J hJ
  have ha (z : U) : a z =
      (supportedRankCovectorSquare (innerₗ V (z : V))).domRestrict B.ker := by
    ext k
    exact (supportedRankCovectorSquare_inner_eq_operator (k : SymmetricSquare V) (z : V)).symm
  have hgoodz (z : U) (hz : z ∈ Ω) :
      LinearSecondFormGoodCovector B (innerₗ V (z : V)) := by
    simpa only [zero_smul, add_zero] using hgood z hz 0 (Submodule.zero_mem _) 0
  let L : Submodule ℝ W := B.rangeᗮ
  obtain ⟨ν, hν⟩ : ∃ ν : L, ν ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by change 0 < finrank ℝ B.rangeᗮ; omega)
  let T : Module.Dual ℝ B.ker →ₗ[ℝ] B.ker →ₗ[ℝ] L :=
    (LinearMap.smulRightₗ : Module.Dual ℝ B.ker →ₗ[ℝ] L →ₗ[ℝ] B.ker →ₗ[ℝ] L).flip ν
  have hTi : Function.Injective T := by
    intro f g h
    ext k
    exact smul_left_injective ℝ hν (LinearMap.congr_fun h k)
  have hdT : finrank ℝ (Module.Dual ℝ B.ker) = finrank ℝ (B.ker →ₗ[ℝ] L) := by
    change finrank ℝ (B.ker →ₗ[ℝ] ℝ) = finrank ℝ (B.ker →ₗ[ℝ] L)
    simp only [Module.finrank_linearMap, Module.finrank_self, L, hdL, mul_one]
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdT).mp hTi
  let S := Submodule.span ℝ
    {f : B.ker →ₗ[ℝ] L |
      ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B ξ ∧
        ∃ ν : L, f = ((supportedRankCovectorSquare ξ).domRestrict B.ker).smulRight ν}
  change S = ⊤
  have himage : (Submodule.span ℝ (a '' Ω)).map T ≤ S := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨innerₗ V (z : V), hgoodz z hz, ν, ?_⟩
    change T (a z) = _
    rw [ha]
    rfl
  rw [hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hTs] at himage
  exact le_antisymm le_top himage

#print axioms upgradeRankQ_pointwise_legal_span

end GlobalEmbedding.Paper
