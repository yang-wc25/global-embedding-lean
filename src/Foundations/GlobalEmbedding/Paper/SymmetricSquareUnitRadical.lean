import GlobalEmbedding.Paper.SymmetricSquareOperatorSupport
import GlobalEmbedding.Paper.SupportedLocusLocalEquations

/-!
# Literal supported kernels and actual unit common radicals

Source: original `prop:supported-rank`, lines 1004–1012.
DAG: `supported-kernel-unit-radical-dictionary`. Exclusive worker W2.
This is the quotient/operator dictionary consumed by W3's closed-incidence theorem.
It does not construct a second locus predicate, geometry chart or good evaluation E/J.
-/

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Support on the actual orthogonal hyperplane is exactly actual annihilation at e.
Source: original common-radical description, with the same binary quotient.
This fixed-vector identity also includes e=0. -/
theorem symmetricSquare_mem_perp_range_iff_operator_kills (q : SymmetricSquare V) (e : V) :
    q ∈ LinearMap.range (symmetricSquareLinearMap (ℝ ∙ e)ᗮ.subtype) ↔
      (symmetricSquareToSelfAdjoint q).val e = 0 := by
  rw [symmetricSquare_mem_range_iff_operator_range]
  constructor
  · intro hr
    have he : e ∈ ((ℝ ∙ e)ᗮ)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro x hx
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx
    exact quadraticSpace_kills_orthogonal (symmetricSquareToSelfAdjoint q).val
      (symmetricSquareToSelfAdjoint q).property.isSymmetric (ℝ ∙ e)ᗮ hr he
  · intro he y hy
    obtain ⟨x, rfl⟩ := hy
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    change inner ℝ ((symmetricSquareToSelfAdjoint q).val x) e = 0
    calc
      _ = inner ℝ x ((symmetricSquareToSelfAdjoint q).val e) :=
        (symmetricSquareToSelfAdjoint q).property.isSymmetric x e
      _ = 0 := by rw [he, inner_zero_right]

/-- The canonical literal support predicate is precisely existence of an actual unit
common radical of ALL forms in the SAME kernel. Source: `prop:supported-rank`.
No phase regularity, chosen orientation, good-point/J or desired closedness is a premise. -/
theorem hasSupportedKernel_iff_unit_common_radical
    {W : Type*} [AddCommGroup W] [Module ℝ W] (B : SymmetricSquare V →ₗ[ℝ] W) :
    HasSupportedKernel B ↔
      ∃ e : V, ‖e‖ = 1 ∧ ∀ q ∈ B.ker, (symmetricSquareToSelfAdjoint q).val e = 0 := by
  constructor
  · rintro ⟨U, hdim, hK⟩
    have hp : 0 < Module.finrank ℝ Uᗮ := by
      have h := U.finrank_add_finrank_orthogonal
      omega
    obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := Uᗮ)).mp hp
    let e₀ : Uᗮ := ‖v‖⁻¹ • v
    have he₀ : ‖e₀‖ = 1 := by simp [e₀, norm_smul, hv]
    refine ⟨e₀.val, he₀, ?_⟩
    intro q hq
    have hr := (symmetricSquare_mem_range_iff_operator_range U q).mp (hK hq)
    exact quadraticSpace_kills_orthogonal (symmetricSquareToSelfAdjoint q).val
      (symmetricSquareToSelfAdjoint q).property.isSymmetric U hr e₀.property
  · rintro ⟨e, hunit, he⟩
    have hne : e ≠ 0 := by
      intro h
      simp [h] at hunit
    refine ⟨(ℝ ∙ e)ᗮ, ?_, ?_⟩
    · have hd := (ℝ ∙ e).finrank_add_finrank_orthogonal
      have hs := finrank_span_singleton (K := ℝ) hne
      omega
    · intro q hq
      exact (symmetricSquare_mem_perp_range_iff_operator_kills q e).mpr (he q hq)

end GlobalEmbedding.Paper
