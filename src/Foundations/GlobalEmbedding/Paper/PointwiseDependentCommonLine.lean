import GlobalEmbedding.Paper.PointwiseDependentMaps
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Common image line from actual pointwise dependence, revised1828–1840. -/
noncomputable section
open Module
namespace GlobalEmbedding.Paper
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Dependence at x and x+v also controls vectors in ker A. Consequently the
actual image of every companion lies in range A whenever A is nonzero. -/
theorem quadraticSpace_range_le_of_pointwise_dependent
    (A B : V →ₗ[ℝ] W) (hA : A ≠ 0)
    (hdep : ∀ v, ¬ LinearIndependent ℝ ![A v, B v]) : B.range ≤ A.range := by
  have hex : ∃ x, A x ≠ 0 := by
    by_contra! hh
    exact hA (LinearMap.ext hh)
  obtain ⟨x, hx⟩ := hex
  have hgood (v : V) (hv : A v ≠ 0) : B v ∈ A.range := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (quadraticSpace_mem_span_of_dependent hv (hdep v))
    rw [← hc]
    exact A.range.smul_mem c ⟨v, rfl⟩
  rintro _ ⟨v, rfl⟩
  by_cases hv : A v = 0
  · have hxv : A (x + v) ≠ 0 := by simpa [map_add, hv] using hx
    have hh := A.range.sub_mem (hgood (x + v) hxv) (hgood x hx)
    simpa [map_add] using hh
  · exact hgood v hv

/-- A pointwise-collinear space of dimension at least two contains only maps of
rank at most one: a higher-rank member would force every member to be its scalar
multiple by the already proved, genuinely factored native homothety argument. -/
theorem quadraticSpace_range_finrank_le_one
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (L : Submodule ℝ (V →ₗ[ℝ] W)) (hdim : 2 ≤ finrank ℝ L)
    (hdep : ∀ A ∈ L, ∀ B ∈ L, ∀ v, ¬ LinearIndependent ℝ ![A v, B v]) :
    ∀ A ∈ L, finrank ℝ A.range ≤ 1 := by
  intro A hA
  by_contra! hrank
  have : Nontrivial A.range := nontrivial_of_finrank_pos (hrank.trans_le' (by omega))
  obtain ⟨u, hu⟩ := exists_ne (0 : A.range)
  obtain ⟨v, huv⟩ := exists_linearIndependent_pair_of_one_lt_finrank hrank hu
  have huv' := huv.map' A.range.subtype (by simp)
  obtain ⟨x, hx⟩ := u.property
  obtain ⟨y, hy⟩ := v.property
  have hxy : LinearIndependent ℝ ![A x, A y] := by
    convert huv' using 1
    ext i
    fin_cases i <;> simp [hx, hy]
  have hdim' : finrank ℝ L ≤ 1 := finrank_le_one (⟨A, hA⟩ : L) (fun B ↦ by
    obtain ⟨c, hc⟩ := quadraticSpace_eq_smul_of_pointwise_dependent A B.val hxy
      (hdep A hA B.val B.property)
    exact ⟨c, Subtype.ext hc.symm⟩)
  omega

/-- FULL common-image-line lemma. The line is obtained from the original
pointwise dependence and dimension>=2; neither rank one nor common support is
postulated as a premise. Source: revised1836–1840. -/
theorem quadraticSpace_common_image_line
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (L : Submodule ℝ (V →ₗ[ℝ] W)) (hdim : 2 ≤ finrank ℝ L)
    (hdep : ∀ A ∈ L, ∀ B ∈ L, ∀ v, ¬ LinearIndependent ℝ ![A v, B v]) :
    ∃ f : W, f ≠ 0 ∧ ∀ B ∈ L, B.range ≤ ℝ ∙ f := by
  have hL : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨A, hA, hAne⟩ := L.ne_bot_iff.mp hL
  have hex : ∃ x, A x ≠ 0 := by
    by_contra! hh
    exact hAne (LinearMap.ext hh)
  obtain ⟨x, hx⟩ := hex
  have hle : (ℝ ∙ A x : Submodule ℝ W) ≤ A.range :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨x, rfl⟩
  have heq : (ℝ ∙ A x : Submodule ℝ W) = A.range :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [finrank_span_singleton hx]
      exact quadraticSpace_range_finrank_le_one L hdim hdep A hA)
  refine ⟨A x, hx, fun B hB ↦ ?_⟩
  rw [heq]
  exact quadraticSpace_range_le_of_pointwise_dependent A B hAne (hdep A hA B hB)

#print axioms quadraticSpace_range_le_of_pointwise_dependent
#print axioms quadraticSpace_range_finrank_le_one
#print axioms quadraticSpace_common_image_line
end GlobalEmbedding.Paper
