import GlobalEmbedding.Paper.QuadraticSpaceEvaluationFrame
import GlobalEmbedding.Paper.SymmetricOperatorDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Full real quadratic-space dimension inequality, revised1779–1814.
All maximum-rank, good-point, frame, coefficients and support facts are constructed.
The equality classification continues in a separate extension after this bound. -/

noncomputable section
open Module
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The literal subspace of actual selfadjoint operators supported on U.
This is a submodule of the existing endomorphism carrier, not a new tensor model. -/
def quadraticSpaceSupportedOperators (U : Submodule ℝ V) : Submodule ℝ (V →L[ℝ] V) where
  carrier := {Q | Q.toLinearMap.IsSymmetric ∧ ∀ v, Q v ∈ U}
  zero_mem' := ⟨LinearMap.IsSymmetric.zero, fun _ ↦ by simp⟩
  add_mem' hQ hR := ⟨hQ.1.add hR.1, fun v ↦ U.add_mem (hQ.2 v) (hR.2 v)⟩
  smul_mem' a _ hQ := ⟨LinearMap.IsSymmetric.smul (by simp) hQ.1,
    fun v ↦ U.smul_mem a (hQ.2 v)⟩

/-- The sharp bound for the entire literal supported selfadjoint submodule. -/
theorem quadraticSpaceSupportedOperators_finrank_le (U : Submodule ℝ V) :
    finrank ℝ (quadraticSpaceSupportedOperators U) ≤
      finrank ℝ U * (finrank ℝ U + 1) / 2 :=
  quadraticSpace_finrank_le_of_supported (quadraticSpaceSupportedOperators U).subtype
    Subtype.val_injective (fun Q ↦ Q.property.1) U (fun Q ↦ Q.property.2)

/-- The exact codimension-one space used in the kernel estimate, derived from
one actual nonorthogonal value, rather than an additional hyperplane hypothesis. -/
theorem quadraticSpace_support_hyperplane_finrank
    (U : Submodule ℝ V) (x₀ : V) (u : U) (hu : inner ℝ (u : V) x₀ ≠ 0) :
    finrank ℝ (U ⊓ (ℝ ∙ x₀)ᗮ : Submodule ℝ V) + 1 = finrank ℝ U := by
  let E := U ⊓ (ℝ ∙ x₀)ᗮ
  let L : U →ₗ[ℝ] ℝ := (innerSL ℝ x₀).toLinearMap.comp U.subtype
  have hLne : L ≠ 0 := by
    intro hL
    have hval := LinearMap.congr_fun hL u
    apply hu
    simpa [L, real_inner_comm] using hval
  have hker : L.ker = E.comap U.subtype := by
    ext v
    change inner ℝ x₀ (v : V) = 0 ↔ (v : V) ∈ U ⊓ (ℝ ∙ x₀)ᗮ
    exact ⟨fun h ↦ ⟨v.property, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr h⟩,
      fun h ↦ Submodule.mem_orthogonal_singleton_iff_inner_right.mp h.2⟩
  have heqdim : finrank ℝ L.ker = finrank ℝ E := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : E ≤ U)).finrank_eq
  rw [← heqdim]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hLne

/-- The sharp estimate at an actual maximal nonorthogonal evaluation point.
All local analytic prerequisites are proved in the imported canonical providers.
Source: revised1795–1814. -/
theorem quadraticSpace_dimension_bound_at_nonorthogonal
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (x₀ : V)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤
        finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap))
    (Q₀ : V →L[ℝ] V) (hQ₀ : Q₀ ∈ P) (hquad : inner ℝ (Q₀ x₀) x₀ ≠ 0) :
    finrank ℝ P ≤
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) *
        (finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x₀).toLinearMap) + 1) / 2 := by
  let T := (quadraticSpaceEvaluation P x₀).toLinearMap
  let U := T.range
  let E := U ⊓ (ℝ ∙ x₀)ᗮ
  let K := T.ker
  have : FiniteDimensional ℝ (V →L[ℝ] V) := inferInstance
  have : FiniteDimensional ℝ P := inferInstance
  have : FiniteDimensional ℝ K := inferInstance
  let F : K →ₗ[ℝ] (V →L[ℝ] V) := P.subtype.comp K.subtype
  have hFinj : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hFsym (a : K) : (F a).toLinearMap.IsSymmetric := hP a.val.val a.val.property
  have hFrange (a : K) (v : V) : F a v ∈ E := by
    have hz : (a.val : V →L[ℝ] V) x₀ = 0 := a.property
    have hr := quadraticSpace_maximal_kernel_range P x₀ hmax
      (a.val : V →L[ℝ] V) a.val.property hz
    exact quadraticSpace_kernel_range_supported (F a) (hFsym a) hz U hr v
  have hbound : finrank ℝ K ≤ finrank ℝ E * (finrank ℝ E + 1) / 2 :=
    quadraticSpace_finrank_le_of_supported (V := V) (M := K) F hFinj hFsym E hFrange
  have hE : finrank ℝ E + 1 = finrank ℝ U :=
    quadraticSpace_support_hyperplane_finrank U x₀ ⟨Q₀ x₀, ⟨⟨Q₀, hQ₀⟩, rfl⟩⟩ hquad
  have htri (m : ℕ) : (m + 1) + m * (m + 1) / 2 =
      (m + 1) * ((m + 1) + 1) / 2 := by
    simpa [Nat.choose_two_right, Nat.mul_comm, Nat.add_assoc] using
      (Nat.choose_succ_succ' (m + 1) 1).symm
  calc
    finrank ℝ P = finrank ℝ U + finrank ℝ K := T.finrank_range_add_finrank_ker.symm
    _ ≤ finrank ℝ U + finrank ℝ E * (finrank ℝ E + 1) / 2 :=
      Nat.add_le_add_left hbound _
    _ = finrank ℝ U * (finrank ℝ U + 1) / 2 := by
      rw [← hE]
      exact htri (finrank ℝ E)

/-- FULL dimension inequality for a real selfadjoint operator space whose actual
evaluation ranks are bounded by d. In particular it applies when d is their maximum.
No local good point, frame, solver or extra support is a final hypothesis.
Source: revised lemma1779–1814. -/
theorem quadraticSpace_dimension_bound
    (P : Submodule ℝ (V →L[ℝ] V))
    (hP : ∀ Q ∈ P, Q.toLinearMap.IsSymmetric) (d : ℕ)
    (hmax : ∀ x : V,
      finrank ℝ (LinearMap.range (quadraticSpaceEvaluation P x).toLinearMap) ≤ d) :
    finrank ℝ P ≤ d * (d + 1) / 2 := by
  by_cases hbot : P = ⊥
  · rw [hbot, finrank_bot]
    exact Nat.zero_le _
  obtain ⟨x₀, hmax₀, Q₀, hQ₀, hquad⟩ :=
    quadraticSpace_exists_maximal_nonorthogonal P hP hbot
  have hb := quadraticSpace_dimension_bound_at_nonorthogonal P hP x₀ hmax₀ Q₀ hQ₀ hquad
  exact hb.trans (Nat.div_le_div_right
    (Nat.mul_le_mul (hmax x₀) (Nat.add_le_add_right (hmax x₀) 1)))

#print axioms quadraticSpaceSupportedOperators
#print axioms quadraticSpaceSupportedOperators_finrank_le
#print axioms quadraticSpace_support_hyperplane_finrank
#print axioms quadraticSpace_dimension_bound_at_nonorthogonal
#print axioms quadraticSpace_dimension_bound

end GlobalEmbedding.Paper
