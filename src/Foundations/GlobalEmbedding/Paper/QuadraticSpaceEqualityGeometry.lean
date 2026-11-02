import GlobalEmbedding.Paper.QuadraticSpaceKernelSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual supported evaluation and the real open-set extension in revised1820–1827. -/
noncomputable section
open InnerProductSpace
namespace GlobalEmbedding.Paper
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual symmetric rank-two operator realizing one supported evaluation. -/
theorem quadraticSpace_supported_evaluation_unit
    (U : Submodule ℝ V) (x u w : V) (hu : u ∈ U) (hw : w ∈ U)
    (hux : inner ℝ u x = 1) :
    ∃ Q : V →L[ℝ] V, Q.toLinearMap.IsSymmetric ∧
      (∀ v, Q v ∈ U) ∧ Q x = w := by
  let Q := rankOne ℝ w u + rankOne ℝ u w - inner ℝ w x • rankOne ℝ u u
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro v z
    change inner ℝ (Q v) z = inner ℝ v (Q z)
    simp only [Q, sub_apply, add_apply,
      smul_apply, rankOne_apply, inner_sub_left, inner_add_left,
      inner_smul_left, inner_sub_right, inner_add_right, inner_smul_right, conj_trivial]
    simp only [real_inner_comm]
    ring
  · intro v
    exact U.sub_mem
      (U.add_mem (U.smul_mem _ hw) (U.smul_mem _ hu))
      (U.smul_mem _ (U.smul_mem _ hu))
  · simp [Q, rankOne_apply, hux]

/-- All vectors in U are realized by actual supported selfadjoint evaluations
whenever x has nonzero U-component. No tensor quotient is changed or reconstructed. -/
theorem quadraticSpace_supported_evaluation_surjective
    (U : Submodule ℝ V) (x : V) (hx : x ∉ Uᗮ) :
    ∀ w ∈ U, ∃ Q : V →L[ℝ] V, Q.toLinearMap.IsSymmetric ∧
      (∀ v, Q v ∈ U) ∧ Q x = w := by
  have hex : ∃ u ∈ U, inner ℝ u x ≠ 0 := by
    by_contra! hh
    exact hx ((U.mem_orthogonal x).mpr hh)
  obtain ⟨u, hu, hux⟩ := hex
  intro w hw
  apply quadraticSpace_supported_evaluation_unit U x ((inner ℝ u x)⁻¹ • u) w
    (U.smul_mem _ hu) hw
  simp [inner_smul_left, hux]

/-- The source's minor extension may be expressed by openness of native linear
independence and empty interior of a proper real subspace. This is genuine
pointwise dependence everywhere, not merely on the good open set. -/
theorem quadraticSpace_pointwise_dependent_extension
    (U : Submodule ℝ V) (hU : U ≠ ⊥) (A B : V →L[ℝ] V)
    (hdep : ∀ x, x ∉ Uᗮ → ¬ LinearIndependent ℝ ![A x, B x]) :
    ∀ x, ¬ LinearIndependent ℝ ![A x, B x] := by
  have hc : Continuous (fun x ↦ ![A x, B x]) := by fun_prop
  have ho : IsOpen {x : V | LinearIndependent ℝ ![A x, B x]} :=
    isOpen_setOfPred_linearIndependent.preimage hc
  have hsub : {x : V | LinearIndependent ℝ ![A x, B x]} ⊆ (Uᗮ : Set V) := by
    intro x hx
    by_contra hn
    exact hdep x hn hx
  intro x hx
  have hi : x ∈ interior (Uᗮ : Set V) := interior_maximal hsub ho hx
  have ht : Uᗮ = ⊤ := Uᗮ.eq_top_of_nonempty_interior' ⟨x, hi⟩
  exact hU (U.orthogonal_eq_top_iff.mp ht)

#print axioms quadraticSpace_supported_evaluation_unit
#print axioms quadraticSpace_supported_evaluation_surjective
#print axioms quadraticSpace_pointwise_dependent_extension
end GlobalEmbedding.Paper
