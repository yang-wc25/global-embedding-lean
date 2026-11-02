import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic

/-!
# Passing the actual legal kernel-variation span to the support-motion quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`prop:supported-rank`, lines 1027–1029. These are finite-dimensional consumer adapters
for the literal `Hom(K,Z)` normal-coordinate space, using native rank-nullity.
-/

namespace GlobalEmbedding.Paper

variable {K Z : Type*} [AddCommGroup K] [Module ℝ K] [FiniteDimensional ℝ K]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- Quotienting the legal span by at most `d` support-motion dimensions loses at most `d`.

Proof: restrict the actual quotient map to the actual legal subspace. Its kernel
embeds into the support-motion subspace by the literal inclusion. Native rank-nullity
and injective dimension monotonicity give the asserted lower bound, also when either
subspace or either numerical bound is zero.
Source: `prop:supported-rank`, the final normal-quotient dimension computation. -/
theorem supportedRank_normal_quotient_bound
    (L T : Submodule ℝ (K →ₗ[ℝ] Z)) (q d : ℕ)
    (hL : q + d ≤ Module.finrank ℝ L) (hT : Module.finrank ℝ T ≤ d) :
    q ≤ Module.finrank ℝ (L.map T.mkQ) := by
  let f := T.mkQ.comp L.subtype
  let j : f.ker →ₗ[ℝ] T :=
    { toFun := fun x ↦ ⟨x.val.val, by
        have hx := x.property
        change T.mkQ x.val.val = 0 at hx
        exact (Submodule.Quotient.mk_eq_zero T).mp hx⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hj : Function.Injective j := by
    intro x y h
    have hxy : x.val.val = y.val.val := congrArg (fun z : T ↦ z.val) h
    exact Subtype.ext (Subtype.ext hxy)
  have hker : Module.finrank ℝ f.ker ≤ d :=
    (LinearMap.finrank_le_finrank_of_injective hj).trans hT
  have hrange : f.range = L.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange] at hrank
  omega

/-- The same normal lower bound after the fixed invertible compression transform.

Proof: a genuine linear equivalence preserves the legal span dimension. Apply the
preceding actual quotient-map bound; the support-motion subspace is kept fixed.
Source: `prop:supported-rank`, fixed positive compression followed by support-motion quotient. -/
theorem supportedRank_transformed_normal_quotient_bound
    (L T : Submodule ℝ (K →ₗ[ℝ] Z)) (e : (K →ₗ[ℝ] Z) ≃ₗ[ℝ] (K →ₗ[ℝ] Z))
    (q d : ℕ) (hL : q + d ≤ Module.finrank ℝ L) (hT : Module.finrank ℝ T ≤ d) :
    q ≤ Module.finrank ℝ ((L.map e.toLinearMap).map T.mkQ) := by
  apply supportedRank_normal_quotient_bound _ T q d _ hT
  rwa [e.finrank_map_eq]

#print axioms supportedRank_normal_quotient_bound
#print axioms supportedRank_transformed_normal_quotient_bound

end GlobalEmbedding.Paper
