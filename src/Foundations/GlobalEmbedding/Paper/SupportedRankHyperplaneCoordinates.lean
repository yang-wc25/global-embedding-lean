import GlobalEmbedding.Paper.SupportedRankSymmetricSquareSplitting
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual coordinates of the original supporting hyperplane

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1007–1027. This only specializes native orthogonal direct-sum coordinates to
the SAME original supporting hyperplane. No coordinate norm or carrier is replaced.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The actual nonzero orthogonal vector parametrizes the entire original complement.
Proof: the complement has dimension one by the exact hyperplane condition. Actual
scalar multiplication by a nonzero vector is injective, hence bijective between
these finite-dimensional spaces. Source: `prop:supported-rank`, `V=U⊕ℝe`. -/
def supportedRankOrthogonalLineEquiv (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) : ℝ ≃ₗ[ℝ] Uᗮ := by
  let f := LinearMap.toSpanSingleton ℝ Uᗮ ⟨e, he⟩
  have hdim : Module.finrank ℝ ℝ = Module.finrank ℝ Uᗮ := by
    have hd := U.finrank_add_finrank_orthogonal
    simp only [Module.finrank_self]
    omega
  have hf : Function.Injective f := by
    intro a b hab
    apply smul_left_injective ℝ he0
    exact congrArg (fun v : Uᗮ ↦ (v : V)) hab
  exact LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

/-- Native orthogonal direct-sum coordinates for the actual original hyperplane.
Source: `prop:supported-rank`, the SAME splitting used by the actual mixed columns. -/
def supportedRankHyperplaneCoordinates (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) : (U × ℝ) ≃ₗ[ℝ] V :=
  ((LinearEquiv.refl ℝ U).prodCongr
    (supportedRankOrthogonalLineEquiv U hU e he he0)).trans
      (U.prodEquivOfIsCompl Uᗮ U.isCompl_orthogonal)

/-- The actual coordinates are the literal sum `u+t e`.
Source: `prop:supported-rank`, original lifted-family parametrization. -/
@[simp] theorem supportedRankHyperplaneCoordinates_apply (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) (u : U) (t : ℝ) :
    supportedRankHyperplaneCoordinates U hU e he he0 (u, t) = (u : V) + t • e := rfl

/-- The scalar-coordinate vector is the SAME chosen original orthogonal vector.
Source: `prop:supported-rank`, original mixed summand `Z=e⊙V`. -/
@[simp] theorem supportedRankHyperplaneCoordinates_vector (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) :
    supportedRankSplitVector (supportedRankHyperplaneCoordinates U hU e he he0) = e := by
  simp [supportedRankSplitVector]

/-- The hyperplane-coordinate inclusion is the original actual subtype inclusion.
Source: `prop:supported-rank`, preserving the original supported symmetric-square range. -/
@[simp] theorem supportedRankHyperplaneCoordinates_inclusion (U : Submodule ℝ V)
    (hU : Module.finrank ℝ U + 1 = Module.finrank ℝ V)
    (e : V) (he : e ∈ Uᗮ) (he0 : e ≠ 0) :
    supportedRankSplitInclusion (supportedRankHyperplaneCoordinates U hU e he he0) =
      U.subtype := by
  ext u
  simp [supportedRankSplitInclusion]

#print axioms supportedRankOrthogonalLineEquiv
#print axioms supportedRankHyperplaneCoordinates
#print axioms supportedRankHyperplaneCoordinates_apply
#print axioms supportedRankHyperplaneCoordinates_vector
#print axioms supportedRankHyperplaneCoordinates_inclusion

end GlobalEmbedding.Paper
