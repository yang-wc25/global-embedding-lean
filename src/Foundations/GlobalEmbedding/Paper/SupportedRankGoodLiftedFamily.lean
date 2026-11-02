import GlobalEmbedding.Paper.SupportedRankGoodEvaluationDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# An actual open family of good lifted covectors for the SAME supported kernel

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012 and 1014–1027. Only the fixed original B is varied in its covector
argument; this does not reconstruct the onto-operator ambient or W3's local geometry.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Normalize the SAME actual evaluation at z by the proved evaluation inverse at x.
Both source and target are the actual support U, with its original induced norm.
Source: `prop:supported-rank`, openness of the actual good support vectors. -/
def supportedRankNormalizedEvaluation (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) : U →ₗ[ℝ] (U →L[ℝ] U) :=
  let E := supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim
  let β : U →ₗ[ℝ] (U →ₗ[ℝ] U) :=
    { toFun := fun z ↦ (supportedRankGoodKernelEvaluation B U hK (z : V)).comp E.symm.toLinearMap
      map_add' z w := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        change (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val
            ((z : V) + (w : V)) =
          (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val z +
            (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val w
        exact map_add _ _ _
      map_smul' c z := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        change (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val
            (c • (z : V)) =
          c • (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val z
        exact map_smul _ _ _ }
  (LinearMap.toContinuousLinearMap : (U →ₗ[ℝ] U) ≃ₗ[ℝ] (U →L[ℝ] U)).toLinearMap.comp β

/-- Pointwise evaluation of the actual normalized operator is literal composition.
Source: the actual evaluation inverse in `prop:supported-rank`. -/
@[simp] theorem supportedRankNormalizedEvaluation_apply (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) (z u : U) :
    supportedRankNormalizedEvaluation B U hK x hg hdim z u =
      supportedRankGoodKernelEvaluation B U hK (z : V)
        ((supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim).symm u) := rfl

/-- At the SAME projected good point the normalized evaluation is literally the identity.
Source: `prop:supported-rank`, the actual invertible good block. -/
theorem supportedRankNormalizedEvaluation_projection (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) :
    supportedRankNormalizedEvaluation B U hK x hg hdim (U.orthogonalProjectionOnto x) =
      ContinuousLinearMap.id ℝ U := by
  let E := supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change (symmetricSquareToSelfAdjoint (E.symm u : SymmetricSquare V)).val
    (U.orthogonalProjectionOnto x) = (u : V)
  rw [← supportedRankGoodKernelEvaluation_projection B U hK x (E.symm u)]
  exact congrArg (fun v : U ↦ (v : V)) (E.apply_symm_apply u)

/-- Positive actual support dimension makes the projected good point genuinely nonzero.
Proof: if it were zero, the actual evaluation equivalence would vanish on every kernel
element, contradicting surjectivity onto a nontrivial U. Source: `prop:supported-rank`. -/
theorem supportedRank_good_projection_ne_zero (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U)
    (hpos : 0 < Module.finrank ℝ U) : U.orthogonalProjectionOnto x ≠ 0 := by
  have : Nontrivial U := Module.nontrivial_of_finrank_pos hpos
  intro hz
  let E := supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨k, hk⟩ := E.surjective u
  have hzero : E k = 0 := by
    apply Subtype.ext
    change (supportedRankGoodKernelEvaluation B U hK x k : V) = 0
    rw [supportedRankGoodKernelEvaluation_projection B U hK x k, hz]
    simp
  exact hu (hk.symm.trans hzero)

/-- Supported operators have unchanged actual evaluation along the original orthogonal e-line.
Proof: the accepted actual supported operator kills U-perpendicular.
Source: `prop:supported-rank`, `K(z+te)=Kz`. -/
theorem supportedRank_kernel_operator_lift (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (k : B.ker) (z : U) (e : V) (he : e ∈ Uᗮ) (t : ℝ) :
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val ((z : V) + t • e) =
      (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val z := by
  have hr := (symmetricSquare_mem_range_iff_operator_range U k).mp (hK k.property)
  have hk := quadraticSpace_kills_orthogonal
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).property.isSymmetric U hr he
  simp only [map_add, map_smul, hk, smul_zero, add_zero]

/-- Actual injective support evaluation makes EVERY lifted original Riesz covector good.
The nonzero claim follows by pairing with z itself; the contraction injectivity is
the SAME evaluation map by the proved orthogonal-line identity.
Source: `prop:supported-rank`, good `ξ=z+te` and its original kernel restriction. -/
theorem supportedRank_good_lift_of_evaluation (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (z : U) (hz : z ≠ 0)
    (hinj : Function.Injective (supportedRankGoodKernelEvaluation B U hK (z : V)))
    (e : V) (he : e ∈ Uᗮ) (t : ℝ) :
    LinearSecondFormGoodCovector B (innerₗ V ((z : V) + t • e)) := by
  apply (linearSecondFormGoodCovector_iff_contraction B _).mpr
  constructor
  · intro hzero
    have hval := LinearMap.congr_fun hzero (z : V)
    change inner ℝ ((z : V) + t • e) (z : V) = 0 at hval
    have hez : inner ℝ e (z : V) = 0 := U.inner_left_of_mem_orthogonal z.property he
    rw [inner_add_left, real_inner_smul_left, hez, mul_zero, add_zero] at hval
    exact hz (Subtype.ext ((inner_self_eq_zero (𝕜 := ℝ)).mp hval))
  · intro k l h
    apply hinj
    apply Subtype.ext
    have hv : (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val
        ((z : V) + t • e) = (symmetricSquareToSelfAdjoint (l : SymmetricSquare V)).val
          ((z : V) + t • e) := by
      rw [symmetricSquareToSelfAdjoint_apply, symmetricSquareToSelfAdjoint_apply]
      exact h
    rw [supportedRank_kernel_operator_lift B U hK k z e he t,
      supportedRank_kernel_operator_lift B U hK l z e he t] at hv
    exact hv

/-- Construct one nonempty open support neighborhood on which ALL real lifted covectors
are genuinely good for the SAME original B.

Proof: the normalized actual evaluation is continuous and equals the identity at
the actual projected point. Pull back the native open set of invertible operators
and remove zero. Its actual injectivity implies injectivity of the original support
evaluation, then the preceding actual contraction argument proves goodness for all t.
Source: `prop:supported-rank`, the open good z-family used in the strong-span proof. -/
theorem supportedRank_exists_good_lifted_family (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U)
    (hpos : 0 < Module.finrank ℝ U) :
    ∃ Ω : Set U, IsOpen Ω ∧ U.orthogonalProjectionOnto x ∈ Ω ∧
      U.orthogonalProjectionOnto x ≠ 0 ∧
      ∀ z ∈ Ω, ∀ e : V, e ∈ Uᗮ → ∀ t : ℝ,
        LinearSecondFormGoodCovector B (innerₗ V ((z : V) + t • e)) := by
  let N := supportedRankNormalizedEvaluation B U hK x hg hdim
  let S : Set U := {z | (N z).IsInvertible}
  have hS : IsOpen S := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    N.toContinuousLinearMap.continuous
  have hz0 := supportedRank_good_projection_ne_zero B U hK x hg hdim hpos
  refine ⟨S \ {0}, hS.sdiff isClosed_singleton, ?_, hz0, ?_⟩
  · constructor
    · change (N (U.orthogonalProjectionOnto x)).IsInvertible
      rw [supportedRankNormalizedEvaluation_projection]
      exact ⟨ContinuousLinearEquiv.refl ℝ U, rfl⟩
    · simpa only [Set.mem_singleton_iff] using hz0
  · intro z hz e he t
    apply supportedRank_good_lift_of_evaluation B U hK z
      (by simpa only [Set.mem_singleton_iff] using hz.2) _ e he t
    intro k l h
    let E := supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim
    apply E.injective
    apply hz.1.injective
    change supportedRankNormalizedEvaluation B U hK x hg hdim z (E k) =
      supportedRankNormalizedEvaluation B U hK x hg hdim z (E l)
    rw [supportedRankNormalizedEvaluation_apply, supportedRankNormalizedEvaluation_apply]
    change supportedRankGoodKernelEvaluation B U hK (z : V) (E.symm (E k)) =
      supportedRankGoodKernelEvaluation B U hK (z : V) (E.symm (E l))
    rw [E.symm_apply_apply, E.symm_apply_apply]
    exact h

#print axioms supportedRankNormalizedEvaluation
#print axioms supportedRankNormalizedEvaluation_apply
#print axioms supportedRankNormalizedEvaluation_projection
#print axioms supportedRank_good_projection_ne_zero
#print axioms supportedRank_kernel_operator_lift
#print axioms supportedRank_good_lift_of_evaluation
#print axioms supportedRank_exists_good_lifted_family

end GlobalEmbedding.Paper
