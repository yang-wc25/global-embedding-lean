import GlobalEmbedding.Paper.SymmetricSquareOperatorSupport
import GlobalEmbedding.Paper.ContractionKernelDictionary
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.NormNum

/-!
# Actual good supported-kernel evaluation and its doubled dual

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012 and 1021–1029. This is the sole actual E/J consumer shared with W3.
The original quotient, actual good predicate and support dictionary are unchanged.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Every original good algebraic covector has its genuine finite-dimensional real Riesz point.
Proof: apply the native Riesz inverse to the SAME covector's canonical continuous realization.
Source: `prop:supported-rank`, the Euclidean identification used to write `Kξ=U`. -/
theorem supportedRank_good_covector_riesz (B : SymmetricSquare V →ₗ[ℝ] W)
    (ξ : V →ₗ[ℝ] ℝ) (hg : LinearSecondFormGoodCovector B ξ) :
    ∃ x : V, innerₗ V x = ξ ∧ LinearSecondFormGoodCovector B (innerₗ V x) := by
  let x := (InnerProductSpace.toDual ℝ V).symm ξ.toContinuousLinearMap
  have hx : innerₗ V x = ξ := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun l : V →L[ℝ] ℝ ↦ l v)
      ((InnerProductSpace.toDual ℝ V).apply_symm_apply ξ.toContinuousLinearMap)
  exact ⟨x, hx, hx.symm ▸ hg⟩

/-- Evaluate the actual supported kernel operators in their actual supporting subspace.
Membership uses the accepted exact quotient/operator support dictionary.
Source: `prop:supported-rank`, `Kξ=U`. -/
def supportedRankGoodKernelEvaluation (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) : B.ker →ₗ[ℝ] U where
  toFun k := ⟨(symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val x,
    ((symmetricSquare_mem_range_iff_operator_range U k).mp (hK k.property)) ⟨x, rfl⟩⟩
  map_add' k l := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, AddSubgroup.coe_add, add_apply]
  map_smul' c k := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, selfAdjoint.val_smul, smul_apply, RingHom.id_apply]

/-- The ORIGINAL good condition proves injectivity of the SAME supported evaluation.
Proof: reuse the exact original good/contraction dictionary and operator evaluation identity.
Source: `prop:supported-rank`, goodness and `Kξ=U`. -/
theorem supportedRankGoodKernelEvaluation_injective (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x)) :
    Function.Injective (supportedRankGoodKernelEvaluation B U hK x) := by
  have hi := (linearSecondFormGoodCovector_iff_contraction B (innerₗ V x)).mp hg
  intro k l h
  apply hi.2
  change contractionKernelQuotientMap (innerₗ V x) (k : SymmetricSquare V) =
    contractionKernelQuotientMap (innerₗ V x) (l : SymmetricSquare V)
  rw [← symmetricSquareToSelfAdjoint_apply, ← symmetricSquareToSelfAdjoint_apply]
  exact congrArg (fun u : U ↦ (u : V)) h

/-- The actual supported good evaluation is an equivalence when its actual dimensions agree.
The dimension equality is later supplied by the sole original dimension provider.
Source: `prop:supported-rank`, `dim K=dim U=n-1` and `Kξ=U`. -/
def supportedRankGoodKernelEvaluationEquiv (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) : B.ker ≃ₗ[ℝ] U :=
  LinearEquiv.ofBijective (supportedRankGoodKernelEvaluation B U hK x)
    ⟨supportedRankGoodKernelEvaluation_injective B U hK x hg,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (supportedRankGoodKernelEvaluation_injective B U hK x hg)⟩

/-- The original actual bilinear quadratic family on the actual support.
Source: `prop:supported-rank`, `Q(z,z)` with the SAME normalized operator dictionary. -/
def supportedRankKernelQuadratic (B : SymmetricSquare V →ₗ[ℝ] W) (U : Submodule ℝ V) :
    B.ker →ₗ[ℝ] U →ₗ[ℝ] U →ₗ[ℝ] ℝ where
  toFun k :=
    { toFun u := (innerₗ V ((symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val u)).comp
        U.subtype
      map_add' u v := by ext w; simp
      map_smul' c u := by ext w; simp }
  map_add' k l := by
    ext u v
    simp [AddSubgroup.coe_add]
  map_smul' c k := by
    ext u v
    simp [selfAdjoint.val_smul]

/-- Self-adjointness of the SAME kernel operators gives the original quadratic symmetry.
Source: `prop:supported-rank`, the actual symmetric quadratic family. -/
theorem supportedRankKernelQuadratic_symm (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (k : B.ker) (u v : U) :
    supportedRankKernelQuadratic B U k u v = supportedRankKernelQuadratic B U k v u := by
  change inner ℝ ((symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val u) v =
    inner ℝ ((symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val v) u
  exact ((symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).property.isSymmetric
    (u : V) (v : V)).trans (real_inner_comm _ _)

/-- Supported evaluation at x equals evaluation at its actual orthogonal projection onto U.
Proof: the accepted supported self-adjoint operator kills the actual orthogonal difference.
Source: `prop:supported-rank`, reducing a good vector to its support component. -/
theorem supportedRankGoodKernelEvaluation_projection (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (k : B.ker) :
    (supportedRankGoodKernelEvaluation B U hK x k : V) =
      (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val
        (U.orthogonalProjectionOnto x) := by
  have hr := (symmetricSquare_mem_range_iff_operator_range U k).mp (hK k.property)
  have hz := quadraticSpace_kills_orthogonal
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).property.isSymmetric U hr
    (U.sub_starProjection_mem_orthogonal x)
  change (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val x =
    (symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val (U.starProjection x)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

/-- The SAME bilinear quadratic family at z0=projection_U x is the genuine evaluation pairing.
Source: `prop:supported-rank`, the actual Jacobian/evaluation bridge. -/
theorem supportedRankKernelQuadratic_projection (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (k : B.ker) (v : U) :
    supportedRankKernelQuadratic B U k (U.orthogonalProjectionOnto x) v =
      inner ℝ (supportedRankGoodKernelEvaluation B U hK x k) v := by
  change inner ℝ ((symmetricSquareToSelfAdjoint (k : SymmetricSquare V)).val
    (U.orthogonalProjectionOnto x)) (v : V) = _
  rw [← supportedRankGoodKernelEvaluation_projection B U hK x k]
  rfl

/-- The actual doubled-dual good evaluation, built by native real Riesz and actual dual maps.
Source: `prop:supported-rank`, the good quadratic Jacobian used in the strong-rank argument. -/
def supportedRankGoodKernelDualEquiv (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) :
    U ≃ₗ[ℝ] Module.Dual ℝ B.ker :=
  let E := supportedRankGoodKernelEvaluationEquiv B U hK x hg hdim
  let R : U ≃ₗ[ℝ] Module.Dual ℝ U :=
    (InnerProductSpace.toDual ℝ U).toLinearEquiv.trans
      (LinearMap.toContinuousLinearMap : (U →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (U →L[ℝ] ℝ)).symm
  (R.trans E.dualMap).trans (LinearEquiv.smulOfNeZero ℝ (Module.Dual ℝ B.ker) 2 (by norm_num))

/-- The constructed J has EXACTLY `J(v)(k)=2Q(k,z0,v)` for the same original family.
Proof: native Riesz/dual evaluation and the already proved projection identity; real
inner symmetry fixes the order of the two arguments. No Jacobian identity is assumed.
Source: `prop:supported-rank`, the good evaluation derivative used by the syzygy argument. -/
theorem supportedRankGoodKernelDualEquiv_apply (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) (v : U) (k : B.ker) :
    supportedRankGoodKernelDualEquiv B U hK x hg hdim v k =
      2 * supportedRankKernelQuadratic B U k (U.orthogonalProjectionOnto x) v := by
  rw [supportedRankKernelQuadratic_projection B U hK x k v]
  change 2 * inner ℝ v (supportedRankGoodKernelEvaluation B U hK x k) =
    2 * inner ℝ (supportedRankGoodKernelEvaluation B U hK x k) v
  exact congrArg (fun r : ℝ ↦ 2 * r) (real_inner_comm _ _)

#print axioms supportedRank_good_covector_riesz
#print axioms supportedRankGoodKernelEvaluation
#print axioms supportedRankGoodKernelEvaluation_injective
#print axioms supportedRankGoodKernelEvaluationEquiv
#print axioms supportedRankKernelQuadratic
#print axioms supportedRankKernelQuadratic_symm
#print axioms supportedRankGoodKernelEvaluation_projection
#print axioms supportedRankKernelQuadratic_projection
#print axioms supportedRankGoodKernelDualEquiv
#print axioms supportedRankGoodKernelDualEquiv_apply

end GlobalEmbedding.Paper
