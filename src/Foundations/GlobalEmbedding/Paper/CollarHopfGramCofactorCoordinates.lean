import GlobalEmbedding.Paper.CollarAmbientHopfSourceCoefficients
import GlobalEmbedding.Paper.FreeGramRightInverse
import GlobalEmbedding.Paper.FreeCorrectionStability
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Exact cofactor coordinates for the same actual Hopf Gram right inverse

Source: `main.tex`, prop:collar, lines522–534.
DAG: `collar-hopf-gram-cofactor-coordinates`; sole AS2b owner W2.
The original cofactor order induces a true Euclidean index isometry. The
native and matrix inverses agree by EXISTING algebra equivalences of inverses.
-/

noncomputable section
open Matrix
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual ordinary transpose matrix is the SAME original column operator,
with its full data domain reindexed by the actual cofactor enumeration.
Proof: the actual inclusion column identity and finite reindexing of the exact
synthesis sum. No smoothness or rank is needed. Source: prop:collar522–534. -/
theorem collarHopf_column_operator_cofactor_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C) :
    let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a)
    let A := freeColumnOperator
      (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x)
    A.comp e.symm.toContinuousLinearMap =
      (Matrix.toEuclideanLin
        (collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)).transpose).toContinuousLinearMap := by
  dsimp only
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro j
  simp only [ContinuousLinearMap.comp_apply, freeColumnOperator_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  change (∑ k : BalancedPairingIndex a,
      u (freeCofactorColumnOrder a k) *
        freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x k j) =
    ∑ r : Fin (freeSymmetricColumnCount a + a),
      collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x) r j * u r
  rw [← (freeCofactorColumnOrder a).sum_comp
    (fun r ↦ collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x) r j * u r)]
  apply Finset.sum_congr rfl
  intro k _
  rw [collarAmbientHopfPairingMatrix_inclusion, Equiv.symm_apply_apply]
  exact mul_comm _ _

/-- The SAME actual ordinary-transpose matrix Gram right inverse is exactly
the original native Gram right inverse in the actual cofactor coordinates.

Proof: transpose corresponds to the real adjoint by Mathlib. Matrix product
corresponds to composition, and both matrix and native total inverse are
Ring.inverse transported along existing algebra equivalences. The actual
Euclidean permutation conjugates the native Gram by its existing star algebra
equivalence, which already preserves Ring.inverse. No new inverse conjugation
calculus, determinant or norm assumption is used; singular/empty cases included.
Source: the precise coefficient Tᵀ(TTᵀ)⁻¹ in prop:collar, lines522–534. -/
theorem collarHopf_gram_cofactor_coordinates {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C) :
    let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a)
    let A := freeColumnOperator
      (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x)
    let T := collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)
    (Matrix.toEuclideanLin (T.transpose * (T * T.transpose)⁻¹)).toContinuousLinearMap =
      (freeGramRightInverse A).comp e.symm.toContinuousLinearMap := by
  let E := EuclideanSpace ℝ (BalancedPairingIndex a)
  let V := EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a))
  let W := EuclideanSpace ℝ (Fin N)
  let e : E ≃ₗᵢ[ℝ] V :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (freeCofactorColumnOrder a)
  let A : E →L[ℝ] W := freeColumnOperator
    (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x)
  let T := collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)
  let B : V →L[ℝ] W := (Matrix.toEuclideanLin T.transpose).toContinuousLinearMap
  let Q : W →L[ℝ] V := (Matrix.toEuclideanLin T).toContinuousLinearMap
  have hB : B = A.comp e.symm.toContinuousLinearMap :=
    (collarHopf_column_operator_cofactor_coordinates C F x).symm
  have hQ : Q = B.adjoint := by
    have he := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (T.transpose)
    have hh := congrArg (fun L ↦ LinearMap.toContinuousLinearMap L) he
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      LinearMap.adjoint_toContinuousLinearMap] using hh
  have hG : Matrix.toEuclideanCLM (𝕜 := ℝ) (T * T.transpose) = B.adjoint.comp B := by
    rw [← hQ]
    exact congrArg (fun L ↦ LinearMap.toContinuousLinearMap L)
      (Matrix.toLpLin_mul 2 2 2 T T.transpose)
  have hGI : Matrix.toEuclideanCLM (𝕜 := ℝ) ((T * T.transpose)⁻¹) =
      (B.adjoint.comp B).inverse := by
    rw [Matrix.nonsing_inv_eq_ringInverse, map_ringInverse,
      hG, ContinuousLinearMap.ringInverse_eq_inverse]
  have hM : (Matrix.toEuclideanLin (T.transpose * (T * T.transpose)⁻¹)).toContinuousLinearMap =
      B.comp (B.adjoint.comp B).inverse := by
    rw [← hGI]
    exact congrArg (fun L ↦ LinearMap.toContinuousLinearMap L)
      (Matrix.toLpLin_mul 2 2 2 T.transpose ((T * T.transpose)⁻¹))
  have heAdj : e.symm.toContinuousLinearMap.adjoint = e.toContinuousLinearMap := by
    convert e.symm.adjoint_eq_symm using 1 <;> ext u <;> rfl
  have hconj : B.adjoint.comp B = e.conjStarAlgEquiv (A.adjoint.comp A) := by
    rw [hB, ContinuousLinearMap.adjoint_comp, heAdj]
    ext u
    rfl
  have hconjInv : (B.adjoint.comp B).inverse =
      e.conjStarAlgEquiv (A.adjoint.comp A).inverse := by
    rw [hconj, ← ContinuousLinearMap.ringInverse_eq_inverse,
      ← map_ringInverse, ContinuousLinearMap.ringInverse_eq_inverse]
  change (Matrix.toEuclideanLin (T.transpose * (T * T.transpose)⁻¹)).toContinuousLinearMap = _
  rw [hM, hconjInv, hB]
  apply ContinuousLinearMap.ext
  intro u
  change A (e.symm (e ((A.adjoint.comp A).inverse (e.symm u)))) =
    A ((A.adjoint.comp A).inverse (e.symm u))
  rw [e.symm_apply_apply]

end GlobalEmbedding.Paper
