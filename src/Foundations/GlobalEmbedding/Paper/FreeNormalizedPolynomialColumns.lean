import GlobalEmbedding.Paper.BalancedPairingMap
import GlobalEmbedding.Paper.FreePolynomialResidual
import GlobalEmbedding.Paper.ManifoldFiniteOperatorSmoothness
import GlobalEmbedding.Paper.FreeNormalizedScaleAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual coordinate masks and polynomial column normalization

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–489.
The two masks use the existing sorted symmetric pairing index. Normalization is an explicit
polynomial through zero, rather than a quotient defined by a limiting choice.
-/

noncomputable section
open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The near patch divides mixed and active-active second columns by epsilon. -/
def freeNearColumnMask (m : ℕ) : BalancedPairingIndex (m + 1) → Bool
  | Sum.inl _ => false
  | Sum.inr ij => decide (ij.val.2 = Fin.last m)

/-- The far patch divides mixed second columns only. -/
def freeFarColumnMask (m : ℕ) : BalancedPairingIndex (m + 1) → Bool
  | Sum.inl _ => false
  | Sum.inr ij => decide (ij.val.2 = Fin.last m ∧ ij.val.1 ≠ Fin.last m)

variable {ι : Type*} [Fintype ι]

/-- Literal orthogonal projection onto the selected coordinates of the actual l2 data space. -/
def freeCoordinateMask (p : ι → Bool) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ if p i then EuclideanSpace.proj i else 0)

omit [Fintype ι] in
@[simp]
theorem freeCoordinateMask_apply (p : ι → Bool) (v : EuclideanSpace ℝ ι) (i : ι) :
    freeCoordinateMask p v i = if p i then v i else 0 := by
  change (if p i then EuclideanSpace.proj i else 0) v = _
  split <;> rfl

omit [Fintype ι] in
/-- A mask is an actual idempotent on the entire data space, including zero-dimensional data. -/
theorem freeCoordinateMask_idempotent (p : ι → Bool) :
    (freeCoordinateMask p).comp (freeCoordinateMask p) = freeCoordinateMask p := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply, freeCoordinateMask_apply]
  split <;> simp_all

/-- Coordinate projection is self-adjoint for the actual Euclidean inner product. -/
theorem freeCoordinateMask_adjoint (p : ι → Bool) :
    (freeCoordinateMask p).adjoint = freeCoordinateMask p := by
  apply LinearMap.IsSymmetric.clm_adjoint_eq
  intro x y
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  change y i * star (freeCoordinateMask p x i) = freeCoordinateMask p y i * star (x i)
  by_cases hp : p i = true <;> simp [freeCoordinateMask_apply, hp]

section Polynomial

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual column polynomial of the map F0 + epsilon Z + epsilon squared W. -/
def freeColumnPolynomial (A0 A1 A2 : V →L[ℝ] E) (ε : ℝ) : V →L[ℝ] E :=
  A0 + ε • A1 + ε ^ 2 • A2

/-- Explicit normalized columns. The selected constant columns vanish after projection;
the selected quotient is therefore A1 + epsilon A2, including at epsilon zero. -/
def freeNormalizedColumnPolynomial (prj : E →L[ℝ] E) (J : V →L[ℝ] V)
    (A0 A1 A2 : V →L[ℝ] E) (ε : ℝ) : V →L[ℝ] E :=
  (prj.comp (freeColumnPolynomial A0 A1 A2 ε)).comp (ContinuousLinearMap.id ℝ V - J) +
    (prj.comp (A1 + ε • A2)).comp J

/-- Multiplying the explicit normalized columns by their actual coordinate scale recovers
the projected original polynomial even at zero. Only the masked base columns must vanish. -/
theorem freeNormalizedColumnPolynomial_scale (prj : E →L[ℝ] E) (J : V →L[ℝ] V)
    (hJ : J.comp J = J) (A0 A1 A2 : V →L[ℝ] E)
    (hbase : (prj.comp A0).comp J = 0) (ε : ℝ) :
    (freeNormalizedColumnPolynomial prj J A0 A1 A2 ε).comp (freeColumnScale J ε) =
      prj.comp (freeColumnPolynomial A0 A1 A2 ε) := by
  have hJJ (v : V) : J (J v) = J v := congrArg (fun L : V →L[ℝ] V ↦ L v) hJ
  have hb (v : V) : prj (A0 (J v)) = 0 :=
    congrArg (fun L : V →L[ℝ] E ↦ L v) hbase
  ext v
  simp only [freeNormalizedColumnPolynomial, freeColumnPolynomial, freeColumnScale,
    ContinuousLinearMap.comp_apply, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul, hJJ, hb]
  module

/-- The unscaled and scaled blocks at zero are their actual constant and linear coefficients. -/
theorem freeNormalizedColumnPolynomial_zero (prj : E →L[ℝ] E) (J : V →L[ℝ] V)
    (A0 A1 A2 : V →L[ℝ] E) :
    freeNormalizedColumnPolynomial prj J A0 A1 A2 0 =
      (prj.comp A0).comp (ContinuousLinearMap.id ℝ V - J) + (prj.comp A1).comp J := by
  simp [freeNormalizedColumnPolynomial, freeColumnPolynomial]

/-- Actual native smooth coefficient fields yield the normalized polynomial smoothly through zero.
No regularity of a preselected quotient or inverse is assumed. -/
theorem freeNormalizedColumnPolynomial_contMDiff
    {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
    [TopologicalSpace M] [ChartedSpace H M]
    (J : V →L[ℝ] V) (prj : M → E →L[ℝ] E)
    (A0 A1 A2 : M → V →L[ℝ] E) (ε : M → ℝ)
    (hprj : ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞ prj)
    (hA0 : ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞ A0)
    (hA1 : ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞ A1)
    (hA2 : ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞ A2)
    (hε : ContMDiff I 𝓘(ℝ, ℝ) ∞ ε) :
    ContMDiff I 𝓘(ℝ, V →L[ℝ] E) ∞
      (fun x ↦ freeNormalizedColumnPolynomial (prj x) J (A0 x) (A1 x) (A2 x) (ε x)) := by
  exact ((hprj.clm_comp ((hA0.add (hε.smul hA1)).add
    ((hε.pow 2).smul hA2))).clm_comp contMDiff_const).add
    ((hprj.clm_comp (hA1.add (hε.smul hA2))).clm_comp contMDiff_const)

end Polynomial

section Adjoint

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking the actual adjoint gives precisely the full-data pairing relation used by the
regularized inverse reconstruction; no range projection is imposed on the data. -/
theorem freeNormalizedColumnPolynomial_adjoint (prj : E →L[ℝ] E)
    (hprj : prj.adjoint = prj) (J : V →L[ℝ] V) (hJ : J.comp J = J)
    (hJadj : J.adjoint = J) (A0 A1 A2 : V →L[ℝ] E)
    (hbase : (prj.comp A0).comp J = 0) (ε : ℝ) :
    (freeColumnPolynomial A0 A1 A2 ε).adjoint.comp prj =
      (freeColumnScale J ε).comp
        (freeNormalizedColumnPolynomial prj J A0 A1 A2 ε).adjoint := by
  have hs : (freeColumnScale J ε).adjoint = freeColumnScale J ε := by
    simp [freeColumnScale, hJadj, ContinuousLinearMap.adjoint_id]
  have h := congrArg ContinuousLinearMap.adjoint
    (freeNormalizedColumnPolynomial_scale prj J hJ A0 A1 A2 hbase ε)
  simpa only [ContinuousLinearMap.adjoint_comp, hprj, hs] using h.symm

end Adjoint

section ActualColumns

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {N a : ℕ}

/-- Every actual first or second column is native smooth along the supplied smooth fields.
This is the accepted native directional smoothness theorem, applied once or twice. -/
theorem freePairingColumn_contMDiff
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (j : BalancedPairingIndex a) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (fun x ↦ balancedPairingColumns F (fun i ↦ D i) x j) := by
  cases j with
  | inl i => exact balanced_directional_contMDiff F hF (D i)
  | inr ij =>
    exact balanced_directional_contMDiff _
      (balanced_directional_contMDiff F hF (D ij.val.2)) (D ij.val.1)

/-- The original full pairing operator is native smooth, by the accepted finite-domain
operator criterion and the actual first and second columns, with no supplied smooth operator. -/
theorem freePairingMap_contMDiff
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (BalancedPairingIndex a)) ∞
      (fun x ↦ balancedPairingMap F (fun i ↦ D i) x) := by
  intro x
  apply (manifold_finite_operator_smooth_iff _ x).mpr
  intro u
  have hrow (j : BalancedPairingIndex a) : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y ↦ inner ℝ (balancedPairingColumns F (fun i ↦ D i) y j) u) := by
    have h := (innerSL ℝ u).contDiff.contMDiff.comp (freePairingColumn_contMDiff F hF D j)
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using h
  let e := (EuclideanSpace.equiv (BalancedPairingIndex a) ℝ).symm
  exact (e.contDiff.contMDiff.comp (contMDiff_pi_module_iff.mpr hrow)).contMDiffAt

/-- All actual first and once-indexed second columns of the same polynomial map are quadratic
in epsilon. The second-column proof applies the accepted first-derivative formula twice,
using the accepted native smoothness of directional derivatives. -/
theorem freePolynomialFamily_columns
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (ε : ℝ) (x : M) (j : BalancedPairingIndex a) :
    balancedPairingColumns (freePolynomialFamily F Z W ε) (fun i ↦ D i) x j =
      balancedPairingColumns F (fun i ↦ D i) x j + ε • balancedPairingColumns Z (fun i ↦ D i) x j +
        ε ^ 2 • balancedPairingColumns W (fun i ↦ D i) x j := by
  cases j with
  | inl i => exact freePolynomialFamily_directional F Z W hF hZ hW (D i) ε x
  | inr ij =>
    have hcol : balancedDirectionalDerivative (freePolynomialFamily F Z W ε) (D ij.val.2) =
        freePolynomialFamily (balancedDirectionalDerivative F (D ij.val.2))
          (balancedDirectionalDerivative Z (D ij.val.2))
          (balancedDirectionalDerivative W (D ij.val.2)) ε := by
      funext y
      exact freePolynomialFamily_directional F Z W hF hZ hW (D ij.val.2) ε y
    change balancedDirectionalDerivative
      (balancedDirectionalDerivative (freePolynomialFamily F Z W ε) (D ij.val.2))
      (D ij.val.1) x = _
    rw [hcol]
    exact freePolynomialFamily_directional _ _ _
      (balanced_directional_contMDiff F hF (D ij.val.2))
      (balanced_directional_contMDiff Z hZ (D ij.val.2))
      (balanced_directional_contMDiff W hW (D ij.val.2)) (D ij.val.1) ε x

/-- The original full balanced pairing operator of the same actual polynomial, with precisely
its original first and sorted symmetric second rows, is the corresponding operator polynomial. -/
theorem freePolynomialFamily_pairingMap
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (ε : ℝ) (x : M) :
    balancedPairingMap (freePolynomialFamily F Z W ε) (fun i ↦ D i) x =
      balancedPairingMap F (fun i ↦ D i) x + ε • balancedPairingMap Z (fun i ↦ D i) x +
        ε ^ 2 • balancedPairingMap W (fun i ↦ D i) x := by
  ext u j
  change inner ℝ (balancedPairingColumns (freePolynomialFamily F Z W ε) (fun i ↦ D i) x j) u =
    inner ℝ (balancedPairingColumns F (fun i ↦ D i) x j) u +
      ε * inner ℝ (balancedPairingColumns Z (fun i ↦ D i) x j) u +
      ε ^ 2 * inner ℝ (balancedPairingColumns W (fun i ↦ D i) x j) u
  rw [freePolynomialFamily_columns F Z W hF hZ hW D ε x j]
  simp only [inner_add_left, real_inner_smul_left]

/-- The actual column operator, namely the adjoint of the original full pairing map,
is the literal column polynomial with its actual constant, displacement and correction columns. -/
theorem freePolynomialFamily_columnOperator
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (ε : ℝ) (x : M) :
    (balancedPairingMap (freePolynomialFamily F Z W ε) (fun i ↦ D i) x).adjoint =
      freeColumnPolynomial (balancedPairingMap F (fun i ↦ D i) x).adjoint
        (balancedPairingMap Z (fun i ↦ D i) x).adjoint
        (balancedPairingMap W (fun i ↦ D i) x).adjoint ε := by
  rw [freePolynomialFamily_pairingMap F Z W hF hZ hW D ε x]
  simp [freeColumnPolynomial]

end ActualColumns

#print axioms freeCoordinateMask_adjoint
#print axioms freeNormalizedColumnPolynomial_scale
#print axioms freeNormalizedColumnPolynomial_contMDiff
#print axioms freeNormalizedColumnPolynomial_adjoint
#print axioms freePairingMap_contMDiff
#print axioms freePolynomialFamily_columnOperator
#print axioms freePolynomialFamily_columns
#print axioms freePolynomialFamily_pairingMap

end GlobalEmbedding.Paper
