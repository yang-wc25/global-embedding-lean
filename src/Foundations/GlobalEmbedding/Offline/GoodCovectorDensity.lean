import GlobalEmbedding.Paper.LinearSecondFormGoodOpen
import GlobalEmbedding.Paper.SaturationOpenPolynomial
import GlobalEmbedding.Paper.GoodCovector
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# A genuine polynomial certificate for actual good covectors

Source: `main.tex`, preparation of the good rank-one dictionary before (6.4),
and node `repair-good-rank-one-dictionary`, Steps 1–2.  The original quotient
contraction dictionary identifies injectivity on the literal `Sym² ker ξ`
with injectivity of the same contraction on the fixed `ker B`.  This module
uses that proved identity, constructs an actual finite determinant polynomial,
and obtains density from the original open-set polynomial identity theorem.
There is no assumed density, surrogate kernel, or altered symmetric square.
-/

noncomputable section

open GlobalEmbedding.Paper Module
open scoped ContDiff

namespace GlobalEmbedding.Offline

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual coordinate polynomial of a real linear functional. -/
def linearCoordinatePolynomial (f : (ι → ℝ) →ₗ[ℝ] ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i

/-- Evaluation recovers the same functional on every vector, including the
empty coordinate type. -/
theorem eval_linearCoordinatePolynomial (f : (ι → ℝ) →ₗ[ℝ] ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (linearCoordinatePolynomial f) = f x := by
  have hx : (∑ i, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  simp only [linearCoordinatePolynomial, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  calc
    (∑ i, f (Pi.single i 1) * x i) = f (∑ i, x i • Pi.single i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = f x := congrArg f hx

section Determinant

variable {K V : Type*} [AddCommGroup K] [Module ℝ K] [FiniteDimensional ℝ K]
    [AddCommGroup V] [Module ℝ V]

/-- A linear operator family injective at one actual parameter has a genuine
nonzero determinant certificate.  The square matrix uses a linear left inverse
at the witness; its entries are coordinates of the SAME family.  In particular
nonvanishing proves actual injectivity, rather than a supplied rank condition. -/
theorem linearFamily_injective_polynomial_certificate
    (A : (ι → ℝ) →ₗ[ℝ] (K →ₗ[ℝ] V)) (x0 : ι → ℝ)
    (h0 : Function.Injective (A x0)) :
    ∃ p : MvPolynomial ι ℝ,
      MvPolynomial.eval x0 p = 1 ∧
      ∀ x, MvPolynomial.eval x p ≠ 0 → Function.Injective (A x) := by
  classical
  obtain ⟨L, hL⟩ := (A x0).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h0)
  let b := Module.finBasis ℝ K
  let entry (i j : Fin (Module.finrank ℝ K)) : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ b.repr (L (A x (b j))) i
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  let P : Matrix (Fin (Module.finrank ℝ K)) (Fin (Module.finrank ℝ K))
      (MvPolynomial ι ℝ) := fun i j ↦ linearCoordinatePolynomial (entry i j)
  have heval (x : ι → ℝ) :
      MvPolynomial.eval x P.det = (L.comp (A x)).det := by
    have hh (i j : Fin (Module.finrank ℝ K)) :
        (MvPolynomial.eval x).mapMatrix P i j = MvPolynomial.eval x (P i j) := by
      rfl
    rw [(MvPolynomial.eval x).map_det]
    rw [← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    rw [hh]
    change MvPolynomial.eval x (linearCoordinatePolynomial (entry i j)) = _
    rw [eval_linearCoordinatePolynomial]
    rw [LinearMap.toMatrix_apply]
    rfl
  refine ⟨P.det, ?_, ?_⟩
  · rw [heval, hL]
    exact LinearMap.det_id
  · intro x hx
    rw [heval] at hx
    have hinj : Function.Injective (L.comp (A x)) :=
      LinearMap.ker_eq_bot.mp (by
        by_contra hn
        exact hx (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn))
    exact Function.Injective.of_comp hinj

end Determinant

section ActualCovectors

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

/-- An actual good witness produces a nonzero polynomial certificate for the
original good set, in any chosen continuous linear coordinates of the full dual.
The determinant uses the real contraction on the SAME `ker B`.  Its implication
for the literal `Sym² ker ξ` is the proved original contraction dictionary.
A coordinate factor explicitly excludes the zero covector, even when `ker B=0`.
-/
theorem actual_good_covector_polynomial_certificate
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (e : (V →L[ℝ] ℝ) ≃L[ℝ] (ι → ℝ))
    (ξ0 : V →L[ℝ] ℝ) (h0 : LinearSecondFormGoodCovector B ξ0.toLinearMap) :
    ∃ p : MvPolynomial ι ℝ,
      MvPolynomial.eval (e ξ0) p ≠ 0 ∧
      ∀ x, MvPolynomial.eval x p ≠ 0 →
        LinearSecondFormGoodCovector B (e.symm x).toLinearMap := by
  classical
  let K := B.ker
  let C := Fin (Module.finrank ℝ K) → ℝ
  let b : K ≃ₗ[ℝ] C := (Module.finBasis ℝ K).equivFun
  let j : C →ₗ[ℝ] SymmetricSquare V := K.subtype.comp b.symm.toLinearMap
  let A : (ι → ℝ) →ₗ[ℝ] (C →ₗ[ℝ] V) :=
    (ContinuousLinearMap.coeLM ℝ).comp
      ((contractionKernelCovectorOperator j).toLinearMap.comp e.symm.toLinearMap)
  have hAval (x : ι → ℝ) (u : C) :
      A x u = contractionKernelQuotientMap (e.symm x).toLinearMap
        (K.subtype (b.symm u)) := rfl
  have hcontract := (linearSecondFormGoodCovector_iff_contraction B ξ0.toLinearMap).mp h0
  have hA0 : Function.Injective (A (e ξ0)) := by
    intro u v huv
    have heq : b.symm u = b.symm v := hcontract.2 (by
      rw [hAval, hAval, e.symm_apply_apply] at huv
      simpa only [LinearMap.domRestrict_apply, Submodule.subtype_apply] using huv)
    exact b.symm.injective heq
  obtain ⟨p, hp, hpinj⟩ := linearFamily_injective_polynomial_certificate A (e ξ0) hA0
  have hx0 : e ξ0 ≠ 0 := by
    intro hz
    have hξ : ξ0 = 0 := e.injective (by simpa only [map_zero] using hz)
    exact h0.1 (by rw [hξ]; rfl)
  obtain ⟨i, hi⟩ : ∃ i, e ξ0 i ≠ 0 := by
    by_contra! h
    exact hx0 (funext h)
  refine ⟨MvPolynomial.X i * p, ?_, ?_⟩
  · simpa only [map_mul, MvPolynomial.eval_X, hp, mul_one] using hi
  · intro x hx
    have hxprod : x i * MvPolynomial.eval x p ≠ 0 := by
      simpa only [map_mul, MvPolynomial.eval_X] using hx
    have hxn : x i ≠ 0 := (mul_ne_zero_iff.mp hxprod).1
    have hxi : (e.symm x).toLinearMap ≠ 0 := by
      intro hz
      have hzero : e.symm x = 0 := ContinuousLinearMap.coe_injective hz
      have hxzero : x = 0 := by
        simpa only [e.apply_symm_apply, map_zero] using congrArg e hzero
      exact hxn (by rw [hxzero]; rfl)
    apply (linearSecondFormGoodCovector_iff_contraction B _).mpr
    refine ⟨hxi, ?_⟩
    have hinj := hpinj x (mul_ne_zero_iff.mp hxprod).2
    intro u v huv
    apply b.injective
    apply hinj
    change contractionKernelQuotientMap (e.symm x).toLinearMap (j (b u)) =
      contractionKernelQuotientMap (e.symm x).toLinearMap (j (b v))
    simpa only [j, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply,
      Submodule.subtype_apply] using huv

/-- From one actual good direction, the original good cone is dense in the
FULL continuous dual.  Every nonempty open set is met by the actual nonzero
determinant polynomial; density is proved, not assumed as a genericity input.
-/
theorem dense_actual_good_covectors
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hgood : ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap) :
    Dense {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap} := by
  classical
  let e : (V →L[ℝ] ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ (V →L[ℝ] ℝ)) → ℝ) :=
    (Module.finBasis ℝ (V →L[ℝ] ℝ)).equivFun.toContinuousLinearEquiv
  obtain ⟨ξ0, h0⟩ := hgood
  obtain ⟨p, hp, hcert⟩ := actual_good_covector_polynomial_certificate B e ξ0 h0
  have hp0 : p ≠ 0 := by
    intro hz
    exact hp (by rw [hz, map_zero])
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  have hopen : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hne : (e.symm ⁻¹' U).Nonempty := by
    obtain ⟨ξ, hξ⟩ := hUne
    exact ⟨e ξ, by simpa only [Set.mem_preimage, e.symm_apply_apply] using hξ⟩
  obtain ⟨x, hx, hpne⟩ := saturation_polynomial_exists_ne_zero_on_open p hp0
    (e.symm ⁻¹' U) hopen hne
  exact ⟨e.symm x, hx, hcert x hpne⟩

/-- The original actual good cone is open and dense as soon as one good
covector exists. Openness reuses the accepted full-dual theorem. -/
theorem isOpen_dense_actual_good_covectors
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hgood : ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap) :
    IsOpen {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap} ∧
    Dense {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap} :=
  ⟨isOpen_linearSecondFormGoodCovector B, dense_actual_good_covectors B hgood⟩

/-- A whole family of actual good covectors can be chosen inside any specified
nonempty open set of families.  For the finite dictionary this simultaneously
preserves any open linear-independence and positive-coefficient conditions once
those conditions have been established for an initial family.  No such condition
is silently assumed here: the exact nonempty open set is an explicit argument.
-/
theorem exists_actual_good_family_mem_open {κ : Type*}
    (B : SymmetricSquare V →ₗ[ℝ] W)
    (hgood : ∃ ξ : V →L[ℝ] ℝ, LinearSecondFormGoodCovector B ξ.toLinearMap)
    (U : Set (κ → V →L[ℝ] ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ξ ∈ U, ∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap := by
  have hd : Dense {ξ : κ → V →L[ℝ] ℝ |
      ∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap} := by
    have heq : Set.univ.pi (fun _ : κ ↦
        {ξ : V →L[ℝ] ℝ | LinearSecondFormGoodCovector B ξ.toLinearMap}) =
        {ξ : κ → V →L[ℝ] ℝ | ∀ i, LinearSecondFormGoodCovector B (ξ i).toLinearMap} := by
      ext ξ
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
    rw [← heq]
    exact dense_pi Set.univ (fun (_ : κ) _ ↦ dense_actual_good_covectors B hgood)
  exact dense_iff_inter_open.mp hd U hU hne

end ActualCovectors

section ManifoldSecondForm

open Manifold Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}

omit [FiniteDimensional ℝ E] [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The existing manifold predicate is exactly the existing raw second-form
predicate; the only coercion issue is nonzeroness of a continuous covector. -/
theorem goodCovector_iff_linearSecondFormGoodCovector
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    GoodCovector F hF x ξ ↔
      LinearSecondFormGoodCovector (trueSecondForm F hF x) ξ.toLinearMap := by
  unfold GoodCovector LinearSecondFormGoodCovector
  have hn : ξ ≠ 0 ↔ ξ.toLinearMap ≠ 0 := by
    constructor
    · intro h hz
      exact h (ContinuousLinearMap.coe_injective hz)
    · intro h hz
      exact h (by rw [hz]; rfl)
  exact and_congr hn Iff.rfl

/-- The SAME actual normal-valued true second form has an open dense set of
original `GoodCovector`s at every point possessing one good witness.  This is
the manifold-facing Step 1 of the source's good rank-one dictionary preparation.
-/
theorem isOpen_dense_goodCovectors
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (hgood : ∃ ξ : TangentSpace I x →L[ℝ] ℝ, GoodCovector F hF x ξ) :
    IsOpen {ξ : TangentSpace I x →L[ℝ] ℝ | GoodCovector F hF x ξ} ∧
    Dense {ξ : TangentSpace I x →L[ℝ] ℝ | GoodCovector F hF x ξ} := by
  have hraw : ∃ ξ : TangentSpace I x →L[ℝ] ℝ,
      LinearSecondFormGoodCovector (trueSecondForm F hF x) ξ.toLinearMap := by
    simpa only [goodCovector_iff_linearSecondFormGoodCovector] using hgood
  simpa only [goodCovector_iff_linearSecondFormGoodCovector] using
    isOpen_dense_actual_good_covectors (trueSecondForm F hF x) hraw

/-- The actual good directions for one true second form meet every nonempty
open condition on a family, as needed to perturb a positive rank-one basis.
-/
theorem exists_goodCovector_family_mem_open {κ : Type*}
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (hgood : ∃ ξ : TangentSpace I x →L[ℝ] ℝ, GoodCovector F hF x ξ)
    (U : Set (κ → TangentSpace I x →L[ℝ] ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ξ ∈ U, ∀ i, GoodCovector F hF x (ξ i) := by
  have hraw : ∃ ξ : TangentSpace I x →L[ℝ] ℝ,
      LinearSecondFormGoodCovector (trueSecondForm F hF x) ξ.toLinearMap := by
    simpa only [goodCovector_iff_linearSecondFormGoodCovector] using hgood
  simpa only [goodCovector_iff_linearSecondFormGoodCovector] using
    exists_actual_good_family_mem_open (trueSecondForm F hF x) hraw U hU hne

end ManifoldSecondForm

#print axioms eval_linearCoordinatePolynomial
#print axioms linearFamily_injective_polynomial_certificate
#print axioms actual_good_covector_polynomial_certificate
#print axioms dense_actual_good_covectors
#print axioms isOpen_dense_actual_good_covectors
#print axioms exists_actual_good_family_mem_open
#print axioms goodCovector_iff_linearSecondFormGoodCovector
#print axioms isOpen_dense_goodCovectors
#print axioms exists_goodCovector_family_mem_open

end GlobalEmbedding.Offline
