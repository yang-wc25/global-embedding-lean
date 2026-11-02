import GlobalEmbedding.Offline.EdgeRootBasis
import GlobalEmbedding.Offline.PositiveFormTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Positive rank-one bases for every positive definite symmetric form

The normalized edge-root construction is transported by an actual positive-form isometry.
The resulting covectors, their squared bilinear forms, and all coefficient functionals
are native linear maps.  Both inverse identities are proved, so spanning and positivity
are conclusions of the construction rather than hypotheses.
-/

open LinearMap
open scoped BigOperators

namespace GlobalEmbedding.Offline

noncomputable def bilinearPullbackLinear
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) : LinearMap.BilinForm ℝ W →ₗ[ℝ] LinearMap.BilinForm ℝ V where
  toFun B := B.comp f f
  map_add' B C := by ext x y; rfl
  map_smul' c B := by ext x y; rfl

@[simp] theorem bilinearPullbackLinear_apply
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (B : LinearMap.BilinForm ℝ W) (x y : V) :
    bilinearPullbackLinear f B x y = B (f x) (f y) := rfl

theorem bilinearPullbackLinear_isSymm
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (B : LinearMap.BilinForm ℝ W) (hB : B.IsSymm) :
    (bilinearPullbackLinear f B).IsSymm := ⟨fun _ _ ↦ hB.eq _ _⟩

theorem bilinearPullbackLinear_equiv_inverse
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (B : LinearMap.BilinForm ℝ V) :
    bilinearPullbackLinear e.toLinearMap
      (bilinearPullbackLinear e.symm.toLinearMap B) = B := by
  ext x y
  simp

noncomputable def rankOneReconstruct
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (ξ : ι → V →ₗ[ℝ] ℝ) : (ι → ℝ) →ₗ[ℝ] LinearMap.BilinForm ℝ V where
  toFun a := ∑ i, a i • LinearMap.BilinForm.linMulLin (ξ i) (ξ i)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem rankOneReconstruct_apply
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (ξ : ι → V →ₗ[ℝ] ℝ) (a : ι → ℝ) (x y : V) :
    rankOneReconstruct ξ a x y = ∑ i, a i * ξ i x * ξ i y := by
  simp [rankOneReconstruct, smul_eq_mul, mul_assoc]

theorem rankOneReconstruct_isSymm
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (ξ : ι → V →ₗ[ℝ] ℝ) (a : ι → ℝ) : (rankOneReconstruct ξ a).IsSymm := by
  constructor
  intro x y
  simp only [rankOneReconstruct_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rankOneReconstruct_comp
    {ι V W : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (ξ : ι → W →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] W) (a : ι → ℝ) :
    rankOneReconstruct (fun i ↦ (ξ i).comp f) a =
      bilinearPullbackLinear f (rankOneReconstruct ξ a) := by
  ext x y
  simp

theorem rankOneReconstruct_normalizedEdge (m : ℕ) (a : EdgePair m → ℝ) :
    rankOneReconstruct (normalizedEdgeCovector m) a = normalizedEdgeReconstruct m a := by
  rw [normalizedEdgeReconstruct_eq_sum]
  rfl

theorem positive_rank_one_basis
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hBpos : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ ξ : EdgePair (Module.finrank ℝ V + 1) → V →ₗ[ℝ] ℝ,
      ∃ C : LinearMap.BilinForm ℝ V →ₗ[ℝ] (EdgePair (Module.finrank ℝ V + 1) → ℝ),
        (∀ i, ξ i ≠ 0) ∧
        LinearIndependent ℝ (fun i ↦ LinearMap.BilinForm.linMulLin (ξ i) (ξ i)) ∧
        (∀ a, C (rankOneReconstruct ξ a) = a) ∧
        (∀ A, A.IsSymm → rankOneReconstruct ξ (C A) = A) ∧
        C B = fun _ ↦ 1 := by
  classical
  let m := Module.finrank ℝ V + 1
  have hm : m ≠ 0 := Nat.succ_ne_zero _
  have hdim : Module.finrank ℝ V = Module.finrank ℝ (zeroSumSpace m) := by
    rw [finrank_zeroSumSpace m hm]
    simp [m]
  obtain ⟨e, he⟩ := positive_bilinear_isometry_of_finrank_eq B (zeroSumDotForm m)
    hB (zeroSumDotForm_isSymm m) hBpos (zeroSumDotForm_posDef m) hdim
  let ξ : EdgePair m → V →ₗ[ℝ] ℝ := fun i ↦
    (normalizedEdgeCovector m i).comp e.toLinearMap
  let C : LinearMap.BilinForm ℝ V →ₗ[ℝ] (EdgePair m → ℝ) :=
    (normalizedEdgeCoefficientLinear m hm).comp (bilinearPullbackLinear e.symm.toLinearMap)
  have hR (a : EdgePair m → ℝ) : rankOneReconstruct ξ a =
      bilinearPullbackLinear e.toLinearMap (normalizedEdgeReconstruct m a) := by
    rw [show ξ = (fun i ↦ (normalizedEdgeCovector m i).comp e.toLinearMap) from rfl,
      rankOneReconstruct_comp, rankOneReconstruct_normalizedEdge]
  have hleft (a : EdgePair m → ℝ) : C (rankOneReconstruct ξ a) = a := by
    change normalizedEdgeCoefficientLinear m hm
      (bilinearPullbackLinear e.symm.toLinearMap (rankOneReconstruct ξ a)) = a
    rw [hR]
    have hinv (A : LinearMap.BilinForm ℝ (zeroSumSpace m)) :
        bilinearPullbackLinear e.symm.toLinearMap
          (bilinearPullbackLinear e.toLinearMap A) = A := by
      ext x y
      simp
    rw [hinv, normalizedEdgeCoefficient_reconstruct]
  have hright (A : LinearMap.BilinForm ℝ V) (hA : A.IsSymm) :
      rankOneReconstruct ξ (C A) = A := by
    rw [hR]
    change bilinearPullbackLinear e.toLinearMap
      (normalizedEdgeReconstruct m
        (normalizedEdgeCoefficientLinear m hm (bilinearPullbackLinear e.symm.toLinearMap A))) = A
    rw [normalizedEdgeReconstruct_coefficients m hm _
      (bilinearPullbackLinear_isSymm _ _ hA), bilinearPullbackLinear_equiv_inverse]
  have hLI : LinearIndependent ℝ (fun i ↦ LinearMap.BilinForm.linMulLin (ξ i) (ξ i)) := by
    let : AddCommGroup (LinearMap.BilinForm ℝ V) := inferInstance
    let : Module ℝ (LinearMap.BilinForm ℝ V) := inferInstance
    apply (Fintype.linearIndependent_iff (R := ℝ)
      (v := fun i ↦ LinearMap.BilinForm.linMulLin (ξ i) (ξ i))).mpr
    intro a ha i
    change rankOneReconstruct ξ a = 0 at ha
    have h := congrArg C ha
    rw [hleft, map_zero] at h
    exact congrFun h i
  refine ⟨ξ, C, ?_, hLI, hleft, hright, ?_⟩
  · intro i hi
    apply hLI.ne_zero i
    ext x y
    simp [hi]
  · have hBtransport : bilinearPullbackLinear e.symm.toLinearMap B = zeroSumDotForm m := by
      ext x y
      simpa using (he (e.symm x) (e.symm y)).symm
    change normalizedEdgeCoefficientLinear m hm (bilinearPullbackLinear e.symm.toLinearMap B) = _
    rw [hBtransport, normalizedEdgeCoefficient_dot]

#print axioms positive_rank_one_basis

end GlobalEmbedding.Offline
