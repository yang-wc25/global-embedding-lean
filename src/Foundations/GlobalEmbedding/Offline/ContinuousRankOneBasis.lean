import GlobalEmbedding.Offline.PositiveRankOneBasis
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The positive basis on the actual continuous bilinear form space

Finite dimensionality only upgrades the already constructed linear maps to continuous
linear maps.  Evaluation, reconstruction, coefficient functionals and the positive tensor
are unchanged.  In particular the topology used to perturb the covectors is the original
continuous-dual topology, and no substitute norm is introduced.
-/

open LinearMap
open scoped BigOperators

namespace GlobalEmbedding.Offline

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def continuousBilinearForget :
    (V →L[ℝ] V →L[ℝ] ℝ) →ₗ[ℝ] LinearMap.BilinForm ℝ V where
  toFun B := (ContinuousLinearMap.coeLM ℝ).comp B.toLinearMap
  map_add' B C := by ext x y; rfl
  map_smul' c B := by ext x y; rfl

@[simp] theorem continuousBilinearForget_apply
    (B : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) :
    continuousBilinearForget B x y = B x y := rfl

theorem continuousBilinearForget_injective :
    Function.Injective (continuousBilinearForget (V := V)) := by
  intro B C h
  ext x y
  exact congrArg (fun A : LinearMap.BilinForm ℝ V ↦ A x y) h

@[simp] theorem continuousBilinearForget_square (ξ : V →L[ℝ] ℝ) :
    continuousBilinearForget (ξ.smulRight ξ) =
      LinearMap.BilinForm.linMulLin ξ.toLinearMap ξ.toLinearMap := by
  ext x y
  rfl

noncomputable def continuousRankOneReconstruct
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ) :
    (ι → ℝ) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) := by
  let R : (ι → ℝ) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
    { toFun := fun a ↦ ∑ i, a i • (ξ i).smulRight (ξ i)
      map_add' := by
        intro a b
        ext x y
        simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, add_mul,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext x y
        simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc, Finset.mul_sum] }
  exact LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ℝ)
    (F' := V →L[ℝ] V →L[ℝ] ℝ) R

theorem continuousRankOneReconstruct_eq_sum
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) :
    continuousRankOneReconstruct ξ a = ∑ i, a i • (ξ i).smulRight (ξ i) := rfl

@[simp] theorem continuousRankOneReconstruct_apply
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) (x y : V) :
    continuousRankOneReconstruct ξ a x y = ∑ i, a i * ξ i x * ξ i y := by
  simp [continuousRankOneReconstruct_eq_sum, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_assoc]

theorem continuousRankOneReconstruct_isSymm
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) (x y : V) :
    continuousRankOneReconstruct ξ a x y = continuousRankOneReconstruct ξ a y x := by
  simp only [continuousRankOneReconstruct_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem continuousBilinearForget_reconstruct
    {ι : Type*} [Fintype ι] (ξ : ι → V →L[ℝ] ℝ) (a : ι → ℝ) :
    continuousBilinearForget (continuousRankOneReconstruct ξ a) =
      rankOneReconstruct (fun i ↦ (ξ i).toLinearMap) a := by
  ext x y
  simp

theorem positive_continuous_rank_one_basis [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (hBpos : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ ξ : EdgePair (Module.finrank ℝ V + 1) → V →L[ℝ] ℝ,
      ∃ C : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (EdgePair (Module.finrank ℝ V + 1) → ℝ),
        (∀ i, ξ i ≠ 0) ∧
        LinearIndependent ℝ (fun i ↦ (ξ i).smulRight (ξ i)) ∧
        (∀ a, C (continuousRankOneReconstruct ξ a) = a) ∧
        (∀ A, (∀ x y, A x y = A y x) → continuousRankOneReconstruct ξ (C A) = A) ∧
        C B = fun _ ↦ 1 := by
  classical
  obtain ⟨ξ, C, hξ, hLI, hleft, hright, hCB⟩ :=
    positive_rank_one_basis (continuousBilinearForget B) ⟨hB⟩ hBpos
  let ξ' : EdgePair (Module.finrank ℝ V + 1) → V →L[ℝ] ℝ :=
    fun i ↦ LinearMap.toContinuousLinearMap (ξ i)
  let C' : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (EdgePair (Module.finrank ℝ V + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V →L[ℝ] V →L[ℝ] ℝ)
      (F' := EdgePair (Module.finrank ℝ V + 1) → ℝ)
      (C.comp (continuousBilinearForget (V := V)))
  have hξcoe : (fun i ↦ (ξ' i).toLinearMap) = ξ := rfl
  have hleft' (a : EdgePair (Module.finrank ℝ V + 1) → ℝ) :
      C' (continuousRankOneReconstruct ξ' a) = a := by
    change C (continuousBilinearForget (continuousRankOneReconstruct ξ' a)) = a
    rw [continuousBilinearForget_reconstruct, hξcoe, hleft]
  refine ⟨ξ', C', ?_, ?_, hleft', ?_, hCB⟩
  · intro i hi
    exact hξ i (congrArg ContinuousLinearMap.toLinearMap hi)
  · apply (Fintype.linearIndependent_iff (R := ℝ)
      (v := fun i ↦ (ξ' i).smulRight (ξ' i))).mpr
    intro a ha i
    change continuousRankOneReconstruct ξ' a = 0 at ha
    have h := congrArg C' ha
    rw [hleft', map_zero] at h
    exact congrFun h i
  · intro A hA
    apply continuousBilinearForget_injective
    rw [continuousBilinearForget_reconstruct, hξcoe]
    exact hright (continuousBilinearForget A) ⟨hA⟩

#print axioms continuousBilinearForget_injective
#print axioms positive_continuous_rank_one_basis

end GlobalEmbedding.Offline
