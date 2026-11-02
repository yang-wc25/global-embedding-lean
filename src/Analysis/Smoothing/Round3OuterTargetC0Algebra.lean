import Smoothing.ParameterRound2TensorGermSpace

/-! Exact original C0 control of SH-a H0-H0. The three terms are the actual
smoothing defect, the old normalized defect relative to H0, and the reserve.
All norm finite guards are produced from compact original evaluation pieces.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

private theorem target_seminorm_bound {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (H SH H0 : X) (a error inherited reference : ℝ)
    (ha : 0 ≤ a) (herror : p (H-SH) ≤ error)
    (hinherited : p (H-H0) ≤ inherited) (hreference : p H0 ≤ reference) :
    p (SH-a • H0-H0) ≤ error+inherited+a*reference := by
  have heq : SH-a • H0-H0 = -(H-SH)+(H-H0)-a • H0 := by abel
  rw [heq]
  calc
    _ ≤ p (-(H-SH)+(H-H0))+p (a • H0) := map_sub_le_add p _ _
    _ ≤ p (-(H-SH))+p (H-H0)+p (a • H0) :=
      add_le_add (map_add_le_add p _ _) le_rfl
    _ = p (H-SH)+p (H-H0)+a*p H0 := by
      rw [map_neg_eq_map,map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ _ := add_le_add (add_le_add herror hinherited)
      (mul_le_mul_of_nonneg_left hreference ha)

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

theorem round3_original_target_C0_from_smoothing_error
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (H SH H0 : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B H i)
      (incrementsOriginalDifferentiation A B i))
    (hSH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B SH i)
      (incrementsOriginalDifferentiation A B i))
    (hH0 : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B H0 i)
      (incrementsOriginalDifferentiation A B i))
    (hHs : ∀ p x, (H p x).IsSymm) (hSHs : ∀ p x, (SH p x).IsSymm)
    (hH0s : ∀ p x, (H0 p x).IsSymm)
    (ell a error inherited reference : ℝ) (ha : 0 ≤ a)
    (herror : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates A B (fun p x => H p x-SH p x))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ error)
    (hinherited : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates A B (fun p x => H p x-H0 p x))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ inherited)
    (hreference : (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B H0)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ reference) :
    paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B
      (fun p x => SH p x-a • H0 p x-H0 p x))
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B
      (fun p x => SH p x-a • H0 p x-H0 p x))
      (incrementsOriginalDifferentiation A B) S).toReal ≤ error+inherited+a*reference := by
  let O := incrementsOriginalDifferentiation A B
  have hO := parameterRound2_originalDifferentiation_open A B
  let gH : parameterRound2_originalTensorGermSpace A B S univ :=
    ⟨H,⟨fun i => ⟨O i,hO i,hSO i,hH i⟩,fun z _ => hHs z.1 z.2⟩⟩
  let gSH : parameterRound2_originalTensorGermSpace A B S univ :=
    ⟨SH,⟨fun i => ⟨O i,hO i,hSO i,hSH i⟩,fun z _ => hSHs z.1 z.2⟩⟩
  let gH0 : parameterRound2_originalTensorGermSpace A B S univ :=
    ⟨H0,⟨fun i => ⟨O i,hO i,hSO i,hH0 i⟩,fun z _ => hH0s z.1 z.2⟩⟩
  let p := parameterRound2_originalTensorGermSeminorm A B S univ hS hSO ell 0
  have hpeq (T : parameterRound2_originalTensorGermSpace A B S univ) :
      p T = (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B T.val) O S).toReal := by
    change (paperAtlasWeighted 0 0 ell _ _ _).toReal = _
    simp only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul]
    rfl
  have hbH : p (gH-gSH) ≤ error := by
    rw [hpeq]
    exact herror
  have hbOld : p (gH-gH0) ≤ inherited := by
    rw [hpeq]
    exact hinherited
  have hbRef : p gH0 ≤ reference := by
    rw [hpeq]
    exact hreference
  have hfinite := parameterRound2_tensorGerm_weighted_finite A B S univ hS hSO
    (gSH-a • gH0-gH0) 0 0 ell
  have hbound := target_seminorm_bound p gH gSH gH0 a error inherited reference
    ha hbH hbOld hbRef
  constructor
  · simp only [paperAtlasWeighted,Finset.sum_range_one,pow_zero,zero_add,one_mul] at hfinite
    exact hfinite
  · rw [hpeq] at hbound
    exact hbound

#print axioms round3_original_target_C0_from_smoothing_error
end GlobalEmbedding.Continuation
