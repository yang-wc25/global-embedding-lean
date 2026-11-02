import Smoothing.ParameterOriginalPairSmoothing

/-!
# Exact finite geometric prefixes used by the original pair constants

For output order m the map uses normalized cutoff and joint transition
profiles only through m+2. The native tensor uses the cutoff profile through
m and the transition profile through m+1. The moment order r changes the
fixed kernel and input derivatives, but does not raise these geometric orders.
The statements are equalities of the actual constants, not asymptotic claims.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper MeasureTheory
open scoped BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

theorem parameterTransitionPrefix_congr {T₁ T₂ : ℕ → ℝ} (j : ℕ)
    (hT : ∀ a ≤ j, T₁ a = T₂ a) :
    bufferedTransitionPrefix T₁ j = bufferedTransitionPrefix T₂ j := by
  unfold bufferedTransitionPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact hT a (by simpa using ha)

theorem parameterJetTransferConstant_congr_prefix {C₁ C₂ T₁ T₂ : ℕ → ℝ} (D m : ℕ)
    (hC : ∀ a ≤ m, C₁ a = C₂ a) (hT : ∀ a ≤ m, T₁ a = T₂ a) :
    parameterJetTransferConstant C₁ T₁ D m = parameterJetTransferConstant C₂ T₂ D m := by
  unfold parameterJetTransferConstant
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  unfold parameterJetTransferCore
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l ≤ j := by simpa using hl
  rw [hC l (hlj.trans hjm), parameterTransitionPrefix_congr (j-l)
    (fun a ha => hT a (ha.trans ((Nat.sub_le j l).trans hjm)))]

theorem parameterTensorProductConstant_congr_prefix {A₁ A₂ B₁ B₂ : ℕ → ℝ} (j : ℕ)
    (hA : ∀ a ≤ j, A₁ a = A₂ a) (hB : ∀ a ≤ j, B₁ a = B₂ a) :
    tensorProductJetConstant A₁ B₁ j = tensorProductJetConstant A₂ B₂ j := by
  unfold tensorProductJetConstant
  apply Finset.sum_congr rfl
  intro a ha
  rw [hA a (by simpa using ha), hB (j-a) (Nat.sub_le _ _)]

theorem parameterTensorTransferConstant_congr_prefix {B₁ B₂ T₁ T₂ J₁ J₂ : ℕ → ℝ}
    (n D m : ℕ) (hB : ∀ a ≤ m, B₁ a = B₂ a)
    (hT : ∀ a ≤ m, T₁ a = T₂ a) (hJ : ∀ a ≤ m, J₁ a = J₂ a) :
    tensorTransferConstant n B₁ T₁ J₁ D m = tensorTransferConstant n B₂ T₂ J₂ D m := by
  have hweight (j : ℕ) (hj : j ≤ m) : tensorFrameWeightConstant B₁ J₁ j =
      tensorFrameWeightConstant B₂ J₂ j := by
    apply parameterTensorProductConstant_congr_prefix j
    · intro a ha
      exact parameterCutoffSquareConstant_congr_prefix a (fun k hk => hB k (hk.trans (ha.trans hj)))
    · intro a ha
      exact parameterTensorProductConstant_congr_prefix a
        (fun k hk => hJ k (hk.trans (ha.trans hj))) (fun k hk => hJ k (hk.trans (ha.trans hj)))
  unfold tensorTransferConstant
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  unfold tensorTransferCore
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l ≤ j := by simpa using hl
  rw [hweight l (hlj.trans hjm), parameterTransitionPrefix_congr (j-l)
    (fun a ha => hT a (ha.trans ((Nat.sub_le j l).trans hjm)))]

section Models
variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace (Ep × Es)] {n d q : ℕ}

/-- The exact map tail constant uses B,T only through m+2, independently of r. -/
theorem parameterMapTailConstant_congr_prefix
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (mu : Measure (Ep × Es)) (kappa : Ep × Es → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m r : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Y B₁ T₁) T₁ D m r =
    parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Y B₂ T₂) T₂ D m r := by
  unfold parameterModelSmoothingTailConstant parameterModelTransferConstant
  rw [parameterJetTransferConstant_congr_prefix D m
    (fun a ha => parameterSpatialTransferCoefficient_congr_prefix a
      (fun b hb => hB b (by omega)) (fun b _ hb => hT b (by omega)))
    (fun a ha => hT a (by omega))]

/-- The same finite geometry suffices for every weighted gain of order m. -/
theorem parameterMapGainConstant_congr_prefix
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (mu : Measure (Ep × Es)) (K : Ep × Es → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    parameterModelSmoothingGainConstant cp cs cy mu K
      (parameterSpatialTransferCoefficient Es Y B₁ T₁) T₁ D m =
    parameterModelSmoothingGainConstant cp cs cy mu K
      (parameterSpatialTransferCoefficient Es Y B₂ T₂) T₂ D m := by
  unfold parameterModelSmoothingGainConstant
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  unfold parameterModelTransferConstant
  rw [parameterJetTransferConstant_congr_prefix D j
    (fun a ha => parameterSpatialTransferCoefficient_congr_prefix a
      (fun b hb => hB b (by omega)) (fun b _ hb => hT b (by omega)))
    (fun a ha => hT a (by omega))]

end Models

section Tensors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {d : ℕ}

/-- The actual source-tangent tensor tail uses B through m and T through m+1. -/
theorem parameterTensorTailConstant_congr_prefix
    (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E) (kappa : E → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m r : ℕ)
    (hB : ∀ a ≤ m, B₁ a = B₂ a) (hT : ∀ a ≤ m+1, T₁ a = T₂ a) :
    modelTensorSmoothingTailConstant n c mu kappa B₁ T₁ (fun j => T₁ (j+1)) D 0 m r =
    modelTensorSmoothingTailConstant n c mu kappa B₂ T₂ (fun j => T₂ (j+1)) D 0 m r := by
  unfold modelTensorSmoothingTailConstant modelTensorTransferConstant
  simp only [Nat.add_zero]
  rw [parameterTensorTransferConstant_congr_prefix n D m hB
    (fun a ha => hT a (by omega)) (fun a ha => hT (a+1) (by omega))]

end Tensors

section Pair
variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace (Ep × Es)] {n d q : ℕ}

/-- The SINGLE constant used in the actual pair endpoint is unchanged when
any normalized geometric derivative above m+2 is changed. In particular,
setting the repair moment order to 40*(k+1) raises no geometric derivative
order unless the fixed observation/input list itself raises m. -/
theorem parameterPairTailConstant_congr_prefix
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (c : (Ep × Es) ≃L[ℝ] (Fin (n+d) → ℝ))
    (mu : Measure (Ep × Es)) (kappa : Ep × Es → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m r : ℕ)
    (hB : ∀ a ≤ m+2, B₁ a = B₂ a) (hT : ∀ a ≤ m+2, T₁ a = T₂ a) :
    max (parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Y B₁ T₁) T₁ D m r)
      (modelTensorSmoothingTailConstant n c mu kappa B₁ T₁ (fun j => T₁ (j+1)) D 0 m r) =
    max (parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Y B₂ T₂) T₂ D m r)
      (modelTensorSmoothingTailConstant n c mu kappa B₂ T₂ (fun j => T₂ (j+1)) D 0 m r) := by
  rw [parameterMapTailConstant_congr_prefix cp cs cy mu kappa D m r hB hT,
    parameterTensorTailConstant_congr_prefix n c mu kappa D m r
      (fun a ha => hB a (by omega)) (fun a ha => hT a (by omega))]

end Pair

#print axioms parameterMapTailConstant_congr_prefix
#print axioms parameterMapGainConstant_congr_prefix
#print axioms parameterTensorTailConstant_congr_prefix
#print axioms parameterPairTailConstant_congr_prefix
end
end GlobalEmbedding.Continuation
