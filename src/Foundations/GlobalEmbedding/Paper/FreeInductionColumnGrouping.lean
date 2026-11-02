import GlobalEmbedding.Paper.FreeNormalizedColumnStabilityBridge

/-!
# The original column grouping and zero-parameter normalized columns

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 477–489.
This is algebra for the actual limiting-rank proof; no full limiting rank is assumed proved here.
-/

noncomputable section

namespace GlobalEmbedding.Paper

/-- The old first and sorted second rows, embedded in the original successor pairing index. -/
def freeOldColumnIndex (m : ℕ) : BalancedPairingIndex m → BalancedPairingIndex (m + 1)
  | Sum.inl i => Sum.inl i.castSucc
  | Sum.inr ij => Sum.inr ⟨(ij.val.1.castSucc, ij.val.2.castSucc), ij.property⟩

/-- Actual column grouping: old columns and active first column, followed by all second rows
whose second index is active. The last such row is the active-active column. -/
def freeInductionColumnIndex (m : ℕ) :
    (BalancedPairingIndex m ⊕ Unit) ⊕ Fin (m + 1) → BalancedPairingIndex (m + 1)
  | Sum.inl (Sum.inl j) => freeOldColumnIndex m j
  | Sum.inl (Sum.inr _) => Sum.inl (Fin.last m)
  | Sum.inr i => Sum.inr ⟨(i, Fin.last m), Fin.le_last i⟩

/-- The grouping includes every original column, including the repeated active second row. -/
theorem freeInductionColumnIndex_surjective (m : ℕ) :
    Function.Surjective (freeInductionColumnIndex m) := by
  rintro (i | ⟨⟨i, j⟩, hij⟩)
  · by_cases hi : i = Fin.last m
    · subst i
      exact ⟨Sum.inl (Sum.inr ()), rfl⟩
    · have hneq : i.val ≠ m := fun h ↦ hi (Fin.ext h)
      have hlt : i.val < m := by omega
      exact ⟨Sum.inl (Sum.inl (Sum.inl ⟨i.val, hlt⟩)), rfl⟩
  · by_cases hj : j = Fin.last m
    · subst j
      exact ⟨Sum.inr i, rfl⟩
    · have hneq : j.val ≠ m := fun h ↦ hj (Fin.ext h)
      have hjlt : j.val < m := by omega
      have hilt : i.val < m := lt_of_le_of_lt hij hjlt
      exact ⟨Sum.inl (Sum.inl (Sum.inr
        ⟨(⟨i.val, hilt⟩, ⟨j.val, hjlt⟩), hij⟩)), rfl⟩

section TriangularRank

variable {Old New Out Quot : Type*} [Fintype Old] [Fintype New]
  [AddCommGroup Out] [Module ℝ Out] [AddCommGroup Quot] [Module ℝ Quot]

/-- A genuine quotient which kills the old columns and separates the new columns proves
independence of the complete family. Apply the quotient to a vanishing finite combination,
eliminate its new coefficients, then use the actual old independence. -/
theorem free_triangular_column_independence
    (a : Old → Out) (b : New → Out) (Q : Out →ₗ[ℝ] Quot)
    (ha : LinearIndependent ℝ a) (hb : LinearIndependent ℝ (fun i ↦ Q (b i)))
    (hQa : ∀ i, Q (a i) = 0) : LinearIndependent ℝ (Sum.elim a b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have hsum : (∑ i, g (Sum.inl i) • a i) + ∑ i, g (Sum.inr i) • b i = 0 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using hg
  have hq := congrArg Q hsum
  simp only [map_add, map_sum, map_smul, hQa, smul_zero, Finset.sum_const_zero,
    zero_add, map_zero] at hq
  have hn : ∀ i, g (Sum.inr i) = 0 :=
    Fintype.linearIndependent_iff.mp hb (fun i ↦ g (Sum.inr i)) hq
  have ho : ∀ i, g (Sum.inl i) = 0 :=
    Fintype.linearIndependent_iff.mp ha (fun i ↦ g (Sum.inl i)) (by simpa [hn] using hsum)
  cases j with
  | inl i => exact ho i
  | inr i => exact hn i

end TriangularRank

/-- Actual coverage by the column grouping transfers independence back to the original index.
Choose a right inverse of the proved surjection and restrict the independent family to it. -/
theorem freeInductionColumns_independent_of_grouping
    {Out : Type*} [AddCommGroup Out] [Module ℝ Out] (m : ℕ)
    (v : BalancedPairingIndex (m + 1) → Out)
    (hv : LinearIndependent ℝ (v ∘ freeInductionColumnIndex m)) :
    LinearIndependent ℝ v := by
  let hs := freeInductionColumnIndex_surjective m
  have h := hv.comp (Function.surjInv hs) (Function.injective_surjInv hs)
  simpa only [Function.comp_def, Function.surjInv_eq] using h

/-- The actual normalized polynomial at zero is the finite operator of its genuine selected
linear columns and unselected base columns. This includes the whole data space at zero. -/
theorem free_normalized_polynomial_zero_columns
    {Idx Out : Type*} [Fintype Idx] [NormedAddCommGroup Out] [NormedSpace ℝ Out]
    (prj : Out →L[ℝ] Out) (masked : Idx → Bool) (v0 v1 v2 : Idx → Out) :
    freeNormalizedColumnPolynomial prj (freeCoordinateMask masked)
        (freeColumnOperator v0) (freeColumnOperator v1) (freeColumnOperator v2) 0 =
      freeColumnOperator (fun j ↦ if masked j then prj (v1 j) else prj (v0 j)) := by
  rw [freeNormalizedColumnPolynomial_zero]
  ext u
  simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, freeColumnOperator_apply, freeCoordinateMask_apply,
    PiLp.sub_apply, map_sum, map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : masked j = true <;> simp [hj]

#print axioms freeInductionColumnIndex_surjective
#print axioms free_triangular_column_independence
#print axioms freeInductionColumns_independent_of_grouping
#print axioms free_normalized_polynomial_zero_columns

end GlobalEmbedding.Paper
