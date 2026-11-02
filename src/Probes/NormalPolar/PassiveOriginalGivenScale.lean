import Probes.ActualOriginalGivenProfile

/-! The original Given input's fixed scale-one finite values already
supply one budget sequence for every smaller derivative scale. No choice
of constants after ell, and no output norm, is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

theorem passiveOriginal_weighted_le_one {a q : ℕ} {Idx : Type*} [Fintype Idx]
    (base j : ℕ) (ell : ℝ) (hell : ell ≤ 1)
    (f : Idx → (Fin a → ℝ) → Fin q → ℝ)
    (O S : Idx → Set (Fin a → ℝ)) :
    paperAtlasWeighted base j ell f O S ≤ paperAtlasWeighted base j 1 f O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_le_sum
  intro k hk
  gcongr

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]

theorem passiveOriginal_given_le_one (Data : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) (hell : ell ≤ 1) :
    actualOriginalGivenInputProfile Data j ell ≤ actualOriginalGivenInputProfile Data j 1 := by
  unfold actualOriginalGivenInputProfile
  apply max_le_max
  · unfold incrementsOriginalInputProfileWithLinear
    apply max_le_max
    · unfold incrementsOriginalCoreInputProfile
      apply max_le_max (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
      apply max_le_max (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
      apply iSup_mono
      intro nu
      apply max_le_max (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
      exact max_le_max (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
        (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
    · exact iSup_mono (fun nu => passiveOriginal_weighted_le_one _ _ ell hell _ _ _)
  · exact max_le_max (iSup_mono (fun nu => passiveOriginal_weighted_le_one _ _ ell hell _ _ _))
      (passiveOriginal_weighted_le_one _ _ ell hell _ _ _)

theorem passiveOriginal_given_fixed_scale_budget (Data : IncrementsOriginalNativeData n d N M P)
    (hfinite : ∀ j, actualOriginalGivenInputProfile Data j 1 ≠ ⊤) :
    ∀ j ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j ell).toReal ≤
        (actualOriginalGivenInputProfile Data j 1).toReal := by
  intro j ell hell hell1
  have h := passiveOriginal_given_le_one Data j ell hell1
  exact ⟨ne_top_of_le_ne_top (hfinite j) h,ENNReal.toReal_mono (hfinite j) h⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_given_fixed_scale_budget
