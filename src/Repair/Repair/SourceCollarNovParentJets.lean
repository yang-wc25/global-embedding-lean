import Repair.SourceCollarNovParentCollars
import Smoothing.TensorLocalNormalizationBounds

/-!
# All-order costs of the actual positive-plateau parent raw function

The scalar derivative bound is constructed on the compact interval fixed by
the original zeroth raw bound. The composition profile is an explicit
factorial and finite-prefix expression, selected before every atlas and raw
family. At order j it depends only on the original prefix through j.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

theorem sourceCollarNov_exists_scalar_jet_bound (C0 : ℝ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 ≤ R j) ∧ ∀ j k, k ≤ j →
      ∀ t ∈ Icc (-max 0 C0) (max 0 C0),
        ‖iteratedFDeriv ℝ k sourceCollarNovPlateauScalar t‖ ≤ R j := by
  have hBound (k : ℕ) : ∃ a : ℝ, 0 ≤ a ∧ ∀ t ∈ Icc (-max 0 C0) (max 0 C0),
      ‖iteratedFDeriv ℝ k sourceCollarNovPlateauScalar t‖ ≤ a := by
    have hCont : Continuous (fun t => ‖iteratedFDeriv ℝ k sourceCollarNovPlateauScalar t‖) :=
      (sourceCollarNovPlateauScalar_contDiff.continuous_iteratedFDeriv (by simp)).norm
    obtain ⟨a,ha⟩ := (isCompact_Icc : IsCompact (Icc (-max 0 C0) (max 0 C0))).bddAbove_image hCont.continuousOn
    exact ⟨max 0 a,le_max_left _ _,fun t ht => (ha ⟨t,ht,rfl⟩).trans (le_max_right _ _)⟩
  choose a ha hBound using hBound
  refine ⟨fun j => ∑ k ∈ Finset.range (j+1), a k,
    fun j => Finset.sum_nonneg (fun k _ => ha k),?_⟩
  intro j k hkj t ht
  exact (hBound k t ht).trans (Finset.single_le_sum (fun r _ => ha r) (by simpa using hkj))

def sourceCollarNovScalarJetBound (C0 : ℝ) : ℕ → ℝ :=
  Classical.choose (sourceCollarNov_exists_scalar_jet_bound C0)

theorem sourceCollarNovScalarJetBound_nonneg (C0 : ℝ) (j : ℕ) :
    0 ≤ sourceCollarNovScalarJetBound C0 j :=
  (Classical.choose_spec (sourceCollarNov_exists_scalar_jet_bound C0)).1 j

def sourceCollarNovParentRawProfile (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ)*sourceCollarNovScalarJetBound (B 0) j*bufferedTransitionPrefix B j^j

theorem sourceCollarNovParentRawProfile_nonneg (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (j : ℕ) :
    0 ≤ sourceCollarNovParentRawProfile B j :=
  mul_nonneg (mul_nonneg (by positivity) (sourceCollarNovScalarJetBound_nonneg (B 0) j))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hB j)) j)

/-- The actual numerical output at order j reads only the original prefix
through j, including the zeroth bound for the fixed scalar interval. -/
theorem sourceCollarNovParentRawProfile_prefix {B C : ℕ → ℝ} (j : ℕ)
    (h : ∀ k, k ≤ j → B k = C k) :
    sourceCollarNovParentRawProfile B j = sourceCollarNovParentRawProfile C j := by
  unfold sourceCollarNovParentRawProfile
  rw [h 0 (Nat.zero_le j)]
  congr 2
  unfold bufferedTransitionPrefix
  congr 1
  exact Finset.sum_congr rfl (fun k hk => h k (by simpa using hk))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sourceCollarNov_parent_raw_composition_jets
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (hJets : ∀ k y, y ∈ O → ‖iteratedFDeriv ℝ k f y‖ ≤ B k)
    (j : ℕ) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (sourceCollarNovPlateauScalar ∘ f) x‖ ≤ sourceCollarNovParentRawProfile B j := by
  have hfx : f x ∈ Icc (-max 0 (B 0)) (max 0 (B 0)) := by
    apply abs_le.mp
    have hh : |f x| ≤ B 0 := by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hJets 0 x hx
    exact hh.trans (le_max_right _ _)
  have hout (k : ℕ) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k sourceCollarNovPlateauScalar univ (f x)‖ ≤
        sourceCollarNovScalarJetBound (B 0) j := by
    rw [iteratedFDerivWithin_univ]
    exact (Classical.choose_spec (sourceCollarNov_exists_scalar_jet_bound (B 0))).2 j k hkj (f x) hfx
  have hin (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k f O x‖ ≤ bufferedTransitionPrefix B j ^ k := by
    rw [iteratedFDerivWithin_of_isOpen _ hO hx]
    have hBprefix : B k ≤ bufferedTransitionPrefix B j := by
      have hsum : B k ≤ ∑ i ∈ Finset.range (j+1), B i :=
        Finset.single_le_sum (fun i _ => hB i) (by simpa using hkj)
      unfold bufferedTransitionPrefix
      linarith
    exact (hJets k x hx).trans (hBprefix.trans (le_self_pow₀ (one_le_bufferedTransitionPrefix hB j) (by omega)))
  have hh := norm_iteratedFDerivWithin_comp_le sourceCollarNovPlateauScalar_contDiff.contDiffOn hf
    (n := j) (by simp) uniqueDiffOn_univ hO.uniqueDiffOn (mapsTo_univ _ _) hx hout hin
  rwa [iteratedFDerivWithin_of_isOpen _ hO hx] at hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParentRawProfile_prefix
#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parent_raw_composition_jets
