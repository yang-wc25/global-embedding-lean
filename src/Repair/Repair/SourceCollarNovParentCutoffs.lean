import Smoothing.TensorLocalNormalization

/-!
# Auxiliary parent cutoffs from the original positive plateaus

These functions are additional observation parents. They do not replace
any original primary cutoff, phase, decomposition or free normal. Their
support is contained in the same original raw support. Each original unit
plateau remains a unit plateau, so their actual square normalization is a
partition. The fixed scalar construction has no atlas-dependent choice.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

/-- A fixed smooth function, one at one and supported where t ≥ 1/2. -/
def sourceCollarNovPlateauScalar (t : ℝ) : ℝ := tensorCoverageBump (4*(1-t))

theorem sourceCollarNovPlateauScalar_contDiff : ContDiff ℝ ∞ sourceCollarNovPlateauScalar :=
  tensorCoverageBump.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem sourceCollarNovPlateauScalar_one : sourceCollarNovPlateauScalar 1 = 1 := by
  apply tensorCoverageBump.one_of_mem_closedBall
  norm_num [tensorCoverageBump]

theorem sourceCollarNovPlateauScalar_zero {t : ℝ} (ht : t < 1/2) :
    sourceCollarNovPlateauScalar t = 0 := by
  apply tensorCoverageBump.zero_of_le_dist
  change 2 ≤ dist (4*(1-t)) (0 : ℝ)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 4*(1-t))]
  linarith

theorem sourceCollarNovPlateauScalar_tsupport :
    tsupport sourceCollarNovPlateauScalar ⊆ Ici (1/2 : ℝ) := by
  apply closure_minimal _ isClosed_Ici
  intro t ht
  by_contra hn
  exact ht (sourceCollarNovPlateauScalar_zero (lt_of_not_ge hn))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}

/-- An auxiliary parent raw function; the original raw family is untouched. -/
def sourceCollarNovParentRaw (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) : M → ℝ :=
  sourceCollarNovPlateauScalar ∘ R.raw i

def sourceCollarNovParent (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) : M → ℝ :=
  tensorLocalNormalizedCutoff (sourceCollarNovParentRaw R) i

theorem sourceCollarNovParentRaw_contMDiff (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (sourceCollarNovParentRaw R i) :=
  sourceCollarNovPlateauScalar_contDiff.comp_contMDiff (R.smooth i)

theorem sourceCollarNovParent_contMDiff (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (sourceCollarNovParent R i) :=
  tensorLocalNormalizedCutoff_contMDiff _ (sourceCollarNovParentRaw_contMDiff R) i

theorem sourceCollarNovParent_positive (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParent R i) ⊆ {x | (1/2 : ℝ) ≤ R.raw i x} := by
  intro x hx
  apply sourceCollarNovPlateauScalar_tsupport
  exact tsupport_comp_subset_preimage _ (R.smooth i).continuous
    (tensorLocalNormalizedCutoff_tsupport_subset (sourceCollarNovParentRaw R) i hx)

theorem sourceCollarNovParent_original_support (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParent R i) ⊆ tsupport (R.raw i) := by
  intro x hx
  apply subset_tsupport
  have h : (1/2 : ℝ) ≤ R.raw i x := sourceCollarNovParent_positive R i hx
  change R.raw i x ≠ 0
  linarith

theorem sourceCollarNovParent_inner_support (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParent R i) ⊆ A.inner i :=
  (sourceCollarNovParent_original_support R i).trans (R.inner_support i)

theorem sourceCollarNovParent_square_sum (R : TensorRawCutoffPreparation A B T D) (x : M) :
    ∑ i, sourceCollarNovParent R i x ^ 2 = 1 := by
  apply tensorLocalNormalizedCutoff_square_sum
  apply (by norm_num : (2 : ℝ) ≤ 4).trans
  apply tensorLocalCoverageSum_four_le
  obtain ⟨i,hi⟩ := R.plateau_cover x
  exact ⟨i,by simp only [sourceCollarNovParentRaw,Function.comp_apply,hi,sourceCollarNovPlateauScalar_one]⟩

theorem sourceCollarNovParent_overlap (R : TensorRawCutoffPreparation A B T D) (i j : Fin A.count) :
    tsupport (sourceCollarNovParent R i) ∩ tsupport (sourceCollarNovParent R j) ⊆
      tsupport (R.raw i) ∩ tsupport (R.raw j) := by
  intro x hx
  exact ⟨sourceCollarNovParent_original_support R i hx.1,
    sourceCollarNovParent_original_support R j hx.2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_square_sum
#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_original_support
