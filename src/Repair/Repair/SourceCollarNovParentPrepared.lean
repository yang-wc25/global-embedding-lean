import Repair.SourceCollarNovParentJets

/-!
# A true prepared auxiliary parent family on the unchanged original atlas

The new raw function is explicitly the fixed plateau scalar of the old raw
function. Its all-order bounds are derived, and the original transitions,
enlarged supports, degree, atlas and original norm sets are retained.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}

theorem sourceCollarNovParentRaw_positive (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParentRaw R i) ⊆ {x | (1/2 : ℝ) ≤ R.raw i x} := by
  intro x hx
  apply sourceCollarNovPlateauScalar_tsupport
  exact tsupport_comp_subset_preimage _ (R.smooth i).continuous hx

theorem sourceCollarNovParentRaw_original_support (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParentRaw R i) ⊆ tsupport (R.raw i) := by
  intro x hx
  apply subset_tsupport
  have hh : (1/2 : ℝ) ≤ R.raw i x := sourceCollarNovParentRaw_positive R i hx
  change R.raw i x ≠ 0
  linarith

/-- This is a produced raw preparation, not a new proof obligation.
Its transition profile and enlarged-support degree are exactly T and D. -/
def sourceCollarNovParentRawPreparation (hA : IsSmoothBufferedAtlas A)
    (R : TensorRawCutoffPreparation A B T D) (hB : ∀ j, 0 ≤ B j) :
    TensorRawCutoffPreparation A (sourceCollarNovParentRawProfile B) T D where
  raw := sourceCollarNovParentRaw R
  smooth := sourceCollarNovParentRaw_contMDiff R
  plateau_cover := by
    intro x
    obtain ⟨i,hi⟩ := R.plateau_cover x
    exact ⟨i,by simp only [sourceCollarNovParentRaw,Function.comp_apply,hi,sourceCollarNovPlateauScalar_one]⟩
  inner_support := fun i => (sourceCollarNovParentRaw_original_support R i).trans (R.inner_support i)
  enlarged_support := fun i => (sourceCollarNovParentRaw_original_support R i).trans (R.enlarged_support i)
  degree := R.degree
  own_jets := by
    intro i j y hy
    exact sourceCollarNov_parent_raw_composition_jets B hB (A.chart i).open_target
      (((R.smooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn)
      (R.own_jets i) j y hy
  transition_jets := by
    intro p i k hk y hy hs
    exact R.transition_jets p i k hk y hy (sourceCollarNovParentRaw_original_support R i hs)

/-- The already constructed auxiliary parent is the actual local square
normalization of the newly proved preparation's raw family. -/
theorem sourceCollarNovParent_prepared_formula (hA : IsSmoothBufferedAtlas A)
    (R : TensorRawCutoffPreparation A B T D) (hB : ∀ j, 0 ≤ B j) :
    sourceCollarNovParent R = tensorLocalNormalizedCutoff (sourceCollarNovParentRawPreparation hA R hB).raw := rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParentRawPreparation
#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_prepared_formula
