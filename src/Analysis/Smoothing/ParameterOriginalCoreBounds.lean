import Smoothing.ParameterPreparedTotalPair

/-!
# The frozen Core MAX supplies the literal total-map/tensor pair budgets

Every coordinate function, differentiation domain, norm domain and compact
parameter evaluation set is taken directly from IncrementsOriginalNativeData.
The frozen Core definition is unchanged. Its total-joint base-two map and
base-zero tensor entries bound the corresponding pair sum with factor two.
No conclusion about inclusion of convolution sampling buffers is substituted
for that separate geometric obligation.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace P]

/-- Exactly the two frozen original Core entries, summed on its original domains. -/
def parameterOriginalCorePairProfile (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart
    D.sourceNormDomain D.parameterNormDomain D.parameterSet
  paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F) O S +
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H) O S

theorem parameterOriginalCore_map_le (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 2 j ell (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet) ≤ incrementsOriginalCoreInputProfile D j ell :=
  le_max_left _ _

theorem parameterOriginalCore_tensor_le (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart
        D.sourceNormDomain D.parameterNormDomain D.parameterSet) ≤ incrementsOriginalCoreInputProfile D j ell :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem parameterOriginalCore_pair_le_two_mul (D : IncrementsOriginalNativeData n d N M P)
    (j : ℕ) (ell : ℝ) :
    parameterOriginalCorePairProfile D j ell ≤ 2 * incrementsOriginalCoreInputProfile D j ell := by
  rw [two_mul]
  exact add_le_add (parameterOriginalCore_map_le D j ell) (parameterOriginalCore_tensor_le D j ell)

/-- The original MAX's finiteness is checked before either norm is projected to R. -/
theorem parameterOriginalCore_pair_finite_and_budget
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤)
    (budget : ℝ) (hbudget : (incrementsOriginalCoreInputProfile D j ell).toReal ≤ budget) :
    parameterOriginalCorePairProfile D j ell ≠ ⊤ ∧
      (parameterOriginalCorePairProfile D j ell).toReal ≤ 2*budget := by
  have hG := ne_top_of_le_ne_top hfinite (parameterOriginalCore_map_le D j ell)
  have hH := ne_top_of_le_ne_top hfinite (parameterOriginalCore_tensor_le D j ell)
  refine ⟨ENNReal.add_ne_top.mpr ⟨hG,hH⟩,?_⟩
  rw [parameterOriginalCorePairProfile,ENNReal.toReal_add hG hH]
  calc
    _ ≤ (incrementsOriginalCoreInputProfile D j ell).toReal +
        (incrementsOriginalCoreInputProfile D j ell).toReal :=
      add_le_add (ENNReal.toReal_mono hfinite (parameterOriginalCore_map_le D j ell))
        (ENNReal.toReal_mono hfinite (parameterOriginalCore_tensor_le D j ell))
    _ ≤ budget+budget := add_le_add hbudget hbudget
    _ = 2*budget := (two_mul budget).symm

theorem parameterPaperAtlasCj_base_le_weighted {ι : Type*} [Fintype ι] {a q : ℕ}
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasCj base f O S ≤ paperAtlasWeighted base j ell f O S := by
  have h := Finset.single_le_sum (s := Finset.range (j+1))
    (f := fun k => ENNReal.ofReal ell ^ k * paperAtlasCj (k+base) f O S)
    (fun k _ => bot_le (α := ℝ≥0∞)) (show 0 ∈ Finset.range (j+1) by simp)
  simpa only [paperAtlasWeighted,pow_zero,one_mul,zero_add] using h

/-- The same frozen Core supplies the true total C2 and tensor C0 gain inputs. -/
theorem parameterOriginalCore_base_gain_inputs
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ)
    (hfinite : incrementsOriginalCoreInputProfile D j ell ≠ ⊤) :
    let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
    let S := incrementsOriginalEvaluation D.atlas D.parameterChart
      D.sourceNormDomain D.parameterNormDomain D.parameterSet
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F) O S ≠ ⊤ ∧
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F) O S).toReal ≤
        (incrementsOriginalCoreInputProfile D j ell).toReal) ∧
    (paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H) O S ≠ ⊤ ∧
      (paperAtlasCj 0 (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H) O S).toReal ≤
        (incrementsOriginalCoreInputProfile D j ell).toReal) := by
  have hG := (parameterPaperAtlasCj_base_le_weighted 2 j ell
    (incrementsOriginalMapCoordinates D.atlas D.parameterChart D.F) _ _).trans
      (parameterOriginalCore_map_le D j ell)
  have hH := (parameterPaperAtlasCj_base_le_weighted 0 j ell
    (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H) _ _).trans
      (parameterOriginalCore_tensor_le D j ell)
  exact ⟨⟨ne_top_of_le_ne_top hfinite hG,ENNReal.toReal_mono hfinite hG⟩,
    ⟨ne_top_of_le_ne_top hfinite hH,ENNReal.toReal_mono hfinite hH⟩⟩

#print axioms parameterOriginalCore_pair_finite_and_budget
#print axioms parameterOriginalCore_base_gain_inputs
end
end GlobalEmbedding.Continuation
