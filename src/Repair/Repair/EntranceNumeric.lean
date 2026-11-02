import Smoothing.ParameterRound2InitialWeights

/-!
# A numeric entrance scale for the original repair construction

The scale and the C440 error radius are functions of allowed reference
bounds.  In particular they are selected before a reference map, an atlas
index type, or a target metric.  The only input orders used by this file
are map442 and reference-tensor440.  All norms below are the existing
original MAX coordinate norms, with their original domains unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ENNReal BigOperators
namespace GlobalEmbedding.Continuation

/-- The original initial scale, uniformly chosen from numerical bounds.
`low` bounds the reference C2/C0 pair, and `high` its C442/C440 pair. -/
def repairEntranceScale (budget epsilon cap low high : ℝ) : ℝ :=
  min cap (min (1/2) (min (epsilon/(8*(low+1)))
    ((budget/2-low)/(1+440*high))))

/-- The target metric is inspected only through this C440 error radius. -/
def repairEntranceMetricRadius (t budget eta : ℝ) : ℝ :=
  min (t^20*(budget/(4*441))) (t^20*(eta/2))

theorem repairEntranceScale_pos
    {budget epsilon cap low high : ℝ}
    (hepsilon : 0 < epsilon) (hcap : 0 < cap)
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high) (hbudget : 4*low < budget) :
    0 < repairEntranceScale budget epsilon cap low high := by
  unfold repairEntranceScale
  apply lt_min hcap
  apply lt_min (by norm_num)
  exact lt_min (div_pos hepsilon (by positivity))
    (div_pos (by linarith) (by positivity))

theorem repairEntranceScale_le_cap (budget epsilon cap low high : ℝ) :
    repairEntranceScale budget epsilon cap low high ≤ cap :=
  min_le_left _ _

theorem repairEntranceScale_le_half (budget epsilon cap low high : ℝ) :
    repairEntranceScale budget epsilon cap low high ≤ 1/2 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem repairEntranceScale_le_scaling (budget epsilon cap low high : ℝ) :
    repairEntranceScale budget epsilon cap low high ≤ epsilon/(8*(low+1)) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem repairEntranceScale_le_pair (budget epsilon cap low high : ℝ) :
    repairEntranceScale budget epsilon cap low high ≤ (budget/2-low)/(1+440*high) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem repairEntranceMetricRadius_pos
    {t budget eta : ℝ} (ht : 0 < t) (hbudget : 0 < budget) (heta : 0 < eta) :
    0 < repairEntranceMetricRadius t budget eta := by
  unfold repairEntranceMetricRadius
  positivity

/-- Every reference pair in the given numerical class has the original
weighted entrance budget at the same preselected scale.  There is no
quantifier over chart count in the scale and no target data in it. -/
theorem repairEntrance_reference_pair_bound
    {ι : Type*} [Fintype ι] {a q q' : ℕ}
    (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (g : ι → (Fin a → ℝ) → Fin q' → ℝ)
    (O S : ι → Set (Fin a → ℝ))
    (hfFinite : paperAtlasCj 442 f O S ≠ ⊤)
    (hgFinite : paperAtlasCj 440 g O S ≠ ⊤)
    {budget epsilon cap low high t : ℝ}
    (hlow : 0 ≤ low) (hhigh : 0 ≤ high)
    (hLow : (paperAtlasCj 2 f O S).toReal+(paperAtlasCj 0 g O S).toReal ≤ low)
    (hHigh : (paperAtlasCj 442 f O S).toReal+(paperAtlasCj 440 g O S).toReal ≤ high)
    (ht : 0 ≤ t) (htt : t ≤ repairEntranceScale budget epsilon cap low high) :
    (paperAtlasWeighted 2 440 t f O S).toReal+
      (paperAtlasWeighted 0 440 t g O S).toReal ≤ budget/2 := by
  have ht1 : t ≤ 1 := (htt.trans
    (repairEntranceScale_le_half budget epsilon cap low high)).trans (by norm_num)
  have hcap := htt.trans (repairEntranceScale_le_pair budget epsilon cap low high)
  have hpaid : t*(1+440*high) ≤ budget/2-low :=
    (le_div_iff₀ (by positivity : 0 < 1+440*high)).mp hcap
  have hf := parameterRound2_paperAtlasWeighted_le_base_add_top 2 440 ht ht1 f O S hfFinite
  have hg := parameterRound2_paperAtlasWeighted_le_base_add_top 0 440 ht ht1 g O S hgFinite
  norm_num only [Nat.cast_ofNat, Nat.add_zero] at hf hg
  have htop := mul_le_mul_of_nonneg_left hHigh (by positivity : 0 ≤ t*440)
  nlinarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntrance_reference_pair_bound
#print axioms GlobalEmbedding.Continuation.repairEntranceScale_pos
#print axioms GlobalEmbedding.Continuation.repairEntranceMetricRadius_pos
