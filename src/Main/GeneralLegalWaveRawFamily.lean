import Main.GeneralLegalWaveRawProfiles
import NormalPolar.JointSecondaryGroupedBudget

/-!
# A shared actual raw-family core for arbitrary legal cutoffs

Every original label retains its own single phase and fixed weight. The
subordinate finite piece index stays dependent on that label. All genuine
raw suppliers are manufactured first and placed under common positive
prefix budgets before contraction, derivative orders or oscillation scale.

This core does not assert observer profiles or a general exact probe family.
-/

noncomputable section
open Set Function Manifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Upgrade
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]

local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

structure GeneralLegalWaveRawFamily
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF) (weight : Fin r → ℝ) where
  piece : ∀ l, GeneralLegalWaveRawProfiles F hF (waves l) (weight l)

theorem exists_generalLegalWaveRawFamily
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hw : ∀ l, 0 < weight l) :
    Nonempty (GeneralLegalWaveRawFamily F hF waves weight) := by
  refine ⟨{piece := ?_}⟩
  intro l
  exact Classical.choice
    (exists_generalLegalWaveRawProfiles F hF hImm (waves l) (weight l) (hw l))

namespace GeneralLegalWaveRawFamily

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

def geometryBudget (d : GeneralLegalWaveRawFamily F hF waves weight) (n : ℕ) : ℝ :=
  1 + ∑ l, (d.piece l).seed.geometryBudget n

def cutoffBudget (d : GeneralLegalWaveRawFamily F hF waves weight) (n : ℕ) : ℝ :=
  1 + ∑ l, (d.piece l).cutoffBudget n

def normalBudget (d : GeneralLegalWaveRawFamily F hF waves weight) (n : ℕ) : ℝ :=
  1 + ∑ l, (d.piece l).normalBudget n

theorem positive (d : GeneralLegalWaveRawFamily F hF waves weight) (n : ℕ) :
    0 < d.geometryBudget n ∧ 0 < d.cutoffBudget n ∧ 0 < d.normalBudget n := by
  exact ⟨add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun l _ => ((d.piece l).positive n).1.le)),
    add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun l _ => ((d.piece l).positive n).2.1.le)),
    add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun l _ => ((d.piece l).positive n).2.2.le))⟩

theorem geometry_le (d : GeneralLegalWaveRawFamily F hF waves weight) (l : Fin r) (n : ℕ) :
    (d.piece l).seed.geometryBudget n ≤ d.geometryBudget n :=
  (Finset.single_le_sum (fun l _ => ((d.piece l).positive n).1.le) (Finset.mem_univ l)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem cutoff_le (d : GeneralLegalWaveRawFamily F hF waves weight) (l : Fin r) (n : ℕ) :
    (d.piece l).cutoffBudget n ≤ d.cutoffBudget n :=
  (Finset.single_le_sum (fun l _ => ((d.piece l).positive n).2.1.le) (Finset.mem_univ l)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem normal_le (d : GeneralLegalWaveRawFamily F hF waves weight) (l : Fin r) (n : ℕ) :
    (d.piece l).normalBudget n ≤ d.normalBudget n :=
  (Finset.single_le_sum (fun l _ => ((d.piece l).positive n).2.2.le) (Finset.mem_univ l)).trans
    (le_add_of_nonneg_left zero_le_one)

def raw (d : GeneralLegalWaveRawFamily F hF waves weight)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (l : Fin r) (i : Fin (d.piece l).seed.refinement.count)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) :
    ActualPrescribedSpatialRawProfiles
      (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      ((d.piece l).seed.coordinate i) ((d.piece l).seed.cutoffCoordinates i)
      ((d.piece l).seed.scaledNormal scale hs i) ((d.piece l).seed.physicalChart i)
      univ ((d.piece l).seed.carrier i) n j ell
      (d.geometryBudget (max n j)) (d.cutoffBudget n) (d.normalBudget n) :=
  ((d.piece l).raw scale hs n j ell he he1 i).enlargeBudgets
    (d.geometryBudget (max n j)) (d.cutoffBudget n) (d.normalBudget n)
    (d.geometry_le l (max n j)) (d.cutoff_le l n) (d.normal_le l n)

theorem raw_sample (d : GeneralLegalWaveRawFamily F hF waves weight)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (l : Fin r) (i : Fin (d.piece l).seed.refinement.count)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) :
    (d.raw scale hs l i n j ell he he1).sample =
      ((d.piece l).seed.physicalChart i).target :=
  (d.piece l).raw_sample scale hs n j ell he he1 i

theorem phase_coordinate (d : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (i : Fin (d.piece l).seed.refinement.count) (z : Z × M)
    (hz : z ∈ ((d.piece l).seed.physicalChart i).source) :
    weight l * (waves l).phase z.2 = (((d.piece l).seed.physicalChart i) z).2 0 :=
  ((d.piece l).seed.inner i).adaptation z.2 hz.2

theorem inverse_phase (d : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (i : Fin (d.piece l).seed.refinement.count) (z : Z × D)
    (hz : z ∈ ((d.piece l).seed.physicalChart i).target) :
    weight l * (waves l).phase ((d.piece l).seed.coordinate i z.1 z.2) = z.2 0 :=
  ((d.piece l).seed.outer i).inverse_phase z.2
    ((d.piece l).seed.inner_target_subset_outer i hz.2)

theorem sum_value (d : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (x : M) :
    ∑ i, (d.piece l).seed.pieceCutoff i x • ((waves l).normal x : V) = (waves l).value x :=
  (d.piece l).seed.sum_value x

theorem sum_paired_value (d : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (x : M) (b : Bool) (tau : ℝ) :
    ∑ i, probeTrig b (weight l * (waves l).phase x / tau) •
      ((d.piece l).seed.pieceCutoff i x • ((waves l).normal x : V)) =
        probeTrig b (weight l * (waves l).phase x / tau) • (waves l).value x := by
  rw [← Finset.smul_sum,d.sum_value]

/-- All within-label cross terms survive the finite subdivision. -/
theorem all_cross_terms (d : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (x : M) :
    (∑ i, ∑ j,
      inner ℝ ((d.piece l).seed.pieceCutoff i x • ((waves l).normal x : V))
        ((d.piece l).seed.pieceCutoff j x • ((waves l).normal x : V))) =
      ‖(waves l).value x‖^2 := by
  rw [← d.sum_value l x]
  simp only [← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
  exact Finset.sum_comm

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.exists_generalLegalWaveRawFamily
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.raw
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.raw_sample
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.phase_coordinate
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.inverse_phase
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.all_cross_terms
