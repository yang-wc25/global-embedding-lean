import NormalPolar.JointSecondarySignedChoices
import Probes.ActualIncrementSecondaryEmptyPadding
import Probes.Round3ParameterSecondaryEmptyPadding

/-! Different signed phases may need different finite adapted refinements.
A single common finite index is obtained by their dependent sum. Entries
belonging to another signed record use the genuine empty restriction of
their fixed host chart and literal zero cutoff. Active charts, phases and
cross terms are retained; no new primary phase label is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep P Rec : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
  [Fintype Rec] [DecidableEq Rec]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {phase : Rec → M → ℝ} {K O : Rec → Set M}
  (seeds : (r : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (phase r) (K r) (O r))

def jointSecondarySeedPaddedChoice (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) : Round3ParameterSecondaryChoice P M m :=
  if s.1 = r then (seeds s.1).choice s.2
  else round3ParameterSecondaryEmptyChoice ((seeds s.1).outer s.2).chart

theorem jointSecondarySeedPaddedChoice_preserves (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    Round3ParameterChartPreserves (jointSecondarySeedPaddedChoice (P := P) seeds r s).chart := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedChoice,if_pos h]
    exact (seeds s.1).choice_preserves s.2
  · simp only [jointSecondarySeedPaddedChoice,if_neg h]
    exact round3ParameterSecondaryEmptyChoice_preserves _

theorem jointSecondarySeedPaddedChoice_host (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedChoice (P := P) seeds r s).host = ((seeds s.1).outer s.2).chart := by
  by_cases h : s.1 = r <;> simp only [jointSecondarySeedPaddedChoice,h,ite_true,ite_false]
  all_goals rfl

theorem jointSecondarySeedPaddedChoice_cutoff (r : Rec)
    (s : Σ r, Fin (seeds r).refinement.count) (z : P × M) :
    (jointSecondarySeedPaddedChoice seeds r s).cutoff z =
      if s.1 = r then (seeds s.1).refinement.cutoff s.2 z.2 else 0 := by
  by_cases h : s.1 = r <;> simp only [jointSecondarySeedPaddedChoice,h,ite_true,ite_false]
  all_goals rfl

theorem jointSecondarySeedPaddedChoice_partition (r : Rec) (z : P × M) (hz : z.2 ∈ K r) :
    ∑ s, (jointSecondarySeedPaddedChoice seeds r s).cutoff z = 1 := by
  simp only [jointSecondarySeedPaddedChoice_cutoff,Fintype.sum_sigma,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (seeds r).refinement.partition z.2 hz

def jointSecondarySeedGeometryBudget (n : ℕ) : ℝ := 1+∑ r, (seeds r).Mg n

def jointSecondarySeedCutoffBudget (n : ℕ) : ℝ := 1+∑ r, (seeds r).Kcut n

theorem jointSecondarySeedGeometryBudget_positive (n : ℕ) :
    0 < jointSecondarySeedGeometryBudget seeds n :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun r _ => ((seeds r).positive n).1.le))

theorem jointSecondarySeedCutoffBudget_positive (n : ℕ) :
    0 < jointSecondarySeedCutoffBudget seeds n :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun r _ => ((seeds r).positive n).2.le))

theorem jointSecondarySeedGeometryBudget_piece (r : Rec) (n : ℕ) :
    (seeds r).Mg n ≤ jointSecondarySeedGeometryBudget seeds n :=
  (Finset.single_le_sum (fun r _ => ((seeds r).positive n).1.le) (Finset.mem_univ r)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem jointSecondarySeedCutoffBudget_piece (r : Rec) (n : ℕ) :
    (seeds r).Kcut n ≤ jointSecondarySeedCutoffBudget seeds n :=
  (Finset.single_le_sum (fun r _ => ((seeds r).positive n).2.le) (Finset.mem_univ r)).trans
    (le_add_of_nonneg_left zero_le_one)

def jointSecondarySeedPaddedRaw (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
      (fun _ => contMDiff_const_rescale F hF scale) n j ell
      (jointSecondarySeedGeometryBudget seeds (max n j)) univ :=
  if s.1 = r then
    ((seeds s.1).raw scale hs n j ell he he1 s.2).enlargeBudget
      (jointSecondarySeedGeometryBudget_piece seeds s.1 (max n j))
  else actualSecondaryEmptyRawGeometry (fun _ : Ep => scale • F)
    (fun _ => contMDiff_const_rescale F hF scale) n j ell
    (jointSecondarySeedGeometryBudget seeds (max n j)) univ
    ((seeds s.1).outer s.2).chart ((seeds s.1).outer s.2).maximal (fun z => phase r z.2)

theorem jointSecondarySeedPaddedRaw_choice (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).c =
        (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).c ∧
    (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).chart =
        (jointSecondarySeedPaddedChoice (P := Ep) seeds r s).chart ∧
    (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).phase =
        (fun z => phase r z.2) := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,jointSecondarySeedPaddedChoice,if_pos h]
    have hp := (seeds s.1).raw_choice scale hs n j ell he he1 s.2
    exact ⟨hp.1,hp.2.1,hp.2.2.trans (by rw [h])⟩
  · simp only [jointSecondarySeedPaddedRaw,jointSecondarySeedPaddedChoice,if_neg h]
    exact ⟨rfl,rfl,rfl⟩

theorem jointSecondarySeedPaddedRaw_sample (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (r : Rec) (s : Σ r, Fin (seeds r).refinement.count) :
    (jointSecondarySeedPaddedRaw seeds scale hs n j ell he he1 r s).sample =
      if s.1 = r then univ ×ˢ ((seeds s.1).inner s.2).chart.target else ∅ := by
  by_cases h : s.1 = r
  · simp only [jointSecondarySeedPaddedRaw,if_pos h]
    exact (seeds s.1).raw_sample _ _ _ _ _ _ _ _
  · simp only [jointSecondarySeedPaddedRaw,if_neg h]
    rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPaddedChoice_partition
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPaddedRaw_choice
#print axioms GlobalEmbedding.Continuation.jointSecondarySeedPaddedRaw_sample
