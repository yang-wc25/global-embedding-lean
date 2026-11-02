import NormalPolar.OriginalWaveSeedUniformBudget

/-! A genuine finite raw supplier for any original finite family of legal
waves. Original labels remain Fin r. The subordinate piece index varies with
each original wave and is never used as a new probe-parameter label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

structure OriginalWaveSeedFamily
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (waves : Fin r → LocalLegalWave (n := m+1) F hF) (weight : Fin r → ℝ) where
  refinement : ∀ l, OriginalWaveSeedRefinement F hF (waves l) (weight l)
  inner : ∀ l (s : Fin (refinement l).count), OriginalWaveSeedBuffer (refinement l) s
  outer : ∀ l (s : Fin (refinement l).count), OriginalWaveSeedBuffer (refinement l) s
  nested : ∀ l s, (inner l s).compactTarget ⊆ interior (outer l s).compactTarget
  geometryBudget : ℕ → ℝ
  cutoffBudget : ℕ → ℝ
  normalBudget : ℕ → ℝ
  positive : ∀ n, 0 < geometryBudget n ∧ 0 < cutoffBudget n ∧ 0 < normalBudget n
  raw : ∀ l s (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
    ActualPrescribedSpatialRawProfiles (fun _ : Z => F) (fun _ => hF)
      (fun _ => (outer l s).spatialChart.symm) ((refinement l).cutoffCoordinates s)
      (fun _ x => (waves l).normal ((outer l s).spatialChart.symm x))
      (inner l s).chart univ (tsupport ((refinement l).cutoff s)) n j ell
      (geometryBudget (max n j)) (cutoffBudget n) (normalBudget n)
  raw_sample : ∀ l s n j ell hell hell1,
    (raw l s n j ell hell hell1).sample = (inner l s).chart.target

/-- Every adapted chart, ordinary partition, compact buffer, solver geometry
and uniform finite-family budget is produced from the original legal waves.
The existential family is chosen before all orders and all later scales. -/
theorem exists_originalWaveSeedFamily
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (waves : Fin r → LocalLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l) :
    Nonempty (OriginalWaveSeedFamily F hF waves weight) := by
  let d (l : Fin r) := Classical.choice
    (exists_originalWaveSeedRefinement F hF (waves l) (weight l) (hweight l))
  let b (l : Fin r) (s : Fin (d l).count) :=
    Classical.choice (exists_originalWaveSeedBuffer (d l) s)
  have hex (l : Fin r) (s : Fin (d l).count) :=
    (b l s).exists_actual_raw_full_profiles (hweight l) hImm
  choose outer nested Cg Cchi Cnu hpos hraw using hex
  let G (n : ℕ) := 1 + ∑ l, ∑ s, Cg l s n
  let Chi (n : ℕ) := 1 + ∑ l, ∑ s, Cchi l s n
  let Nu (n : ℕ) := 1 + ∑ l, ∑ s, Cnu l s n
  have hg (n : ℕ) : 0 < G n ∧ ∀ l s, Cg l s n ≤ G n :=
    originalWave_finite_budget (fun l => (d l).count) (fun l s => Cg l s n)
      (fun l s => (hpos l s n).1.le)
  have hc (n : ℕ) : 0 < Chi n ∧ ∀ l s, Cchi l s n ≤ Chi n :=
    originalWave_finite_budget (fun l => (d l).count) (fun l s => Cchi l s n)
      (fun l s => (hpos l s n).2.1.le)
  have hn (n : ℕ) : 0 < Nu n ∧ ∀ l s, Cnu l s n ≤ Nu n :=
    originalWave_finite_budget (fun l => (d l).count) (fun l s => Cnu l s n)
      (fun l s => (hpos l s n).2.2.le)
  refine ⟨{
    refinement := d
    inner := b
    outer := outer
    nested := nested
    geometryBudget := G
    cutoffBudget := Chi
    normalBudget := Nu
    positive := fun n => ⟨(hg n).1,(hc n).1,(hn n).1⟩
    raw := ?_
    raw_sample := ?_ }⟩
  · intro l s n j ell hell hell1
    exact (b l s).enlarge_raw_profiles (outer l s)
      (Classical.choose (hraw l s n j ell hell hell1))
      ((hg (max n j)).2 l s) ((hc n).2 l s) ((hn n).2 l s)
  · intro l s n j ell hell hell1
    exact Classical.choose_spec (hraw l s n j ell hell hell1)

namespace OriginalWaveSeedFamily

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

def physical (family : OriginalWaveSeedFamily F hF waves weight)
    (hweight : ∀ l, 0 < weight l)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (l : Fin r) (s : Fin (family.refinement l).count) :
    ActualPrescribedPhysicalGeometry (fun _ : Z => F) (fun _ => hF)
      (fun _ => (family.outer l s).spatialChart.symm)
      (fun _ x => (waves l).normal ((family.outer l s).spatialChart.symm x))
      (family.inner l s).chart (fun z : Z × M => weight l * (waves l).phase z.2) :=
  (family.inner l s).actual_physical_geometry (family.outer l s)
    (family.nested l s) (hweight l) hImm

theorem sum_original_value (family : OriginalWaveSeedFamily F hF waves weight)
    (l : Fin r) (z : Z × M) :
    ∑ s, (family.refinement l).cutoff s z • ((waves l).normal z.2 : V) =
      (waves l).value z.2 :=
  (family.refinement l).sum_value z

end OriginalWaveSeedFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_originalWaveSeedFamily
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedFamily.physical
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedFamily.sum_original_value

