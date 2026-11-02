import NormalPolar.OriginalWaveSeedFamily
import NormalPolar.OriginalWaveSeedRescaledData

/-! A genuine finite raw supplier for any original finite family of legal
waves. Original labels remain Fin r. The subordinate piece index varies with
each original wave and is never used as a new probe-parameter label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

structure OriginalWaveSeedRescaledFamily
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
  raw : ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) l s (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
    ActualPrescribedSpatialRawProfiles (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
      (fun _ => (outer l s).spatialChart.symm) ((refinement l).cutoffCoordinates s)
      (fun _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
        ((outer l s).spatialChart.symm x) ((waves l).normal ((outer l s).spatialChart.symm x)))
      (inner l s).chart univ (tsupport ((refinement l).cutoff s)) n j ell
      (geometryBudget (max n j)) (cutoffBudget n) (normalBudget n)
  raw_sample : ∀ c hc l s n j ell hell hell1,
    (raw c hc l s n j ell hell hell1).sample = (inner l s).chart.target

/-- Every adapted chart, ordinary partition, compact buffer, solver geometry
and uniform finite-family budget is produced from the original legal waves.
The existential family is chosen before all orders and all later scales. -/
theorem exists_originalWaveSeedRescaledFamily
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (waves : Fin r → LocalLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l) :
    Nonempty (OriginalWaveSeedRescaledFamily F hF waves weight) := by
  let d (l : Fin r) := Classical.choice
    (exists_originalWaveSeedRefinement F hF (waves l) (weight l) (hweight l))
  let b (l : Fin r) (s : Fin (d l).count) :=
    Classical.choice (exists_originalWaveSeedBuffer (d l) s)
  have hex (l : Fin r) (s : Fin (d l).count) :=
    (b l s).exists_rescaled_raw_full_profiles (hweight l) hImm
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
  · intro c hcon l s n j ell hell hell1
    exact ((b l s).rescale c (originalWave_contraction_ne_zero c hcon)).enlarge_raw_profiles
      ((outer l s).rescale c (originalWave_contraction_ne_zero c hcon))
      (Classical.choose (hraw l s c hcon n j ell hell hell1))
      ((hg (max n j)).2 l s) ((hc n).2 l s) ((hn n).2 l s)
  · intro c hcon l s n j ell hell hell1
    exact Classical.choose_spec (hraw l s c hcon n j ell hell hell1)

namespace OriginalWaveSeedRescaledFamily

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

/-- Each contraction uses the very same finite charts, partition, samples,
and globally selected prefix budgets. Only the actual reference map varies. -/
def slice (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) :
    OriginalWaveSeedFamily (c • F) (contMDiff_const_rescale F hF c)
      (fun l => actualRescaledLegalWave F hF c (originalWave_contraction_ne_zero c hc) (waves l))
      weight where
  refinement := fun l => (family.refinement l).rescale c (originalWave_contraction_ne_zero c hc)
  inner := fun l s => (family.inner l s).rescale c (originalWave_contraction_ne_zero c hc)
  outer := fun l s => (family.outer l s).rescale c (originalWave_contraction_ne_zero c hc)
  nested := family.nested
  geometryBudget := family.geometryBudget
  cutoffBudget := family.cutoffBudget
  normalBudget := family.normalBudget
  positive := family.positive
  raw := family.raw c hc
  raw_sample := family.raw_sample c hc

theorem at_inner_chart (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (l : Fin r) (s : Fin (family.refinement l).count) :
    ((family.slice c hc).inner l s).chart = (family.inner l s).chart := rfl

theorem at_outer_chart (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (l : Fin r) (s : Fin (family.refinement l).count) :
    ((family.slice c hc).outer l s).spatialChart = (family.outer l s).spatialChart := rfl

theorem at_budget (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) :
    (family.slice c hc).geometryBudget = family.geometryBudget ∧
    (family.slice c hc).cutoffBudget = family.cutoffBudget ∧
    (family.slice c hc).normalBudget = family.normalBudget := ⟨rfl,rfl,rfl⟩

/-- The literal probe reference is supplied without choosing a fresh chart
or any new raw budget after t. -/
def probe (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (t : ℝ) (ht : 0 < t) (htmax : t ≤ 1/2) :=
  family.slice (Real.sqrt (1-(t^(10:ℕ))^2)) (actual_probe_contraction_mem_Icc t ht htmax)

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_originalWaveSeedRescaledFamily
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.slice
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.probe
