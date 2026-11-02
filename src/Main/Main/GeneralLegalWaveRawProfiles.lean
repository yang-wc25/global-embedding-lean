import Main.GeneralLegalWaveSeedProfiles
import Main.GeneralPrescribedRawGeometry
import NormalPolar.ActualProbeRescaledLegalWave

/-!
# Actual prescribed raw profiles for an arbitrary supported legal wave

This producer starts from the original immersion and arbitrary smooth
cutoff. It chooses one genuine weighted-phase seed, proves the actual
cutoff/normal profiles on its nested compact buffers, and reuses that
seed's unit-scale geometry. All raw coefficients, whole-target samples
and prefix budgets are manufactured outputs. No raw supplier or response
estimate is an input.

This closes a primitive source-construction boundary. Observer-transition
profiles, original-label family assembly and the general exact probes
output are still separate obligations.
-/

noncomputable section
open Set Function Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]

local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

namespace GeneralLegalWaveSeed

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : OpenSupportedLegalWave (n := m+1) F hF} {weight : ℝ}

def coordinate (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : Z → D → M :=
  fun _ => (d.outer i).chart.symm

theorem contraction_ne_zero (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1) : scale ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hs.1)

def scaledNormal (d : GeneralLegalWaveSeed F hF w weight)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1) (i : Fin d.refinement.count) :
    (b : Z) → (x : D) → normalSpace (I := IM) (scale • F) (d.coordinate i b x) :=
  fun b x => actualRescaledNormal F hF scale (contraction_ne_zero scale hs)
    (d.coordinate i b x) (w.normal (d.coordinate i b x))

def geometryBudget (d : GeneralLegalWaveSeed F hF w weight) (k : ℕ) : ℝ :=
  d.Mg (max k k)

end GeneralLegalWaveSeed

/-- A single actual general wave supplies all prescribed raw profiles with
one finite geometry and budget functions fixed before contraction and scale. -/
structure GeneralLegalWaveRawProfiles
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) where
  seed : GeneralLegalWaveSeed F hF w weight
  cutoffBudget : ℕ → ℝ
  normalBudget : ℕ → ℝ
  positive : ∀ n, 0 < seed.geometryBudget n ∧ 0 < cutoffBudget n ∧ 0 < normalBudget n
  raw : ∀ scale (hs : scale ∈ Icc (1/2 : ℝ) 1) n j ell,
    0 ≤ ell → ell ≤ 1 → ∀ i : Fin seed.refinement.count,
    ActualPrescribedSpatialRawProfiles
      (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      (seed.coordinate i) (seed.cutoffCoordinates i) (seed.scaledNormal scale hs i)
      (seed.physicalChart i) univ (seed.carrier i) n j ell
      (seed.geometryBudget (max n j)) (cutoffBudget n) (normalBudget n)
  raw_sample : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).sample = (seed.physicalChart i).target

/-- Every geometry, primitive coefficient bound and sample identity is
produced from the actual original wave. No bump conversion is used. -/
theorem exists_generalLegalWaveRawProfiles
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) (hw : 0 < weight) :
    Nonempty (GeneralLegalWaveRawProfiles F hF w weight) := by
  obtain ⟨d⟩ := exists_generalLegalWaveSeed F hF hImm w weight hw
  choose Cchi Cnu hpos hprofile using fun i => d.exists_primitive_profiles i
  let Bchi (n : ℕ) : ℝ := 1 + ∑ i, Cchi i n
  let Bnu (n : ℕ) : ℝ := 1 + ∑ i, Cnu i n
  have hchi (n : ℕ) : 0 < Bchi n := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun i _ => (hpos i n).1.le))
  have hnu (n : ℕ) : 0 < Bnu n := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun i _ => (hpos i n).2.le))
  have hCchi (i : Fin d.refinement.count) (n : ℕ) : Cchi i n ≤ Bchi n :=
    (Finset.single_le_sum (fun i _ => (hpos i n).1.le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hCnu (i : Fin d.refinement.count) (n : ℕ) : Cnu i n ≤ Bnu n :=
    (Finset.single_le_sum (fun i _ => (hpos i n).2.le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨{
    seed := d
    cutoffBudget := Bchi
    normalBudget := Bnu
    positive := fun n => ⟨(d.positive (max n n)).1,hchi n,hnu n⟩
    raw := ?_
    raw_sample := ?_ }⟩
  · intro scale hs n j ell he he1 i
    let g := d.raw scale hs (max n j) (max n j) 1 zero_le_one le_rfl i
    refine generalPrescribedRawOfUnitGeometry
      (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      (d.coordinate i) (d.cutoffCoordinates i) (d.scaledNormal scale hs i)
      (d.physicalChart i) univ (d.carrier i) n j ell
      (d.geometryBudget (max n j)) (Bchi n) (Bnu n) he he1 g
      (d.raw_c scale hs (max n j) (max n j) 1 zero_le_one le_rfl i)
      (d.raw_chart scale hs (max n j) (max n j) 1 zero_le_one le_rfl i)
      (d.raw_sample scale hs (max n j) (max n j) 1 zero_le_one le_rfl i)
      (d.raw_support scale hs (max n j) (max n j) 1 zero_le_one le_rfl i)
      (d.cutoffCoordinates_support i) (d.cutoffCoordinates_smooth i)
      (d.normalCoordinates_smooth i) ?_ ?_
    · intro k hk z hz
      exact ((hprofile i ell he he1 n k hk z hz).1).trans (hCchi i n)
    · intro k hk z hz
      exact ((hprofile i ell he he1 n k hk z hz).2).trans (hCnu i n)
  · intros
    apply generalPrescribedRawOfUnitGeometry_sample

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.exists_generalLegalWaveRawProfiles
