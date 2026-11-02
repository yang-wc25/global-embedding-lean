import NormalPolar.JointSecondarySignedRefinement
import NormalPolar.PassiveParameterJets
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual nested compact target buffers for the signed-phase partition.
Their literal chart functions and full cutoff carriers are retained. Raw
profile constants are selected on the compact buffer before scale/order use. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "Z" => EuclideanSpace ℝ (Fin 0)

structure JointSecondarySignedBuffer {phase : M → ℝ} {K O : Set M}
    (d : JointSecondarySignedRefinement (m := m) phase K O) (i : Fin d.count) where
  compactTarget : Set D
  compact : IsCompact compactTarget
  contained : compactTarget ⊆ (d.chart i).target
  contains_support : (d.chart i) '' tsupport (d.cutoff i) ⊆ interior compactTarget

variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}

theorem jointSecondary_exists_signed_buffer (d : JointSecondarySignedRefinement (m := m) phase K O)
    (i : Fin d.count) : Nonempty (JointSecondarySignedBuffer d i) := by
  have hcompact := (isClosed_tsupport (d.cutoff i)).isCompact
  have himage := hcompact.image_of_continuousOn ((d.chart i).continuousOn.mono (d.cutoff_support i))
  have htarget : (d.chart i) '' tsupport (d.cutoff i) ⊆ (d.chart i).target := by
    rintro _ ⟨x,hx,rfl⟩
    exact (d.chart i).map_source (d.cutoff_support i hx)
  obtain ⟨L,hL,hKL,hLT⟩ := exists_compact_between himage (d.chart i).open_target htarget
  exact ⟨⟨L,hL,hLT,hKL⟩⟩

namespace JointSecondarySignedBuffer

def chart (b : JointSecondarySignedBuffer d i) : OpenPartialHomeomorph M D :=
  ((d.chart i).symm.restrOpen (interior b.compactTarget) isOpen_interior).symm

@[simp] theorem chart_apply (b : JointSecondarySignedBuffer d i) (x : M) : b.chart x = d.chart i x := rfl
@[simp] theorem inverse_apply (b : JointSecondarySignedBuffer d i) (y : D) : b.chart.symm y = (d.chart i).symm y := rfl

theorem chart_target (b : JointSecondarySignedBuffer d i) : b.chart.target = interior b.compactTarget := by
  change (d.chart i).target ∩ interior b.compactTarget = interior b.compactTarget
  exact inter_eq_right.mpr (interior_subset.trans b.contained)

theorem source_subset (b : JointSecondarySignedBuffer d i) : b.chart.source ⊆ (d.chart i).source :=
  fun _ hz => hz.1

theorem support_source (b : JointSecondarySignedBuffer d i) : tsupport (d.cutoff i) ⊆ b.chart.source := by
  intro x hx
  exact ⟨d.cutoff_support i hx,b.contains_support ⟨x,hx,rfl⟩⟩

theorem maximal (b : JointSecondarySignedBuffer d i) : b.chart ∈ maximalAtlas IM ∞ M := by
  apply (mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · exact (contMDiffOn_of_mem_maximalAtlas (d.maximal i)).mono b.source_subset
  · exact (contMDiffOn_symm_of_mem_maximalAtlas (d.maximal i)).mono (fun _ hz => hz.1)

theorem adaptation (b : JointSecondarySignedBuffer d i) (x : M) (hx : x ∈ b.chart.source) :
    phase x = b.chart x 0 := d.adaptation i x (b.source_subset hx)

theorem inverse_phase (b : JointSecondarySignedBuffer d i) (y : D) (hy : y ∈ b.chart.target) :
    phase (b.chart.symm y) = y 0 := d.inverse_phase i y hy.1

theorem source_domain (b : JointSecondarySignedBuffer d i) : b.chart.source ⊆ O :=
  b.source_subset.trans (d.source_domain i)

theorem exists_outer (b : JointSecondarySignedBuffer d i) :
    ∃ b' : JointSecondarySignedBuffer d i, b.compactTarget ⊆ interior b'.compactTarget := by
  obtain ⟨L,hL,hBL,hLT⟩ := exists_compact_between b.compact (d.chart i).open_target b.contained
  exact ⟨⟨L,hL,hLT,b.contains_support.trans (interior_subset.trans hBL)⟩,hBL⟩

/-- Actual all-order joint profile on the entire inner target. The passive
parameter may be arbitrary; its derivatives come from the true linear
projection with operator norm one. -/
theorem exists_passive_prefix_profile {Ep V : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : JointSecondarySignedBuffer d i) (U : Set D) (hU : IsOpen U)
    (hBU : b.compactTarget ⊆ U) (f : D → V) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧ ∀ ell, 0 ≤ ell → ell ≤ 1 →
      ∀ n k, k ≤ n → ∀ z : Ep × D, z.2 ∈ b.chart.target →
      ell^k*‖iteratedFDeriv ℝ k (fun w : Ep × D => f w.2) z‖ ≤ C n := by
  let f0 : Z × D → V := fun z => f z.2
  let U0 : Set (Z × D) := univ ×ˢ U
  have hU0 : IsOpen U0 := isOpen_univ.prod hU
  have hf0 : ContDiffOn ℝ ∞ f0 U0 := hf.comp contDiffOn_snd (fun _ hz => hz.2)
  have hcompact : IsCompact ((univ : Set Z) ×ˢ b.compactTarget) := isCompact_univ.prod b.compact
  have hcont (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k f0) (univ ×ˢ b.compactTarget) := by
    intro z hz
    exact ((hf0.contDiffAt (hU0.mem_nhds ⟨mem_univ _,hBU hz.2⟩)).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  have hbound (k : ℕ) : ∃ B : ℝ, ∀ z ∈ (univ : Set Z) ×ˢ b.compactTarget,
      ‖iteratedFDeriv ℝ k f0 z‖ ≤ B := hcompact.exists_bound_of_continuousOn (hcont k)
  choose B hB using hbound
  let C (n : ℕ) := 1+∑ k ∈ Finset.range (n+1), |B k|
  refine ⟨C,fun n => by dsimp only [C]; positivity,?_⟩
  intro ell hell hell1 n k hk z hz
  have hzB : z.2 ∈ b.compactTarget := by rw [b.chart_target] at hz; exact interior_subset hz
  have he := passiveParameter_iteratedFDeriv_norm (0 : Z) f0 U0 hU0 hf0 z
    (show ((0 : Z),z.2) ∈ U0 from ⟨mem_univ _,hBU hzB⟩) k (by simp)
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f0 (0,z.2)‖ :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ B k := hB k (0,z.2) ⟨mem_univ _,hzB⟩
    _ ≤ |B k| := le_abs_self _
    _ ≤ ∑ q ∈ Finset.range (n+1), |B q| :=
      Finset.single_le_sum (fun q _ => abs_nonneg (B q)) (Finset.mem_range.mpr (by omega))
    _ ≤ C n := by dsimp only [C]; linarith

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_signed_buffer
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_passive_prefix_profile
