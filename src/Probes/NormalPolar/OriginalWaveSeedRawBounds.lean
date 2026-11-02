import NormalPolar.OriginalWaveSeedGeometry

/-! Bounds for literal original-wave fields on genuinely constructed nested
compact targets. Every constant is chosen before the derivative scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Z × D

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

theorem spatial_inverse_original (b : OriginalWaveSeedBuffer d i) (z : X) :
    b.spatialChart.symm z.2 = ((d.chart i).symm z).2 := by
  rw [b.spatialChart_inverse,b.inverse_apply]
  exact congrArg (fun t : X => ((d.chart i).symm t).2)
    (Prod.ext (Subsingleton.elim _ _) rfl)

theorem compact_in_outer (b b' : OriginalWaveSeedBuffer d i)
    (h : b.compactTarget ⊆ interior b'.compactTarget) :
    b.compactTarget ⊆ (univ : Set Z) ×ˢ b'.spatialChart.target := by
  intro z hz
  refine ⟨mem_univ _,(b'.spatialChart_target z.2).mpr ?_⟩
  rw [b'.chart_target]
  have he : ((default : Z),z.2) = z := Prod.ext (Subsingleton.elim _ _) rfl
  rw [he]
  exact h hz

/-- Finite-prefix constants on the whole inner target, chosen before scale.
The surrounding open set need only contain the actual compact buffer. -/
theorem exists_prefix_profile {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (b : OriginalWaveSeedBuffer d i) (O : Set X) (hO : IsOpen O)
    (hBO : b.compactTarget ⊆ O) (f : X → Y) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧ ∀ ell : ℝ, 0 ≤ ell → ell ≤ 1 →
      ∀ n k, k ≤ n → ∀ z ∈ b.chart.target,
        ell^k * ‖iteratedFDeriv ℝ k f z‖ ≤ C n := by
  have hc (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k f) b.compactTarget := by
    intro z hz
    exact ((hf.contDiffAt (hO.mem_nhds (hBO hz))).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  have hb (k : ℕ) : ∃ C : ℝ, ∀ z ∈ b.compactTarget,
      ‖iteratedFDeriv ℝ k f z‖ ≤ C := b.compact.exists_bound_of_continuousOn (hc k)
  choose C hC using hb
  let B (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (|C k|+1)
  have hCB (n k : ℕ) (hk : k ≤ n) : |C k|+1 ≤ B n := by
    change |C k|+1 ≤ ∑ j ∈ Finset.range (n+1), (|C j|+1)
    exact Finset.single_le_sum (f := fun j : ℕ => |C j|+1)
      (fun (j : ℕ) (_ : j ∈ Finset.range (n+1)) => by positivity)
      (show k ∈ Finset.range (n+1) from Finset.mem_range.mpr (by omega))
  refine ⟨B,fun n => lt_of_lt_of_le (by positivity : 0 < |C 0|+1) (hCB n 0 (by omega)),?_⟩
  intro ell hell hell1 n k hk z hz
  have hzL : z ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz
  calc
    ell^k * ‖iteratedFDeriv ℝ k f z‖ ≤ 1 * ‖iteratedFDeriv ℝ k f z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
    _ ≤ C k := by simpa only [one_mul] using hC k z hzL
    _ ≤ |C k|+1 := (le_abs_self _).trans (by linarith)
    _ ≤ B n := hCB n k hk

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.exists_prefix_profile
