import NormalPolar.OriginalWaveSeedPhysical

/-! Monotone budgets for the literal finite original-wave pieces. Enlarging
a bound changes no chart, sample, cutoff, normal, phase or support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

def enlarge_raw_profiles (b b' : OriginalWaveSeedBuffer d i)
    {n j : ℕ} {ell Mg Bchi Bnu Mg' Bchi' Bnu' : ℝ}
    (raw : ActualPrescribedSpatialRawProfiles (fun _ : Z => F) (fun _ => hF)
      (fun _ => b'.spatialChart.symm) (d.cutoffCoordinates i)
      (fun _ x => w.normal (b'.spatialChart.symm x))
      b.chart univ (tsupport (d.cutoff i)) n j ell Mg Bchi Bnu)
    (hg : Mg ≤ Mg') (hc : Bchi ≤ Bchi') (hn : Bnu ≤ Bnu') :
    ActualPrescribedSpatialRawProfiles (fun _ : Z => F) (fun _ => hF)
      (fun _ => b'.spatialChart.symm) (d.cutoffCoordinates i)
      (fun _ x => w.normal (b'.spatialChart.symm x))
      b.chart univ (tsupport (d.cutoff i)) n j ell Mg' Bchi' Bnu' :=
  { raw with
    A_jets := fun k hk z hz => (raw.A_jets k hk z hz).trans hg
    B_jets := fun k hk z hz => (raw.B_jets k hk z hz).trans hg
    G_jets := fun k hk z hz => (raw.G_jets k hk z hz).trans hg
    J_jets := fun k hk z hz => (raw.J_jets k hk z hz).trans hg
    T_jets := fun k hk z hz => (raw.T_jets k hk z hz).trans hg
    BR_jets := fun k hk z hz => (raw.BR_jets k hk z hz).trans hg
    cutoff_jets := fun k hk z hz => (raw.cutoff_jets k hk z hz).trans hc
    normal_jets := fun k hk z hz => (raw.normal_jets k hk z hz).trans hn }

end OriginalWaveSeedBuffer

/-- The finite family need not be nonempty. This single pre-scale constant
bounds every original label and each of its actual subordinate pieces. -/
theorem originalWave_finite_budget {r : ℕ} (count : Fin r → ℕ)
    (C : (l : Fin r) → Fin (count l) → ℝ) (hC : ∀ l s, 0 ≤ C l s) :
    0 < 1 + ∑ l, ∑ s, C l s ∧
      ∀ l s, C l s ≤ 1 + ∑ l, ∑ s, C l s := by
  have hsum : 0 ≤ ∑ l, ∑ s, C l s :=
    Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun s _ => hC l s))
  refine ⟨by linarith,?_⟩
  intro l s
  have hs : C l s ≤ ∑ t, C l t :=
    Finset.single_le_sum (f := C l) (fun t _ => hC l t) (Finset.mem_univ s)
  have hl : (∑ t, C l t) ≤ ∑ j, ∑ t, C j t :=
    Finset.single_le_sum (f := fun j => ∑ t, C j t)
      (fun j _ => Finset.sum_nonneg (fun t _ => hC j t)) (Finset.mem_univ l)
  linarith

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.enlarge_raw_profiles
#print axioms GlobalEmbedding.NormalPolar.originalWave_finite_budget

