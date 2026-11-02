import NormalPolar.OriginalWaveSeedObserver

/-! Uniform actual transition and phase budgets on the original compact
atlas supports. The active domains and samples are the literal ones already
constructed from each original wave piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

theorem exists_compact_native_prefix
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S O : Set X) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O)
    (f : X → Y) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ n k, k ≤ n → ∀ z ∈ S, ‖iteratedFDeriv ℝ k f z‖ ≤ C n := by
  have hc (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k f) S := by
    intro z hz
    exact ((hf.contDiffAt (hO.mem_nhds (hSO hz))).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  choose B hB using fun k => hS.exists_bound_of_continuousOn (hc k)
  let C (n : ℕ) : ℝ := ∑ k ∈ Finset.range (n+1), (|B k|+1)
  have hBC (n k : ℕ) (hk : k ≤ n) : |B k|+1 ≤ C n :=
    Finset.single_le_sum (f := fun k : ℕ => |B k|+1)
      (fun _ _ => by positivity) (show k ∈ Finset.range (n+1) by simp; omega)
  refine ⟨C,fun n => lt_of_lt_of_le (by positivity : 0 < |B 0|+1) (hBC n 0 (by omega)),?_⟩
  intro n k hk z hz
  exact (hB k z hz).trans ((le_abs_self _).trans
    ((show |B k| ≤ |B k|+1 by linarith).trans (hBC n k hk)))

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedFamily

/-- Actual all-order observation constants, uniformly over every original
atlas chart and all subordinate pieces. Only the original compactness and
maximal-atlas hypotheses occur before this existential. -/
theorem exists_observation_bounds (family : OriginalWaveSeedFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ h, IsCompact (A.support h)) :
    ∃ T P : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < P k) ∧
      ∀ (h : Fin A.count) (l : Fin r) (s : Fin (family.refinement l).count)
        (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ (k : ℕ) (z : X),
        z ∈ (univ : Set Z) ×ˢ ((A.chart h) '' A.support h) →
        (z.1,(A.chart h).symm z.2) ∈ tsupport ((family.refinement l).cutoff s) →
        (ell^(k-1) * ‖iteratedFDeriv ℝ k
          ((family.inner l s).chart ∘ (fun y : X => (y.1,(A.chart h).symm y.2))) z‖ ≤ T k) ∧
        (∀ j, k < j → ell^k * ‖iteratedFDeriv ℝ (k+1)
          (fun y : X => weight l * (waves l).phase ((A.chart h).symm y.2)) z‖ ≤ P j) := by
  let Idx := (h : Fin A.count) × (l : Fin r) × Fin (family.refinement l).count
  let S (idx : Idx) : Set X := OriginalWaveSeedBuffer.observerActiveSample
    (A.chart idx.1) (A.support idx.1) (family.refinement idx.2.1) idx.2.2
  let O (idx : Idx) : Set X := (family.inner idx.2.1 idx.2.2).observerDomain (A.chart idx.1)
  have hS (idx : Idx) : IsCompact (S idx) :=
    (family.inner idx.2.1 idx.2.2).observer_sample_compact _ _ (hcompact _) (hA.support_subset _)
  have hO (idx : Idx) : IsOpen (O idx) :=
    (family.inner idx.2.1 idx.2.2).observerDomain_open _
  have hSO (idx : Idx) : S idx ⊆ O idx :=
    (family.inner idx.2.1 idx.2.2).observer_sample_domain _ _ (hA.support_subset _)
  have ht (idx : Idx) := exists_compact_native_prefix (S idx) (O idx) (hS idx) (hO idx) (hSO idx)
    _ ((family.inner idx.2.1 idx.2.2).observer_transition_smooth _ (hA.chart_mem _))
  have hp (idx : Idx) := exists_compact_native_prefix (S idx) (O idx) (hS idx) (hO idx) (hSO idx)
    _ ((family.inner idx.2.1 idx.2.2).observer_phase_smooth _ (hA.chart_mem _))
  choose CT hCT bT using ht
  choose CP hCP bP using hp
  choose BT hBT using fun k => Finite.exists_le (fun idx : Idx => CT idx k)
  choose BP hBP using fun k => Finite.exists_le (fun idx : Idx => CP idx k)
  refine ⟨fun k => |BT k|+1,fun k => |BP k|+1,fun k => ⟨by positivity,by positivity⟩,?_⟩
  intro h l s ell hell hell1 k z hz hactive
  have hzS : z ∈ S ⟨h,l,s⟩ := (family.inner l s).observer_active_mem_sample
    (A.chart h) (A.support h) (hA.support_subset h) z hz hactive
  constructor
  · calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ k
          ((family.inner l s).chart ∘ (fun y : X => (y.1,(A.chart h).symm y.2))) z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
      _ ≤ CT ⟨h,l,s⟩ k := by simpa only [one_mul] using bT ⟨h,l,s⟩ k k le_rfl z hzS
      _ ≤ BT k := hBT k ⟨h,l,s⟩
      _ ≤ |BT k|+1 := (le_abs_self _).trans (by linarith)
  · intro j hkj
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ (k+1)
          (fun y : X => weight l * (waves l).phase ((A.chart h).symm y.2)) z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
      _ ≤ CP ⟨h,l,s⟩ j := by simpa only [one_mul] using bP ⟨h,l,s⟩ j (k+1) (by omega) z hzS
      _ ≤ BP j := hBP j ⟨h,l,s⟩
      _ ≤ |BP j|+1 := (le_abs_self _).trans (by linarith)

end OriginalWaveSeedFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedFamily.exists_observation_bounds

