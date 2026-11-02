import NormalPolar.ActualRepairGlobalParameter

/-!
# Fixed slow parameter profiles of the constructed global chart input

The global cutoff is fixed before the later oscillation scales.  Actual
compact parameter samples therefore give one finite profile for every order,
uniform over all of the original charts.  The bound is then valid for every
slow scale in [0,1], without selecting a different function at each order or
scale.  The identity on the original repair ball remains unchanged.
-/

noncomputable section
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar

variable {d : ℕ} {ι P : Type*} [Fintype ι] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem actualRepairGlobalParameter_fixed_profiles
    (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (Q : ι → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ ell : ℝ, 0 ≤ ell → ell ≤ 1 → ∀ k i z, z ∈ Q i →
        ell ^ k * ‖iteratedFDeriv ℝ k
          (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) z‖ ≤ C k := by
  have hs (i : ι) : ContDiffOn ℝ ∞
      (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) (B.chart i).target :=
    ((actualRepairGlobalParameter_smooth B hB b p₀ hp₀).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (hB i))).contDiffOn
  have hbound (k : ℕ) (i : ι) : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Q i,
      ‖iteratedFDeriv ℝ k
        (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) z‖ ≤ C := by
    have hc := (ContinuousOn.continuousOn_iteratedFDeriv (hs i) (B.chart i).open_target
      (by simp : (k : ℕ∞ω) ≤ ∞)).mono
      (hTarget i)
    obtain ⟨C, hC, hnorm⟩ := ((hQ i).image_of_continuousOn hc).isBounded.exists_pos_norm_le
    exact ⟨C, hC, fun z hz => hnorm _ ⟨z, hz, rfl⟩⟩
  choose c hc hcBound using hbound
  refine ⟨fun k => ∑ i, c k i, fun k => Finset.sum_nonneg (fun i _ => (hc k i).le), ?_⟩
  intro ell hell hell1 k i z hz
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ k
        (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) z‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)
    _ ≤ c k i := by simpa only [one_mul] using hcBound k i z hz
    _ ≤ ∑ a, c k a := Finset.single_le_sum (fun a _ => (hc k a).le) (Finset.mem_univ i)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_fixed_profiles
