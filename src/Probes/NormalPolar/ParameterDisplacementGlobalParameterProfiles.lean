import NormalPolar.ActualRepairGlobalParameterProfiles
import Probes.ActualSourceRestriction

/-! The actual global chart input has fixed full joint slow profiles after
adjoining the spatial variable. The spatial projection is a contraction, so
no source-coordinate cost or changed parameter ball is introduced. -/

noncomputable section
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.NormalPolar

theorem norm_iteratedFDeriv_parameter_only_le
    {Ep Es V : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Ep → V) (O : Set Ep) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (z : Ep × Es) (hz : z.1 ∈ O) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y : Ep × Es => f y.1) z‖ ≤ ‖iteratedFDeriv ℝ j f z.1‖ := by
  let L : Ep × Es →L[ℝ] Ep := ContinuousLinearMap.fst ℝ Ep Es
  have hU : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hU.uniqueDiffOn hz (i := j) (by simp)
  rw [iteratedFDerivWithin_of_isOpen j hU hz,
    iteratedFDerivWithin_of_isOpen j hO (show L z ∈ O from hz)] at he
  change ‖iteratedFDeriv ℝ j (f ∘ L) z‖ ≤ ‖iteratedFDeriv ℝ j f (L z)‖
  rw [he]
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro y
    change ‖y.1‖ ≤ 1*‖y‖
    simpa only [one_mul] using norm_fst_le y
  apply ((iteratedFDeriv ℝ j f (L z)).norm_compContinuousLinearMap_le _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

variable {d : ℕ} {ι P Es : Type*} [Fintype ι] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem actualRepairGlobalParameter_joint_fixed_profiles
    (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Q : ι → Set Ep) (hQ : ∀ i, IsCompact (Q i))
    (hTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (b : ι) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      (∀ i, ContDiffOn ℝ ∞
        (fun z : Ep × Es => actualRepairGlobalParameter B b p₀ ((B.chart i).symm z.1))
        (Prod.fst ⁻¹' (B.chart i).target)) ∧
      ∀ j ell, 0 ≤ ell → ell ≤ 1 → ∀ k, k ≤ j → ∀ i z, z.1 ∈ Q i →
        ell^k*‖iteratedFDeriv ℝ k
          (fun y : Ep × Es => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y.1)) z‖ ≤ K j := by
  obtain ⟨C,hC,hbound⟩ := actualRepairGlobalParameter_fixed_profiles B hB Q hQ hTarget b p₀ hp₀
  let K : ℕ → ℝ := fun j => ∑ k ∈ Finset.range (j+1), C k
  have hs (i : ι) : ContDiffOn ℝ ∞
      (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) (B.chart i).target :=
    ((actualRepairGlobalParameter_smooth B hB b p₀ hp₀).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas (hB i))).contDiffOn
  refine ⟨K,(fun j => Finset.sum_nonneg (fun k _ => hC k)),?_,?_⟩
  · intro i
    exact (hs i).comp contDiff_fst.contDiffOn (fun z hz => hz)
  · intro j ell hell hell1 k hk i z hz
    have hn := norm_iteratedFDeriv_parameter_only_le
      (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y))
      (B.chart i).target (B.chart i).open_target (hs i) z (hTarget i hz) k
    calc
      _ ≤ ell^k*‖iteratedFDeriv ℝ k
          (fun y => actualRepairGlobalParameter B b p₀ ((B.chart i).symm y)) z.1‖ :=
        mul_le_mul_of_nonneg_left hn (pow_nonneg hell k)
      _ ≤ C k := hbound ell hell hell1 k i z.1 hz
      _ ≤ K j := Finset.single_le_sum (fun q _ => hC q) (by simpa using hk)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.norm_iteratedFDeriv_parameter_only_le
#print axioms GlobalEmbedding.NormalPolar.actualRepairGlobalParameter_joint_fixed_profiles
