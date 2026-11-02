import Smoothing.Round3OuterStageFreeNormal
import Smoothing.Round3OuterNormalCoverGeometry
import Smoothing.Round3OuterOriginalCoverNorm

/-! The SAME actual SF supplies one intrinsic physical normal with all of
its ORIGINAL weighted norms.  Its local formulas are the actual normalized
two-frame projections.  Original samples may meet different reference
pieces and different physical parameter charts.  No new-normal estimate is
an input; no chart-count factor is added; constants precede the current stage.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Y" => Fin (m+1+d) → ℝ
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_exists_uniform_actual_stage_intrinsic_normal_original_norms
    (BS0 TS0 BP0 TP0 T Tobs Mv : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (hTobs : ∀ j, 0 ≤ Tobs j) (hMv : ∀ j, 0 ≤ Mv j)
    (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius) (r : ℕ)
    (budget cF cT mu : ℝ) (hbudget : 0 ≤ budget)
    (hcF : 0 < cF) (hcT : 0 < cT) (hmu : 0 < mu) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket),
    let hF := fun p => parameterRound2_native_source_slice_contMDiff
      (round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
        hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage) p
    ∀ (psi : P → M → ℝ) (vref : P × M → Ey) (A : Type*)
      (Orig Samples : Fin Data.atlas.count × Fin Data.parameterCount → Set Y),
    (∀ i, IsOpen (Orig i)) →
    ∀ cover : Round3OriginalNormalCoverGeometry Data hF psi vref A Orig Samples cF cT mu,
    (∀ i a k, 1 ≤ k → ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (round3OriginalAdaptedTransition Data.atlas
        (cover.host i a).1 (cover.chart i a)) (cover.forward i a y)‖ ≤ T k) →
    (∀ i a k, 1 ≤ k → ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (cover.forward i a) y‖ ≤ Tobs k) →
    (∀ i a k, ∀ y ∈ Samples i ∩ cover.original i a,
      ‖iteratedFDeriv ℝ k (round3NormalChartReference Data (cover.host i a)
        (cover.chart i a) vref) (cover.forward i a y)‖ ≤ Mv k) →
    let normal := parameterRound2_intrinsicUnitFreeNormalField (fun p x => Data.F (p,x)) hF psi vref
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart normal i)
      (⋃ a, cover.original i a)) ∧
    (∀ i a z, z ∈ cover.native i a →
      ‖normal ((Data.parameterChart (cover.host i a).2).symm z.1,(cover.chart i a z.1).symm z.2)‖ = 1) ∧
    (∀ z, normal z ∈ parameterRound2_intrinsicPhaseFreeSpace
      (fun x => Data.F (z.1,x)) (hF z.1) (psi z.1) z.2) ∧
    ∀ j, paperAtlasWeighted 0 j stage.ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart normal) Orig Samples ≠ ⊤ ∧
      (paperAtlasWeighted 0 j stage.ell
        (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart normal) Orig Samples).toReal ≤ C j := by
  let Mprefix : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j+1), Mv l
  have hMp : ∀ j, 0 ≤ Mprefix j := fun j => Finset.sum_nonneg (fun l _ => hMv l)
  obtain ⟨Cn,hCn,hNative⟩ := round3_exists_uniform_actual_stage_free_normal_profiles
    (m := m) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 T Mprefix hBS0 hTS0 hBP0 hTP0 hT hMp Ds Dp radius hradius r
    budget cF cT mu hbudget hcF hcT hmu
  let cy := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let C : ℕ → ℝ := fun j => (j+1)*(‖cy‖*actualFastChartTransferPrefix Tobs j*Cn j)
  have hC : ∀ j, 0 ≤ C j := fun j => mul_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (actualFastChartTransferPrefix_nonneg Tobs hTobs j)) (hCn j))
  refine ⟨C,hC,?_⟩
  intro Data reference givenPacket stage hF psi vref A Orig Samples hOrig cover hChartJets hObserverJets hReferenceJets normal
  let g := fun i a (z : X) => normal
    ((Data.parameterChart (cover.host i a).2).symm z.1,(cover.chart i a z.1).symm z.2)
  have hell1 : stage.ell ≤ 1 := stage.ell_le_t.trans stage.t_le_one
  have hPhysical (i) (a : A) := round3_actual_normal_parameter_pullback_germs
    (fun p x => Data.F (p,x)) hF psi vref (Data.parameterChart (cover.host i a).2).symm
    (cover.chart i a) (cover.chart_smooth i a) (cover.native i a) (cover.native_open i a)
    (cover.chart_target i a) (cover.phase_smooth i a) (cover.phase_adapted i a)
  have hActual (j : ℕ) (i) (a : A) := hNative Data reference givenPacket stage j
    (cover.host i a) (cover.chart i a) (cover.chart_smooth i a)
    (cover.native i a) (cover.forward i a '' (Samples i ∩ cover.original i a))
    (round3NormalChartReference Data (cover.host i a) (cover.chart i a) vref)
    (cover.native_open i a)
    (by rintro _ ⟨y,hy,rfl⟩; exact cover.forward_maps i a hy.2)
    (cover.reference_smooth i a) (cover.transition_smooth i a) (cover.source i a) (cover.parameter i a)
    (cover.chart_target i a)
    (by rintro _ ⟨y,hy,rfl⟩; exact cover.sample i a y hy)
    (by intro l hl _; rintro _ ⟨y,hy,rfl⟩; exact hChartJets i a l hl y hy)
    (by
      intro k hk
      rintro _ ⟨y,hy,rfl⟩
      have hb := hReferenceJets i a k y hy
      have hpre : Mv k ≤ Mprefix j := Finset.single_le_sum
        (fun l _ => hMv l) (by simp; omega)
      exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ stage.ell_pos.le hell1) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hb)).trans hpre)
    (cover.first i a) (cover.transverse i a) (cover.reserve i a)
  have hLocal (j : ℕ) (i) (a : A) : ContDiffOn ℝ ∞ (g i a) (cover.native i a) ∧
      ∀ k ≤ j, ∀ y ∈ Samples i ∩ cover.original i a,
        stage.ell^k*‖iteratedFDeriv ℝ k (g i a) (cover.forward i a y)‖ ≤ Cn j := by
    refine ⟨(hPhysical i a).1.mp (hActual j i a).2.1,?_⟩
    intro k hk y hy
    have hb := (hActual j i a).2.2.2 k hk _ ⟨y,hy,rfl⟩
    have heq := congrArg (fun v => stage.ell^k*‖v‖)
      ((hPhysical i a).2 k _ (cover.forward_maps i a hy.2))
    exact heq.symm.le.trans hb
  have hEq (i) (a : A) : EqOn (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart normal i)
      ((EuclideanSpace.equiv (Fin N) ℝ) ∘ g i a ∘ cover.forward i a) (cover.original i a) := by
    intro y hy
    exact congrArg (fun z => (EuclideanSpace.equiv (Fin N) ℝ) (normal z)) (cover.same_point i a y hy).symm
  have hNorm (j : ℕ) := round3_original_weighted_norm_from_native_open_cover j stage.ell (Cn j)
    stage.ell_pos hell1 (hCn j) Tobs hTobs
    (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart normal) Orig Samples hOrig
    cover.original cover.native g cover.forward cover.original_open cover.native_open cover.original_subset
    cover.covers (fun i a => (hLocal j i a).1) cover.forward_smooth cover.forward_maps hEq
    (fun i a => (hLocal j i a).2)
    (by
      intro i a k hk _ y hy
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ stage.ell_pos.le hell1) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hObserverJets i a k hk y hy))
  refine ⟨(hNorm 0).1,?_,?_,fun j => (hNorm j).2⟩
  · intro i a z hz
    have heq := round3_actual_normal_parameter_pullback_eq_intrinsic
      (fun p x => Data.F (p,x)) hF psi vref (Data.parameterChart (cover.host i a).2).symm
      (cover.chart i a) (cover.chart_smooth i a) (cover.native i a) (cover.native_open i a)
      (cover.chart_target i a) (cover.phase_smooth i a) (cover.phase_adapted i a) hz
    obtain ⟨nv,hnv,hunit,_⟩ := (hActual 0 i a).2.2.1 z hz
    have hnvPhysical : (nv : Ey) = normal
        ((Data.parameterChart (cover.host i a).2).symm z.1,(cover.chart i a z.1).symm z.2) := hnv.trans heq
    rw [← hnvPhysical]
    exact hunit
  · intro z
    exact round3_intrinsic_unit_normal_mem_phase_free (fun p x => Data.F (p,x)) hF psi vref z

#print axioms round3_exists_uniform_actual_stage_intrinsic_normal_original_norms
end GlobalEmbedding.Continuation
