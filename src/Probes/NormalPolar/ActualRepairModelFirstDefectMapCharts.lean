import NormalPolar.ActualRepairModelFirstDefectMapNative
import Smoothing.ParameterRound2MeanRawNative

/-! The original inverse parameter chart is differentiated before measuring
all joint jets of the complete first increment. The sample is its actual
image, and the local differentiation domain is an open restriction of the
original domain. No compact parameter direction is discarded. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actualRepairModelFirstDefect_map_norms_after_parameter_charts
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (U : Ep × M → V) (j : ℕ) (tau ell delta K : ℝ)
    (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hdelta : 0 ≤ delta) (hK : 0 ≤ K) (TP : ℕ → ℝ) (hTP : ∀ k, 0 ≤ TP k)
    (Omega : Fin A.count × Fin count → Set X) (hOmega : ∀ i, IsOpen (Omega i))
    (hSample : ∀ i, parameterRound2_meanParameterMap (m := m) (B i.2) ''
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) ⊆ Omega i)
    (hU : ∀ i, ContDiffOn ℝ ∞ (fun z : X => U (z.1,(A.chart i.1).symm z.2)) (Omega i))
    (hjet : ∀ i, ∀ k ≤ j+2, ∀ y ∈ parameterRound2_meanParameterMap (m := m) (B i.2) ''
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i),
      tau^k*‖iteratedFDeriv ℝ k (fun z : X => U (z.1,(A.chart i.1).symm z.2)) y‖ ≤ K*delta*tau)
    (hParam : ∀ i : Fin A.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j+2 →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    let coordinates := incrementsOriginalMapCoordinates A B U
    let C := actualRepairModelFirstDefectMapNormCost m d N j (actualFastChartTransferPrefix TP (j+2)*K)
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) ∧
    (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasCj 2 coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta/tau) := by
  intro coordinates C
  let a := parameterTensorModelEquiv (m+1) d
  let phi := fun i : Fin A.count × Fin count => parameterRound2_meanParameterMap (m := m) (B i.2)
  let O := fun i : Fin A.count × Fin count => (B i.2).target ×ˢ (A.chart i.1).target
  let S0 := fun i => a ⁻¹' S i
  let U0 := fun i : Fin A.count × Fin count => fun z : X => U (z.1,(A.chart i.1).symm z.2)
  let CP := actualFastChartTransferPrefix TP (j+2)
  have hCP : 0 ≤ CP := actualFastChartTransferPrefix_nonneg TP hTP (j+2)
  have hO (i) : IsOpen (O i) := (B i.2).open_target.prod (A.chart i.1).open_target
  have hSO0 : ∀ i, S0 i ⊆ O i := by
    intro i z hz
    have hh := hSO i hz
    have he : (incrementsOriginalParameterPoint (a z),incrementsOriginalSourcePoint (a z)) = z := a.symm_apply_apply z
    rw [← he]
    exact ⟨hh.2,hh.1⟩
  have hphi (i) : ContDiffOn ℝ ∞ (phi i) (O i) :=
    (((contMDiffOn_symm_of_mem_maximalAtlas (hB i.2)).contDiffOn).comp
      contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd
  let V0 := fun i => O i ∩ phi i ⁻¹' Omega i
  have hV (i) : IsOpen (V0 i) :=
    (hphi i).continuousOn.isOpen_inter_preimage (hO i) (hOmega i)
  have hSV : ∀ i, S0 i ⊆ V0 i := fun i z hz => ⟨hSO0 i hz,hSample i ⟨z,hz,rfl⟩⟩
  have hsm (i) : ContDiffOn ℝ ∞ (actualRepairModelFirstDefectObservedMap A B U i) (V0 i) :=
    (hU i).comp ((hphi i).mono inter_subset_left) (fun _ hz => hz.2)
  have hjets : ∀ i, ∀ k ≤ j+2, ∀ z : X, a z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualRepairModelFirstDefectObservedMap A B U i) z‖ ≤ (CP*K)*delta*tau := by
    intro i k hk z hz
    have ht := actual_fast_joint_chart_transfer TP hTP k (phi i) (U0 i) (V0 i) (Omega i)
      (hV i) (hOmega i) ((hphi i).mono inter_subset_left) (hU i)
      (fun _ hy => hy.2) z (hSV i hz) tau ell (K*delta*tau) htau htaul
      (fun r hr => hjet i r (hr.trans hk) (phi i z) ⟨z,hz,rfl⟩)
      (fun r hr hrk => hParam i z hz r hr (hrk.trans hk))
    exact (ht.trans (mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix TP hTP hk) (by positivity))).trans_eq (by ring)
  exact actualRepairModelFirstDefect_map_norms_from_native A B S V0 hV
    (fun _ _ hz => hz.1) hSV U j tau delta (CP*K) htau (htaul.trans hell1)
    hdelta (mul_nonneg hCP hK) hsm hjets

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_map_norms_after_parameter_charts
