import Repair.SourceCollarNovParentCutoffs
import GlobalEmbedding.Offline.BufferedSamplingDomains
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual auxiliary parent collars from one original input derivative

The observation parent has raw value at least 1/2 on its support.  The
original raw C1 bound therefore supplies a common ball on which the same
raw value exceeds 1/4.  That ball remains in the original sampling buffer
and pulls back to the original inner set. The primary data are unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {A : BufferedAtlas M E} {B T : ℕ → ℝ} {D : ℕ}

def sourceCollarNovParentRadius (A : BufferedAtlas M E) (B : ℕ → ℝ) : ℝ :=
  min A.buffer (1/(8*(B 1+1)))

theorem sourceCollarNovParentRadius_pos (A : BufferedAtlas M E) (B : ℕ → ℝ) (hB : 0 ≤ B 1) :
    0 < sourceCollarNovParentRadius A B := by
  exact lt_min A.buffer_pos (by positivity)

def sourceCollarNovParentDomain (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) : Set E :=
  bufferedSamplingCoordinates A i ∩
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (R.raw i) ⁻¹' Ioi (1/4 : ℝ))

def sourceCollarNovParentCarrier (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) : Set E :=
  (A.chart i) '' tsupport (sourceCollarNovParent R i)

theorem sourceCollarNovParent_domain_open (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    IsOpen (sourceCollarNovParentDomain R i) :=
  (bufferedSamplingCoordinates_open A i).inter
    ((A.chart i).isOpen_inter_preimage_symm ((R.smooth i).continuous.isOpen_preimage _ isOpen_Ioi))

theorem sourceCollarNovParent_domain_sampling (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    sourceCollarNovParentDomain R i ⊆ bufferedSamplingCoordinates A i := inter_subset_left

theorem sourceCollarNovParent_domain_inner (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    (A.chart i).symm '' sourceCollarNovParentDomain R i ⊆ A.inner i := by
  rintro _ ⟨y,hy,rfl⟩
  apply R.inner_support i
  apply subset_tsupport
  have hh : (1/4 : ℝ) < R.raw i ((A.chart i).symm y) := hy.2.2
  change R.raw i ((A.chart i).symm y) ≠ 0
  linarith

theorem sourceCollarNovParent_carrier_inner (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    sourceCollarNovParentCarrier R i ⊆ bufferedInnerCoordinates A i := by
  rintro _ ⟨x,hx,rfl⟩
  exact bufferedInnerCoordinates_mem A i (sourceCollarNovParent_inner_support R i hx)

theorem sourceCollarNovParent_source (R : TensorRawCutoffPreparation A B T D) (i : Fin A.count) :
    tsupport (sourceCollarNovParent R i) ⊆
      (A.chart i).source ∩ (A.chart i) ⁻¹' sourceCollarNovParentCarrier R i := by
  intro x hx
  exact ⟨A.inner_subset i (sourceCollarNovParent_inner_support R i hx),⟨x,hx,rfl⟩⟩

theorem sourceCollarNovParent_buffer (hA : IsSmoothBufferedAtlas A)
    (R : TensorRawCutoffPreparation A B T D) (hB : 0 ≤ B 1)
    (i : Fin A.count) (c : E) (hc : c ∈ sourceCollarNovParentCarrier R i) :
    ball c (sourceCollarNovParentRadius A B) ⊆ sourceCollarNovParentDomain R i := by
  let r := sourceCollarNovParentRadius A B
  have hr : 0 < r := sourceCollarNovParentRadius_pos A B hB
  have hrA : r ≤ A.buffer := min_le_left _ _
  have hcInner := sourceCollarNovParent_carrier_inner R i hc
  have hSampling : ball c r ⊆ bufferedSamplingCoordinates A i := by
    intro y hy
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hcInner,ball_subset_ball hrA hy⟩⟩
  have hTarget : ball c r ⊆ (A.chart i).target :=
    hSampling.trans (bufferedSampling_subset_target A i)
  have hSmooth : ContDiffOn ℝ ∞ (R.raw i ∘ (A.chart i).symm) (A.chart i).target :=
    ((R.smooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn
  have hDerivative (y : E) (hy : y ∈ ball c r) :
      ‖fderiv ℝ (R.raw i ∘ (A.chart i).symm) y‖ ≤ B 1 := by
    simpa only [norm_iteratedFDeriv_one] using R.own_jets i 1 y (hTarget hy)
  have hcHalf : (1/2 : ℝ) ≤ R.raw i ((A.chart i).symm c) := by
    obtain ⟨x,hx,rfl⟩ := hc
    rw [(A.chart i).left_inv (A.inner_subset i (sourceCollarNovParent_inner_support R i hx))]
    exact sourceCollarNovParent_positive R i hx
  have hBr : B 1*r ≤ 1/8 := by
    have hden : 0 < B 1+1 := by linarith
    have hrCap : r ≤ 1/(8*(B 1+1)) := min_le_right _ _
    calc
      B 1*r ≤ (B 1+1)*r := mul_le_mul_of_nonneg_right (by linarith) hr.le
      _ ≤ (B 1+1)*(1/(8*(B 1+1))) := mul_le_mul_of_nonneg_left hrCap hden.le
      _ = 1/8 := by field_simp
  intro y hy
  have hDifference := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hSmooth.contDiffAt ((A.chart i).open_target.mem_nhds (hTarget hy))).differentiableAt (by simp))
    hDerivative (convex_ball c r) (mem_ball_self hr) hy
  have hnorm : ‖y-c‖ ≤ r := by
    have hh : ‖y-c‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    exact hh.le
  have hSmall : ‖(R.raw i ∘ (A.chart i).symm) y-(R.raw i ∘ (A.chart i).symm) c‖ ≤ 1/8 :=
    hDifference.trans ((mul_le_mul_of_nonneg_left hnorm hB).trans hBr)
  have hLower := (abs_le.mp (show |R.raw i ((A.chart i).symm y)-R.raw i ((A.chart i).symm c)| ≤ 1/8 by
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hSmall)).1
  exact ⟨hSampling hy,hTarget hy,by change (1/4 : ℝ) < R.raw i ((A.chart i).symm y); linarith⟩

theorem sourceCollarNovParent_compact [T2Space M]
    (R : TensorRawCutoffPreparation A B T D)
    (Omega : Fin A.count → Set E) (hCompact : ∀ i, IsCompact (Omega i))
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    IsCompact (tsupport (sourceCollarNovParent R i)) := by
  have hComp := (hCompact i).image_of_continuousOn ((A.chart i).symm.continuousOn.mono (hTarget i))
  apply hComp.of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  have hi := sourceCollarNovParent_inner_support R i hx
  refine ⟨A.chart i x,hSampling i (bufferedInner_subset_sampling A i (bufferedInnerCoordinates_mem A i hi)),?_⟩
  exact (A.chart i).left_inv (A.inner_subset i hi)

theorem sourceCollarNovParent_carrier_compact [T2Space M]
    (R : TensorRawCutoffPreparation A B T D)
    (Omega : Fin A.count → Set E) (hCompact : ∀ i, IsCompact (Omega i))
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) (i : Fin A.count) :
    IsCompact (sourceCollarNovParentCarrier R i) :=
  (sourceCollarNovParent_compact R Omega hCompact hTarget hSampling i).image_of_continuousOn
    ((A.chart i).continuousOn.mono ((sourceCollarNovParent_inner_support R i).trans (A.inner_subset i)))

theorem sourceCollarNovParent_carrier_bound
    (R : TensorRawCutoffPreparation A B T D)
    (Omega : Fin A.count → Set E) (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (bound : ℝ) (hBound : ∀ i y, y ∈ Omega i → ‖y‖ ≤ bound) (i : Fin A.count) :
    sourceCollarNovParentCarrier R i ⊆ closedBall 0 bound := by
  intro y hy
  simpa only [mem_closedBall,dist_zero_right] using hBound i y
    (hSampling i (bufferedInner_subset_sampling A i (sourceCollarNovParent_carrier_inner R i hy)))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_buffer
#print axioms GlobalEmbedding.Continuation.sourceCollarNovParent_carrier_compact
