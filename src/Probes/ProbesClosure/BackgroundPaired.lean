import ProbesClosure.BackgroundOriginalNorms
import ProbesClosure.BackgroundFamilySharp
import NormalPolar.ActualRepairSamplingAtlas

/-! The actual sharp background, now on the original paired ball and in the
paper scales. The original product samples provide every spatial support
observation. All responses and original norms are attached to the literal
scaled background, retaining its linear dependence on the parameter norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N p r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin p)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Params" => Fin p → ℝ
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The product SUP set contains every spatial sample at any one parameter
sample. This uses the literal original coordinate equivalence. -/
theorem probes_background_original_samples_cover
    (A : BufferedAtlas M D) (Omega : Fin A.count → Set D)
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (B : BufferedAtlas P Ep) (Q : Fin B.count → Set Ep)
    (hQTarget : ∀ i, Q i ⊆ (B.chart i).target)
    (b : Fin B.count) (y₀ : Ep) (hy₀ : y₀ ∈ Q b) :
    ∀ i x, x ∈ (actualRepairSamplingAtlas A Omega).support i →
      ∃ y ∈ (parameterTensorModelEquiv (m+1) p) ⁻¹'
        incrementsOriginalEvaluation A B.chart Omega Q univ (i,b),
        y.2 = A.chart i x := by
  intro i x hx
  have hSample : A.chart i x ∈ Omega i := by
    rw [← actualRepairSamplingAtlas_coordinate_support A Omega hTarget i]
    exact ⟨x,hx,rfl⟩
  let y : Ep × D := (y₀,A.chart i x)
  have hs := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) p).symm_apply_apply y)
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) p).symm_apply_apply y)
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) p y) = y.2 at hs
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) p y) = y.1 at hp
  refine ⟨y,?_,rfl⟩
  refine ⟨?_,?_,?_,mem_univ _⟩
  · change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) p y) ∈ (A.chart i).target ∧
      incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) p y) ∈ (B.chart b).target
    rw [hs,hp]
    exact ⟨hTarget i hSample,hQTarget b hy₀⟩
  · change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) p y) ∈ Omega i
    rw [hs]
    exact hSample
  · change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) p y) ∈ Q b
    rw [hp]
    exact hy₀

/-- Chart jointness, both original norms, and the two native remainders
consumed by the complete four-response sum theorem. No loss of radius or
replacement of the background map occurs in the conversion. -/
theorem probes_background_paired_responses
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (B : BufferedAtlas P Ep)
    (Samples : Fin A.count × Fin B.count → Set (Fin (m+1+p) → ℝ))
    (b : Fin B.count)
    (hSamples : ∀ i x, x ∈ A.support i →
      ∃ y ∈ (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b), y.2 = A.chart i x)
    (t C : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (wave : Params → M → V)
    (hSharp : ProbesBackgroundNativeSharp A B Samples b (t^((6:ℝ)/5)) C wave)
    (label : (Fin r × Bool) ↪ Fin p) :
    let radius := actualRepairParameterRadius (tensorChartFamilyOfAtlas B)
    let out := fun (u : ProbeParameters r) x => t^(10:ℕ) • wave (probeParameterEmbedding label u) x
    (∀ i, ContDiffOn ℝ ∞ (fun z : ProbeParameters r × D => out z.1 ((A.chart i).symm z.2))
      (Metric.ball 0 radius ×ˢ (A.chart i).target)) ∧
    (∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ direction : ProbeParameters r,
      probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => out v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*(C*‖u‖)*t^(10:ℕ)*‖direction‖) ∧
      probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => out v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*(C*‖u‖)*t^((44:ℝ)/5)*‖direction‖)) ∧
    ∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ i x, x ∈ A.support i → ∀ direction,
      ‖fderiv ℝ (fun v => out v x) u direction‖ ≤
        t^((56:ℝ)/5)*(C*‖u‖)*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (out v ∘ (A.chart i).symm)) (A.chart i x)) u direction‖ ≤
        t^((44:ℝ)/5)*(C*‖u‖)*‖direction‖ := by
  intro radius out
  have hNorm := probes_background_original_parameter_norms A hA
    (fun i => (parameterTensorModelEquiv (m+1) p) ⁻¹' Samples (i,b)) hSamples
    radius (t^((6:ℝ)/5)) (t^(10:ℕ)) C (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) (pow_nonneg ht.le _) hC wave hSharp label
  refine ⟨hNorm.1,?_,?_⟩
  · intro u hu direction
    have hn := hNorm.2.2 u hu direction
    refine ⟨hn.1,?_⟩
    simpa only [mul_div_assoc,probe_delta_div_tau_eq_sigma t ht] using hn.2
  · intro u hu i x hx direction
    have hEmbed : probeParameterEmbedding label u ∈ Metric.ball (0 : Params) radius := by
      simpa only [Metric.mem_ball,dist_zero_right,probeParameterEmbedding_norm] using hu
    obtain ⟨y,hy,heq⟩ := hSamples i x hx
    have hn := (hSharp i).2 (probeParameterEmbedding label u) hEmbed y hy
    rw [heq] at hn
    let f := fun v z => wave v ((A.chart i).symm z)
    have hb := globalWave_background_native_paired_paper_scales label f u (A.chart i x) t C ht
      hn.1 hn.2.1 hn.2.2
    have hV : ‖fderiv ℝ (fun v => out v x) u‖ ≤ (C*t^((56:ℝ)/5))*‖u‖ := by
      simpa only [f,out,(A.chart i).left_inv (hA.support_subset i hx)] using hb.1.2
    have hH : ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (out v ∘ (A.chart i).symm))
        (A.chart i x)) u‖ ≤ (C*t^((44:ℝ)/5))*‖u‖ := hb.2.2.2
    constructor
    · exact ((fderiv ℝ (fun v => out v x) u).le_opNorm direction).trans
        ((mul_le_mul_of_nonneg_right hV (norm_nonneg direction)).trans_eq (by ring))
    · exact ((fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (out v ∘ (A.chart i).symm))
        (A.chart i x)) u).le_opNorm direction).trans
        ((mul_le_mul_of_nonneg_right hH (norm_nonneg direction)).trans_eq (by ring))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_background_original_samples_cover
#print axioms GlobalEmbedding.Continuation.probes_background_paired_responses
