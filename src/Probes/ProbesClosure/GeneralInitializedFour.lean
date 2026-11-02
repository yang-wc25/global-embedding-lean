import ProbesClosure.GeneralPhysicalNorms
import ProbesClosure.GeneralInitializedResponses
import ProbesClosure.GeneralFourFields

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N r : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin (Fintype.card (Fin r × Bool)))
private local instance physicalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance physicalHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance physicalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
/-- All four prescribed responses for the already selected actual wave family,
on the full parameter ball fixed by initialization. The family is retained
from the mixed signed construction; no new family or output certificate is
assumed. Full first-map responses still require the background and secondary
terms on this same family. -/
theorem generalLegalWave_initialized_physical_four_responses
    (F : M → V) (hF : ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,D) 𝓘(ℝ,V) F x))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D) (hcompact : ∀ i, IsCompact (Omega i))
    (htarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (B : BufferedAtlas P Ep) (sourceCost rho : ℝ) (hrho : 0 < rho) :
    let amplitude := passiveOriginalReserveAmplitude sourceCost rho
    let ha := passiveOriginalReserveAmplitude_pos sourceCost rho hrho
    let Initialized := jointMixedParameterInitializedAtlas B sourceCost rho hrho
    ∀ length : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ etaH etaV : ℝ → ℝ,
      (∀ t, 0 ≤ etaH t) ∧ (∀ t, 0 ≤ etaV t) ∧
      Tendsto etaH (𝓝[>] 0) (𝓝 0) ∧ Tendsto etaV (𝓝[>] 0) (𝓝 0) ∧
      ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
      ∀ (b : Fin B.count) (p₀ : P), p₀ ∈ B.inner b →
      GeneralWaveFirstFourAt F hF waves (actualRepairSamplingAtlas A Omega) weight
        (family.centeredPhysicalPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length Initialized amplitude ha b p₀)
        (Metric.ball 0 (actualRepairParameterRadius (tensorChartFamilyOfAtlas Initialized)))
        (actualRepairParameterRadius (tensorChartFamilyOfAtlas Initialized)) t C (etaH t) (etaV t) := by
  intro amplitude ha Initialized length
  have hbuffer := jointMixedParameterInitializedAtlas_buffer B sourceCost rho hrho
  obtain ⟨Cv,hCv,etaH,hHnon,hHlim,hvalue,hhessian⟩ :=
    general_family_initialized_responses F hF hImm waves weight hweight family
      A hA Omega hcompact htarget B sourceCost rho hrho length
  obtain ⟨C,hC,hnorm⟩ := family.exists_physical_parameter_norms
    A hA Omega hcompact htarget length Initialized amplitude ha hbuffer
  let etaV := originalProbeChartModulus Cv 0 1 0
  have hVnon (t : ℝ) : 0 ≤ etaV t :=
    originalProbeChartModulus_nonneg Cv 0 1 0 t hCv.le (by norm_num) (by norm_num)
  have hVlim : Tendsto etaV (𝓝[>] 0) (𝓝 0) :=
    originalProbeChartModulus_tendsto Cv 0 1 0
  have hVeq (t : ℝ) : etaV t = Cv*|t|^((1:ℝ)/10) := by
    simp [etaV,originalProbeChartModulus]
  refine ⟨C,hC,etaH,etaV,hHnon,hVnon,hHlim,hVlim,?_⟩
  intro c hc t ht ht1 b p₀ hp₀ u _ hu
  have hscale := probe_original_scale_conditions t ht ht1
  have hn (direction : ProbeParameters r) := hnorm c hc (t^(10:ℕ))
    (t^((6:ℝ)/5)) (t^((11:ℝ)/10)) hscale.2.2.1 hscale.2.2.2 hscale.2.1
    (pow_nonneg ht.le _) b p₀ hp₀ u hu direction
  refine ⟨fun direction => (hn direction).1,?_,?_,?_⟩
  · intro direction
    simpa only [mul_div_assoc,probe_delta_div_tau_eq_sigma t ht] using (hn direction).2
  · intro l sine i x hx
    have hs := (actualRepairSamplingAtlas_smooth A hA Omega htarget).support_subset i hx
    have hy : A.chart i x ∈ Omega i := by
      rw [← actualRepairSamplingAtlas_coordinate_support A Omega htarget i]
      exact ⟨x,hx,rfl⟩
    have hh := hhessian c hc t ht ht1 b p₀ hp₀ i (A.chart i x) hy u hu l sine
    have hbound := hh.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hC (norm_nonneg u))) (Real.rpow_nonneg ht.le _))
    simpa only [actualRepairSamplingAtlas_chart,(A.chart i).left_inv hs] using hbound
  · intro l sine x
    have hv := hvalue c hc t ht ht1 b p₀ hp₀ x u hu l sine
    rw [← hVeq t] at hv
    exact hv.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hC (norm_nonneg u))) (Real.rpow_nonneg ht.le _))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.generalLegalWave_initialized_physical_four_responses
