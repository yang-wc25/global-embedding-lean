import ProbesClosure.GeneralGroupedIdentity
import ProbesClosure.GeneralOriginalHessian
import NormalPolar.ActualRepairSamplingAtlas

/-! An actual original-wave family with both paper responses on the original
repair samples. The auxiliary atlas changes only its bookkeeping supports:
its chart, differentiation domain and sampled norm are literally unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
private local instance paperOriginalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance paperOriginalHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance paperOriginalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem exists_generalLegalWave_paper_responses
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF)
    (weight : Fin r → ℝ) (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (Omega : Fin atlas.count → Set D)
    (hcompact : ∀ j, IsCompact (Omega j))
    (htarget : ∀ j, Omega j ⊆ (atlas.chart j).target) :
    ∃ family : GeneralLegalWaveRawFamily F hF waves weight,
    ∀ length : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ modulus : ℝ → ℝ,
      (∀ t, 0 ≤ modulus t) ∧ Tendsto modulus (𝓝[>] 0) (𝓝 0) ∧
      (∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
        ∀ (x : M) (u : ProbeParameters r) (k : Fin r) (sine : Bool),
        ‖fderiv ℝ (fun v => family.groupedPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length v x)
            u (Pi.single (k,sine) 1) -
          (-(t^((56:ℝ)/5))*(weight k^2)⁻¹ *
            probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) • (waves k).value x‖ ≤
          t^((56:ℝ)/5) * (C * |t|^((1:ℝ)/10))) ∧
      (∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
        ∀ j y, y ∈ Omega j → ∀ (u : ProbeParameters r) (k : Fin r) (sine : Bool),
        ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
            (family.groupedPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length v ∘ (atlas.chart j).symm))
            y) u (Pi.single (k,sine) 1) -
          (t^((44:ℝ)/5)*probeTrig sine
            (weight k*(waves k).phase ((atlas.chart j).symm y)/t^((6:ℝ)/5))) •
            phaseRankOneHessian ((waves k).phase ∘ (atlas.chart j).symm)
              ((waves k).value ∘ (atlas.chart j).symm) y‖ ≤
          t^((44:ℝ)/5) * modulus t) := by
  obtain ⟨family⟩ := exists_generalLegalWaveRawFamily F hF hImm waves weight hweight
  refine ⟨family,?_⟩
  intro length
  let sampleAtlas := actualRepairSamplingAtlas atlas Omega
  have hsmooth : IsSmoothBufferedAtlas sampleAtlas :=
    actualRepairSamplingAtlas_smooth atlas hAtlas Omega htarget
  have hsupport : ∀ j, IsCompact (sampleAtlas.support j) :=
    actualRepairSamplingAtlas_support_compact atlas Omega hcompact htarget
  obtain ⟨C,hC,hvalue⟩ := family.exists_original_value_response hImm hweight
    sampleAtlas hsmooth hsupport length
  obtain ⟨modulus,hnonneg,hlimit,hhessian⟩ := family.exists_original_hessian_response
    hImm hweight sampleAtlas hsmooth hsupport length
  refine ⟨C,hC,modulus,hnonneg,hlimit,?_,?_⟩
  · intro c hc t ht ht1 x u k sine
    rw [family.groupedPairMap_eq_originalPairMap]
    exact hvalue c hc t ht ht1 x u k sine
  · intro c hc t ht ht1 j y hy u k sine
    have hx : (atlas.chart j).symm y ∈ sampleAtlas.support j := ⟨y,hy,rfl⟩
    have h := hhessian c hc t ht ht1 j ((atlas.chart j).symm y) hx u k sine
    simpa only [sampleAtlas,actualRepairSamplingAtlas_chart,
      (atlas.chart j).right_inv (htarget j hy),family.groupedPairMap_eq_originalPairMap] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.exists_generalLegalWave_paper_responses

