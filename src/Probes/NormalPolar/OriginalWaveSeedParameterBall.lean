import NormalPolar.PassiveOriginalSmallParameter

/-! The amplitude restriction must be chosen at initialization. If the
initial buffer already meets that restriction, the small global parameter
is the identity on the entire original repair ball, with every derivative.
No previously fixed ball is shrunk by these statements. -/
noncomputable section
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "X" => Fin d → ℝ

theorem passiveOriginalSmallParameter_original_radius
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1)) :
    actualRepairParameterRadius
      (tensorChartFamilyOfAtlas (passiveOriginalAmplitudeAtlas B amplitude ha)) =
      actualRepairParameterRadius (tensorChartFamilyOfAtlas B) := by
  change min B.buffer (amplitude/
    (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1)) /
    (‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖+1) =
    B.buffer/(‖(EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap‖+1)
  rw [min_eq_left hbuffer]

theorem passiveOriginalSmallParameter_original_ball_identity
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : X) (hv : ‖v‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) :
    passiveOriginalSmallParameter B amplitude ha b p₀
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ v) = v := by
  apply passiveOriginalSmallParameter_local_identity B amplitude ha b p₀ hp₀ v
  rwa [passiveOriginalSmallParameter_original_radius B amplitude ha hbuffer]

theorem passiveOriginalSmallParameter_original_ball_germ
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : X) (hv : ‖v‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) :
    (fun w => passiveOriginalSmallParameter B amplitude ha b p₀
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ w)) =ᶠ[𝓝 v]
      (id : X → X) := by
  have hm : v ∈ Metric.ball (0 : X)
      (actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) := by
    simpa only [Metric.mem_ball,dist_zero_right] using hv
  filter_upwards [Metric.isOpen_ball.mem_nhds hm] with w hw
  exact passiveOriginalSmallParameter_original_ball_identity B amplitude ha hbuffer b p₀ hp₀ w
    (by simpa only [Metric.mem_ball,dist_zero_right] using hw)

theorem passiveOriginalSmallParameter_original_ball_jets
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (amplitude : ℝ) (ha : 0 < amplitude)
    (hbuffer : B.buffer ≤ amplitude/
      (‖(EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap‖+1))
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b)
    (v : X) (hv : ‖v‖ < actualRepairParameterRadius (tensorChartFamilyOfAtlas B)) (k : ℕ) :
    iteratedFDeriv ℝ k (fun w => passiveOriginalSmallParameter B amplitude ha b p₀
      (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ w)) v =
      iteratedFDeriv ℝ k (id : X → X) v := by
  have he := passiveOriginalSmallParameter_original_ball_germ B amplitude ha hbuffer b p₀ hp₀ v hv
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_original_radius
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_original_ball_identity
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_original_ball_germ
#print axioms GlobalEmbedding.Continuation.passiveOriginalSmallParameter_original_ball_jets

