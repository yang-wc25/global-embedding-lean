import Initialization.Assembly.ActualPhaseJets

/-!
# Actual cross-chart rate discrepancy

The discrepancy is the derivative of the actual frozen phase, multiplied by
the real frequency, minus the same actual normalized coframe in reference
coordinates. It is never a separately supplied formal error field.
-/

noncomputable section
open Bundle Manifold Set Metric Filter IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

theorem fderiv_centered_rescaling
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (q : E) (T : ℝ) (y : E)
    (hf : DifferentiableAt ℝ f (q + T⁻¹ • y)) :
    fderiv ℝ (fun z ↦ f (q + T⁻¹ • z)) y =
      T⁻¹ • fderiv ℝ f (q + T⁻¹ • y) := by
  have ha : HasFDerivAt (fun z : E ↦ q + T⁻¹ • z)
      (T⁻¹ • ContinuousLinearMap.id ℝ E) y := by
    simpa only [zero_add, Pi.add_def, Pi.smul_def, id_eq] using
      (hasFDerivAt_const q y).add ((hasFDerivAt_id y).const_smul T⁻¹)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using
    (hf.hasFDerivAt.comp y ha).fderiv

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable (G : PreparedCharts M n)
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (f : FullTangentFrame 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M) n)

theorem actualPhaseCoordinate_contDiffAt {K : ℝ} (F : ChartCutoffFamily G K)
    (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : q + T⁻¹ • y ∈ (G.chart p).target)
    (hx : (G.chart p).symm (q + T⁻¹ • y) ∈ (G.chart (F.parent i)).source) :
    ContDiffAt ℝ ∞ (actualPhaseCoordinate G g f F p q T i) y := by
  have ha : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ↦ q + T⁻¹ • z) :=
    contDiff_const.add (contDiff_id.const_smul T⁻¹)
  have hb := (contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth p)).contMDiffAt
    ((G.chart p).open_target.mem_nhds hy)
  have hc := (F.frozenVectorPhase_contMDiffOn G g f i).contMDiffAt
    ((G.chart (F.parent i)).open_source.mem_nhds hx)
  exact (hc.comp y (hb.comp y ha.contMDiff.contMDiffAt)).contDiffAt

theorem actualReferenceCoframe_contDiffAt
    (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : q + T⁻¹ • y ∈ (G.chart p).target) :
    ContDiffAt ℝ ∞ (actualReferenceCoframe G g f p q T) y := by
  have ha : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ↦ q + T⁻¹ • z) :=
    contDiff_const.add (contDiff_id.const_smul T⁻¹)
  exact ((chartOrthonormalCoframe_contDiffOn g f (G.chart p) (G.chart_smooth p)).contDiffAt
    ((G.chart p).open_target.mem_nhds hy)).comp y ha.contDiffAt

/-- The actual rate field is smooth in every genuine overlap neighborhood. -/
theorem actualPhaseRateError_contDiffAt {K : ℝ} (F : ChartCutoffFamily G K)
    (p : Fin G.count) (q : EuclideanSpace ℝ (Fin n)) (T : ℝ) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : q + T⁻¹ • y ∈ (G.chart p).target)
    (hx : (G.chart p).symm (q + T⁻¹ • y) ∈ (G.chart (F.parent i)).source) :
    ContDiffAt ℝ ∞ (actualPhaseRateError G g f F p q T i) y :=
  (((actualPhaseCoordinate_contDiffAt G g f F p q T i hy hx).fderiv_right
    (m := ∞) (by simp)).const_smul T).sub
      (actualReferenceCoframe_contDiffAt G g f p q T hy)

/-- The true phase derivative in any reference chart is the frozen actual
coframe times the true chart-transition derivative. -/
theorem ChartCutoffFamily.frozenVectorPhase_crossChart_fderiv
    {K : ℝ} (F : ChartCutoffFamily G K) (p : Fin G.count) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (G.chart p).target)
    (hx : (G.chart p).symm y ∈ (G.chart (F.parent i)).source) :
    fderiv ℝ (F.frozenVectorPhase G g f i ∘ (G.chart p).symm) y =
      (preparedCoframe G g f (F.parent i) (F.center i)).comp
        (fderiv ℝ (G.chart (F.parent i) ∘ (G.chart p).symm) y) := by
  have htr : DifferentiableAt ℝ (G.chart (F.parent i) ∘ (G.chart p).symm) y :=
    mdifferentiableAt_iff_differentiableAt.mp
      (((initialization_chart_mdifferentiable _ (G.chart_smooth (F.parent i))).mdifferentiableAt hx).comp y
        ((initialization_chart_mdifferentiable _ (G.chart_smooth p)).mdifferentiableAt_symm hy))
  exact ((preparedCoframe G g f (F.parent i) (F.center i)).hasFDerivAt.comp y
    (htr.hasFDerivAt.sub_const (F.center i))).fderiv

/-- Exact cancellation of the real frequency: the actual rate error factors
through the actual frozen-coframe difference and the true transition. -/
theorem actualPhaseRateError_eq_frozen_transition
    {K : ℝ} (F : ChartCutoffFamily G K) (p : Fin G.count)
    (q : EuclideanSpace ℝ (Fin n)) {T : ℝ} (hT : T ≠ 0) (i : Fin F.count)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : q + T⁻¹ • y ∈ (G.chart p).target)
    (hx : (G.chart p).symm (q + T⁻¹ • y) ∈ (G.chart (F.parent i)).source) :
    actualPhaseRateError G g f F p q T i y =
      (preparedCoframe G g f (F.parent i) (F.center i) -
        preparedCoframe G g f (F.parent i)
          (G.chart (F.parent i) ((G.chart p).symm (q + T⁻¹ • y)))).comp
        (fderiv ℝ (G.chart (F.parent i) ∘ (G.chart p).symm) (q + T⁻¹ • y)) := by
  let ψ := F.frozenVectorPhase G g f i ∘ (G.chart p).symm
  have hψ : DifferentiableAt ℝ ψ (q + T⁻¹ • y) :=
    ((((F.frozenVectorPhase_contMDiffOn G g f i).contMDiffAt
      ((G.chart (F.parent i)).open_source.mem_nhds hx)).comp (q + T⁻¹ • y)
        ((contMDiffOn_symm_of_mem_maximalAtlas (G.chart_smooth p)).contMDiffAt
          ((G.chart p).open_target.mem_nhds hy))).contDiffAt).differentiableAt (by simp)
  change T • fderiv ℝ (fun z ↦ ψ (q + T⁻¹ • z)) y -
    preparedCoframe G g f p (q + T⁻¹ • y) = _
  rw [fderiv_centered_rescaling ψ q T y hψ, smul_smul, mul_inv_cancel₀ hT, one_smul]
  rw [F.frozenVectorPhase_crossChart_fderiv G g f p i hy hx]
  exact chartOrthonormalCoframe_frozen_transition_error g f _ _
    (G.chart_smooth (F.parent i)) (G.chart_smooth p) (F.center i) hy hx

end GlobalEmbedding.Initialization
