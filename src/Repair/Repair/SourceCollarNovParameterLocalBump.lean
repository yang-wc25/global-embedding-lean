import Repair.SourceCollarNovCutoffs
import Repair.SourceCollarNovParentCutoffs

/-!
# Parameter localization inside an unchanged original chart

The already given global raw cutoff protects the original chart boundary.
Consequently this construction needs no Hausdorff assumption on the ambient
parameter space.  A small Euclidean bump and a fixed scalar plateau produce
a new auxiliary local unit function supported in the requested open set.
No numerical derivative bound for this auxiliary function is asserted.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- A local unit bump protected by an original globally smooth raw cutoff.
The actual chart and its target are not restricted or replaced. -/
theorem sourceCollarNov_parameter_local_unit_bump
    (e : OpenPartialHomeomorph P Ep) (he : e ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (raw : P → ℝ) (hRaw : ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ raw)
    (hSupport : tsupport raw ⊆ e.source)
    (U : Set P) (hU : IsOpen U) (p : P) (hp : p ∈ U) (hOne : raw p = 1) :
    ∃ beta : P → ℝ, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ beta ∧
      (∀ q, 0 ≤ beta q ∧ beta q ≤ 1) ∧ tsupport beta ⊆ U ∧ beta =ᶠ[𝓝 p] 1 := by
  have hpSource : p ∈ e.source :=
    hSupport (subset_tsupport raw (by change raw p ≠ 0; rw [hOne]; exact one_ne_zero))
  let O : Set Ep := e.target ∩ e.symm ⁻¹' U
  have hO : IsOpen O := e.isOpen_inter_preimage_symm hU
  have hpO : e p ∈ O := ⟨e.map_source hpSource,by
    change e.symm (e p) ∈ U
    rwa [e.left_inv hpSource]⟩
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hpO)
  let eta : ContDiffBump (e p) := {
    rIn := r/4
    rOut := r/2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  let theta : P → ℝ := sourceCollarNovPlateauScalar ∘ raw
  have hTheta : ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ theta :=
    sourceCollarNovPlateauScalar_contDiff.comp_contMDiff hRaw
  have hThetaSupport : tsupport theta ⊆ tsupport raw := by
    intro q hq
    have hPos : (1/2 : ℝ) ≤ raw q :=
      sourceCollarNovPlateauScalar_tsupport (tsupport_comp_subset_preimage _ hRaw.continuous hq)
    exact subset_tsupport raw (by intro hz; rw [hz] at hPos; norm_num at hPos)
  let beta := sourceCollarNovCutoff e theta eta
  have hBeta : ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ beta :=
    sourceCollarNovCutoff_contMDiff e he theta eta hTheta (hThetaSupport.trans hSupport) eta.contDiff
  refine ⟨beta,hBeta,?_,?_,?_⟩
  · intro q
    by_cases hq : q ∈ e.source
    · change 0 ≤ sourceCollarNovCutoff e theta eta q ∧ sourceCollarNovCutoff e theta eta q ≤ 1
      simp only [sourceCollarNovCutoff,Set.indicator_of_mem hq]
      have ht0 : 0 ≤ theta q := tensorCoverageBump.nonneg
      have ht1 : theta q ≤ 1 := tensorCoverageBump.le_one
      refine ⟨mul_nonneg ht0 eta.nonneg,?_⟩
      exact (mul_le_mul_of_nonneg_right ht1 eta.nonneg).trans (by simpa using eta.le_one (x := e q))
    · simp only [beta,sourceCollarNovCutoff,Set.indicator_of_notMem hq]
      exact ⟨le_rfl,zero_le_one⟩
  · intro q hq
    have hh := sourceCollarNovCutoff_tsupport e theta eta (hThetaSupport.trans hSupport) hq
    have heq : e q ∈ closedBall (e p) (r/2) := by
      have heq' : e q ∈ tsupport (eta : Ep → ℝ) := hh.2.2
      simpa only [eta.tsupport_eq] using heq'
    have hqO : e q ∈ O := hBall (closedBall_subset_ball (by linarith) heq)
    have hqU : e.symm (e q) ∈ U := hqO.2
    rwa [e.left_inv hh.2.1] at hqU
  · have hArgCont : Continuous (fun q : P => (4 : ℝ)*(1-raw q)) :=
      continuous_const.mul (continuous_const.sub hRaw.continuous)
    have hArg : Tendsto (fun q : P => (4 : ℝ)*(1-raw q)) (𝓝 p) (𝓝 (0 : ℝ)) := by
      simpa only [hOne,sub_self,mul_zero] using
        (hArgCont.continuousAt (x := p)).tendsto
    have hThetaOne : theta =ᶠ[𝓝 p] 1 := tensorCoverageBump.eventuallyEq_one.comp_tendsto hArg
    have hEtaOne : (fun q => eta (e q)) =ᶠ[𝓝 p] 1 :=
      eta.eventuallyEq_one.comp_tendsto (e.continuousAt hpSource)
    filter_upwards [e.open_source.mem_nhds hpSource,hThetaOne,hEtaOne] with q hq ht heq
    simp only [beta,sourceCollarNovCutoff,Set.indicator_of_mem hq,ht,heq,one_mul,Pi.one_apply]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parameter_local_unit_bump
