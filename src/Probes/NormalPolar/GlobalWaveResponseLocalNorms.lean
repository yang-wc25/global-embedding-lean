import NormalPolar.ParameterDisplacementFirstIncrementNorms
import NormalPolar.ActualProbeSecondaryUniform
import NormalPolar.FullResponseTail
import NormalPolar.OriginalProbeScales

/-! Native parameter responses become the literal original spatial C1/C2
gauges. The order of differentiation is changed only using genuine joint
smoothness of the same family. All lower jets are included, and the actual
source/target norm-conversion constants are retained. -/
noncomputable section
open Set Filter Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade GlobalEmbedding.Continuation
variable {n N : ℕ} {P M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)
private local instance atlasResponseHessianSemi : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance atlasResponseHessianNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance atlasResponseHessianSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem globalWave_original_parameter_norms_from_charts
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (U : Set P) (hU : IsOpen U) (F : P → M → V)
    (hF : ∀ i, ContDiffOn ℝ ∞ (fun z : P×E => F z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (u d : P) (hu : u ∈ U) (tau delta C : ℝ)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (h0 : ∀ i x, x ∈ A.support i → ‖fderiv ℝ (fun v => F v x) u‖ ≤ C*delta*tau)
    (h1 : ∀ i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v => fderiv ℝ (F v ∘ (A.chart i).symm) (A.chart i x)) u‖ ≤ C*delta)
    (h2 : ∀ i x, x ∈ A.support i →
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u‖ ≤
        C*delta/tau) :
    probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => F v x) u d) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant n N 1*C*delta*‖d‖) ∧
    probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => F v x) u d) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant n N 2*C*delta/tau*‖d‖) := by
  let response : M → V := fun x => fderiv ℝ (fun v => F v x) u d
  have hchart (i : Fin A.count) : ContDiffOn ℝ ∞ (response ∘ (A.chart i).symm) (A.chart i).target := by
    have hd := (contDiffOn_actual_parameter_fderiv (hU.prod (A.chart i).open_target)
      (hF i)).clm_apply (contDiffOn_const (c:=d))
    exact hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨hu,hy⟩)
  have hjets : ∀ i, ∀ k ≤ 2, ∀ x ∈ A.support i,
      tau^k*‖iteratedFDeriv ℝ k (response ∘ (A.chart i).symm) (A.chart i x)‖ ≤
        (C*‖d‖)*delta*tau := by
    intro i k hk x hx
    have hxsource := hA.support_subset i hx
    interval_cases k
    · simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero,Function.comp_apply,
        (A.chart i).left_inv hxsource,response]
      calc
        _ ≤ ‖fderiv ℝ (fun v => F v x) u‖*‖d‖ := ContinuousLinearMap.le_opNorm _ d
        _ ≤ (C*delta*tau)*‖d‖ := mul_le_mul_of_nonneg_right (h0 i x hx) (norm_nonneg d)
        _ = _ := by ring
    · have hf := hF i
      have he := actual_parameter_spatial_fderiv_comm
        (fun z : P×E => F z.1 ((A.chart i).symm z.2)) u (A.chart i x) d
        (hf.contDiffAt ((hU.prod (A.chart i).open_target).mem_nhds
          ⟨hu,(A.chart i).map_source hxsource⟩))
      have hb := (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fun v => fderiv ℝ (F v ∘ (A.chart i).symm) (A.chart i x)) u) d).trans
        (mul_le_mul_of_nonneg_right (h1 i x hx) (norm_nonneg d))
      change ‖fderiv ℝ (fun v => fderiv ℝ (fun y => F v ((A.chart i).symm y)) (A.chart i x)) u d‖ ≤ _ at hb
      rw [he] at hb
      simp only [pow_one,norm_iteratedFDeriv_one]
      exact (mul_le_mul_of_nonneg_left hb htau.le).trans_eq (by ring)
    · have hb := (ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm)) (A.chart i x)) u) d).trans
        (mul_le_mul_of_nonneg_right (h2 i x hx) (norm_nonneg d))
      have he : fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (F v ∘ (A.chart i).symm))
          (A.chart i x)) u d = fderiv ℝ (fderiv ℝ (response ∘ (A.chart i).symm)) (A.chart i x) :=
        actual_parameter_spatial_second_fderiv_comm (hU.prod (A.chart i).open_target)
          (fun z : P×E => F z.1 ((A.chart i).symm z.2)) (hF i) u (A.chart i x) d
          ⟨hu,(A.chart i).map_source hxsource⟩
      rw [he] at hb
      have hn : ‖iteratedFDeriv ℝ 2 (response ∘ (A.chart i).symm) (A.chart i x)‖ =
          ‖fderiv ℝ (fderiv ℝ (response ∘ (A.chart i).symm)) (A.chart i x)‖ := by
        rw [← norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one]
      rw [hn]
      exact (mul_le_mul_of_nonneg_left hb (sq_nonneg tau)).trans_eq (by field_simp)
  have hbound (j : ℕ) (hj : j ≤ 2) := probeAtlasCj_le_of_native_chart_weighted_jets
    A hA response hchart j tau delta (C*‖d‖) htau htau1 hdelta (by positivity)
      (fun i k hk x hx => hjets i k (hk.trans hj) x hx)
  have he1 : probeAtlasFromNativeConstant n N 1*((C*‖d‖)*delta*tau/tau^1) =
      probeAtlasFromNativeConstant n N 1*C*delta*‖d‖ := by field_simp
  have he2 : probeAtlasFromNativeConstant n N 2*((C*‖d‖)*delta*tau/tau^2) =
      probeAtlasFromNativeConstant n N 2*C*delta/tau*‖d‖ := by field_simp
  exact ⟨by simpa only [he1] using hbound 1 (by omega),
    by simpa only [he2] using hbound 2 (by omega)⟩

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_original_parameter_norms_from_charts
