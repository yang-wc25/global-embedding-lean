import NormalPolar.ActualProbeInitialSupplySignedSecondaryResponses
import NormalPolar.FullResponseScales
import NormalPolar.FullResponseTail

/-!
# The actual signed secondary on the unchanged paired parameter ball

The original signed-secondary producer works in Fin p coordinates. This file
uses the existing exact paired linear isometry to transport its true value,
first, Hessian and original C1/C2 responses to the original probe labels.
Every derivative belongs to the same physical secondary after the same
parameter chart. The parameter radius, source atlas and samples are unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

/-- The full directional chain rule for the existing paired isometry. -/
theorem probes_paired_fderiv_apply {p r : ℕ} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (label : (Fin r × Bool) ↪ Fin p) (f : (Fin p → ℝ) → Y)
    (u direction : ProbeParameters r)
    (hf : DifferentiableAt ℝ f (probeParameterEmbedding label u)) :
    fderiv ℝ (fun v => f (probeParameterEmbedding label v)) u direction =
      fderiv ℝ f (probeParameterEmbedding label u) (probeParameterEmbedding label direction) := by
  exact congrArg (fun L : ProbeParameters r →L[ℝ] Y => L direction)
    (hf.hasFDerivAt.comp u (probeParameterEmbedding label).toContinuousLinearMap.hasFDerivAt).fderiv

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

/-- All secondary responses on the original paired ball, including the exact
original atlas norms and every direction, with no paired-coordinate loss. -/
theorem probes_signed_secondary_paired
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Omega : Fin A.count → Set D) (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hCover : ∀ x, ∃ i, x ∈ (actualRepairSamplingAtlas A Omega).support i)
    (B : BufferedAtlas P Ep) (C t : ℝ) (wave : P × M → V)
    (hBounds : actualProbeInitialSecondaryBallBounds A Omega B C t wave)
    (label : (Fin r × Bool) ↪ Fin p)
    (b : Fin B.count) (p₀ : P) (hp₀ : p₀ ∈ B.inner b) :
    let radius := actualRepairParameterRadius (tensorChartFamilyOfAtlas B)
    let out := fun (u : ProbeParameters r) x =>
      wave (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ (probeParameterEmbedding label u),x)
    let Aout := actualRepairSamplingAtlas A Omega
    (∀ i, ContDiffOn ℝ ∞ (fun z : ProbeParameters r × D => out z.1 ((A.chart i).symm z.2))
      (Metric.ball 0 radius ×ˢ (A.chart i).target)) ∧
    (∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ x direction,
      ‖fderiv ℝ (fun v => out v x) u direction‖ ≤
        t^((56:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖) ∧
    (∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ i x, x ∈ Aout.support i → ∀ direction,
      ‖fderiv ℝ (fun v => fderiv ℝ (out v ∘ (Aout.chart i).symm) (Aout.chart i x)) u direction‖ ≤
        t^(10:ℕ)*actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (out v ∘ (Aout.chart i).symm)) (Aout.chart i x)) u direction‖ ≤
        t^((44:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖) ∧
    ∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ direction,
      probeAtlasCj Aout 1 (fun x => fderiv ℝ (fun v => out v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*actualProbeSecondaryModulus C t*t^(10:ℕ)*‖direction‖) ∧
      probeAtlasCj Aout 2 (fun x => fderiv ℝ (fun v => out v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*actualProbeSecondaryModulus C t*t^((44:ℝ)/5)*‖direction‖) := by
  intro radius out Aout
  let native := fun (v : Params) x => wave (actualRepairParameterMap (tensorChartFamilyOfAtlas B) b p₀ v,x)
  obtain ⟨hJ,hN,hNorm⟩ := hBounds b p₀ hp₀
  have hEmbed (u : ProbeParameters r) (hu : u ∈ Metric.ball (0 : ProbeParameters r) radius) :
      probeParameterEmbedding label u ∈ Metric.ball (0 : Params) radius := by
    simpa only [Metric.mem_ball,dist_zero_right,probeParameterEmbedding_norm] using hu
  have hValDiff (v : Params) (hv : v ∈ Metric.ball (0 : Params) radius) (x : M) :
      DifferentiableAt ℝ (fun w => native w x) v := by
    obtain ⟨i,hi⟩ := A.cover x
    have hs := A.inner_subset i hi
    have hj : ContDiffAt ℝ ∞
        (fun z : Params × D => native z.1 ((A.chart i).symm z.2)) (v,A.chart i x) :=
      (hJ i).contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds
        ⟨hv,(A.chart i).map_source hs⟩)
    have hslice := hj.comp v (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [Function.comp_def,id_eq,(A.chart i).left_inv hs] using
      hslice.differentiableAt (by simp)
  have hAout : IsSmoothBufferedAtlas Aout := actualRepairSamplingAtlas_smooth A hA Omega hTarget
  have hSample (i : Fin A.count) (x : M) (hx : x ∈ Aout.support i) : A.chart i x ∈ Omega i := by
    rw [← actualRepairSamplingAtlas_coordinate_support A Omega hTarget i]
    exact ⟨x,hx,rfl⟩
  have hPairJoint (i : Fin A.count) : ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × D => out z.1 ((A.chart i).symm z.2))
      (Metric.ball 0 radius ×ˢ (A.chart i).target) := by
    have hm : ContDiff ℝ ∞ (fun z : ProbeParameters r × D => (probeParameterEmbedding label z.1,z.2)) :=
      ((probeParameterEmbedding label).toContinuousLinearMap.contDiff.comp contDiff_fst).prodMk contDiff_snd
    exact (hJ i).comp hm.contDiffOn (fun z hz => ⟨hEmbed z.1 hz.1,hz.2⟩)
  refine ⟨hPairJoint,?_,?_,?_⟩
  · intro u hu x direction
    obtain ⟨i,hx⟩ := hCover x
    have hb := (hN i (probeParameterEmbedding label u) (hEmbed u hu)
      (A.chart i x) (hSample i x hx) (probeParameterEmbedding label direction)).1
    have h0 : ‖fderiv ℝ (fun w => native w x) (probeParameterEmbedding label u)
        (probeParameterEmbedding label direction)‖ ≤
        t^((56:ℝ)/5)*actualProbeSecondaryModulus C t*‖direction‖ := by
      simpa only [(A.chart i).left_inv (hAout.support_subset i hx),probeParameterEmbedding_norm] using hb
    change ‖fderiv ℝ (fun v => native (probeParameterEmbedding label v) x) u direction‖ ≤ _
    rw [probes_paired_fderiv_apply label (fun v => native v x) u direction (hValDiff _ (hEmbed u hu) x)]
    exact h0
  · intro u hu i x hx direction
    let f := fun (v : Params) y => native v ((A.chart i).symm y)
    have hxTarget := (A.chart i).map_source (hAout.support_subset i hx)
    have hy : (probeParameterEmbedding label u,A.chart i x) ∈
        Metric.ball (0 : Params) radius ×ˢ (A.chart i).target := ⟨hEmbed u hu,hxTarget⟩
    have jets := incrementsJointSpatialJets_bridge (fun z : Params × D => f z.1 z.2)
      (Metric.ball (0 : Params) radius ×ˢ (A.chart i).target)
      (Metric.isOpen_ball.prod (A.chart i).open_target) (hJ i)
    have hfirst : DifferentiableAt ℝ (fun v => fderiv ℝ (f v) (A.chart i x)) (probeParameterEmbedding label u) :=
      (((jets.2.1.contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hy)).comp
        (probeParameterEmbedding label u) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    have hhess : DifferentiableAt ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) (A.chart i x))
        (probeParameterEmbedding label u) :=
      (((jets.2.2.contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hy)).comp
        (probeParameterEmbedding label u) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    have hb := (hN i (probeParameterEmbedding label u) (hEmbed u hu)
      (A.chart i x) (hSample i x hx) (probeParameterEmbedding label direction)).2
    constructor
    · change ‖fderiv ℝ (fun v => fderiv ℝ (f (probeParameterEmbedding label v)) (A.chart i x)) u direction‖ ≤ _
      rw [probes_paired_fderiv_apply label (fun v => fderiv ℝ (f v) (A.chart i x)) u direction hfirst]
      simpa only [probeParameterEmbedding_norm] using hb.1
    · change ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f (probeParameterEmbedding label v))) (A.chart i x)) u direction‖ ≤ _
      rw [probes_paired_fderiv_apply label (fun v => fderiv ℝ (fderiv ℝ (f v)) (A.chart i x)) u direction hhess]
      simpa only [probeParameterEmbedding_norm] using hb.2
  · intro u hu direction
    have heq : (fun x => fderiv ℝ (fun v => out v x) u direction) =
        (fun x => fderiv ℝ (fun v => native v x) (probeParameterEmbedding label u)
          (probeParameterEmbedding label direction)) := by
      funext x
      exact probes_paired_fderiv_apply label (fun v => native v x) u direction (hValDiff _ (hEmbed u hu) x)
    rw [heq]
    simpa only [probeParameterEmbedding_norm] using hNorm
      (probeParameterEmbedding label u) (probeParameterEmbedding label direction) (hEmbed u hu)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_paired_fderiv_apply
#print axioms GlobalEmbedding.Continuation.probes_signed_secondary_paired
