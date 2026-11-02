import NormalPolar.GlobalWaveResponseAtlasNorms
import NormalPolar.GlobalWaveResponseBackgroundPhysical
import NormalPolar.ActualRepairSamplingAtlas

/-! The full actual mean-iterate background has the sharp original C1/C2
parameter responses on the SAME source sampling atlas. All native bounds
and joint regularity are constructed from primitive original data. The
observer-image cover is explicit and is produced by the actual packet
parameter plateau; no old support is silently placed inside its samples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical ENNReal Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation GlobalEmbedding.Upgrade
universe uM uTr uΛ uΒ
variable {m d N p r count : ℕ} {M : Type uM} {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance bgActualHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance bgActualHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance bgActualHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- A norm-conversion bridge, applied below only to the actual constructed
background family. The same paired isometry and literal scalar map are
used before differentiating in either variable. -/
theorem globalWave_background_native_norm_bridge
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (label : (Fin r × Bool) ↪ Fin p) (wave : (Fin p → ℝ) → Ep × M → V)
    (Su : Set (Fin p → ℝ)) (hSu : IsOpen Su) (W : Set (Ep × M))
    (hJoint : ContMDiffOn ((𝓘(ℝ,(Fin p → ℝ)×Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (fun z : ((Fin p → ℝ)×Ep)×M => wave z.1.1 (z.1.2,z.2))
      {z | z.1.1 ∈ Su ∧ (z.1.2,z.2) ∈ W})
    (Samples : Fin atlas.count × Fin count → Set X)
    (tau Cost delta : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hCost : 0 ≤ Cost) (hdelta : 0 ≤ delta)
    (hNative : ∀ idx (u : Fin p → ℝ), u ∈ Su → ∀ y ∈ Samples idx,
      let f := fun v x => wave v (y.1,(atlas.chart idx.1).symm x)
      (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
        ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ 2*(Cost*tau)*‖u‖) ∧
      (HasFDerivAt (fun v => fderiv ℝ (f v) y.2) (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
        ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ 2*Cost*‖u‖) ∧
      (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
        (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
        ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤ 2*(Cost/tau)*‖u‖))
    (b : Ep) (hSlice : ∀ x, (b,x) ∈ W)
    (Spatial : Fin atlas.count → Set D) (hSpatialTarget : ∀ i, Spatial i ⊆ (atlas.chart i).target)
    (hSpatialSamples : ∀ i y, y ∈ Spatial i → ∃ j : Fin count, (b,y) ∈ Samples (i,j))
    (u direction : ProbeParameters r) (hu : probeParameterEmbedding label u ∈ Su) :
    let B := fun (v : ProbeParameters r) x => delta • wave (probeParameterEmbedding label v) (b,x)
    probeAtlasCj (actualRepairSamplingAtlas atlas Spatial) 1
      (fun x => fderiv ℝ (fun v => B v x) u direction) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*(2*Cost*‖u‖)*delta*‖direction‖) ∧
    probeAtlasCj (actualRepairSamplingAtlas atlas Spatial) 2
      (fun x => fderiv ℝ (fun v => B v x) u direction) ≤
      ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*(2*Cost*‖u‖)*delta/tau*‖direction‖) := by
  intro B
  let U := (probeParameterEmbedding label) ⁻¹' Su
  have hU : IsOpen U := hSu.preimage (probeParameterEmbedding label).continuous
  let SampleAtlas := actualRepairSamplingAtlas atlas Spatial
  have hSampleAtlas : IsSmoothBufferedAtlas SampleAtlas :=
    actualRepairSamplingAtlas_smooth atlas hAtlas Spatial hSpatialTarget
  have hMap : ContMDiff ((𝓘(ℝ,ProbeParameters r)).prod 𝓙) ((𝓘(ℝ,(Fin p → ℝ)×Ep)).prod 𝓙) ∞
      (fun z : ProbeParameters r × M => ((probeParameterEmbedding label z.1,b),z.2)) :=
    ((((probeParameterEmbedding label).toContinuousLinearMap.contDiff.prodMk contDiff_const).contMDiff).comp
      contMDiff_fst).prodMk contMDiff_snd
  have hScale : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ (fun v : V => delta • v) := by
    convert (delta • (ContinuousLinearMap.id ℝ V)).contDiff.contMDiff using 1
    funext v
    rfl
  have hBJ : ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry B) (U ×ˢ univ) :=
    hScale.comp_contMDiffOn (hJoint.comp hMap.contMDiffOn (fun z hz => ⟨hz.1,hSlice z.2⟩))
  have hBounds (i : Fin atlas.count) (x : M) (hx : x ∈ SampleAtlas.support i) :
      ‖fderiv ℝ (fun v => B v x) u‖ ≤ (2*(Cost)*‖u‖)*delta*tau ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (B v ∘ (atlas.chart i).symm) (atlas.chart i x)) u‖ ≤
        (2*(Cost)*‖u‖)*delta ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (B v ∘ (atlas.chart i).symm)) (atlas.chart i x)) u‖ ≤
        (2*(Cost)*‖u‖)*delta/tau := by
    have hxsource := hSampleAtlas.support_subset i hx
    have hxy : atlas.chart i x ∈ Spatial i := by
      rw [← actualRepairSamplingAtlas_coordinate_support atlas Spatial hSpatialTarget i]
      exact ⟨x,hx,rfl⟩
    obtain ⟨j,hj⟩ := hSpatialSamples i (atlas.chart i x) hxy
    have hn := hNative (i,j) (probeParameterEmbedding label u) hu (b,atlas.chart i x) hj
    let f := fun v y => wave v
      (b,(atlas.chart i).symm y)
    have h0 : HasFDerivAt (fun v => wave v (b,x))
        (fderiv ℝ (fun v => wave v (b,x))
          (probeParameterEmbedding label u)) (probeParameterEmbedding label u) ∧
        ‖fderiv ℝ (fun v => wave v (b,x))
          (probeParameterEmbedding label u)‖ ≤ 2*(Cost*tau)*‖probeParameterEmbedding label u‖ := by
      simpa only [(atlas.chart i).left_inv hxsource] using hn.1
    have hb0 := globalWave_paired_scaled_native_bound label _ u delta (2*(Cost*tau)) h0.1 h0.2
    have hb1 := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (f v) (atlas.chart i x)) u delta
      (2*(Cost)) hn.2.1.1 hn.2.1.2
    have hb2 := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (fderiv ℝ (f v)) (atlas.chart i x))
      u delta (2*(Cost/tau)) hn.2.2.1 hn.2.2.2
    have he1 : (fun v => fderiv ℝ (B v ∘ (atlas.chart i).symm) (atlas.chart i x)) =
        (fun v => delta • fderiv ℝ (f (probeParameterEmbedding label v)) (atlas.chart i x)) := by
      funext v
      exact globalWave_native_first_smul (f (probeParameterEmbedding label v)) delta (atlas.chart i x)
    have he2 : (fun v => fderiv ℝ (fderiv ℝ (B v ∘ (atlas.chart i).symm)) (atlas.chart i x)) =
        (fun v => delta • fderiv ℝ (fderiv ℝ (f (probeParameterEmbedding label v))) (atlas.chart i x)) := by
      funext v
      exact globalWave_native_hessian_smul (f (probeParameterEmbedding label v)) delta (atlas.chart i x)
    refine ⟨hb0.2.trans_eq ?_,?_,?_⟩
    · rw [abs_of_nonneg hdelta]
      ring
    · rw [he1]
      exact hb1.2.trans_eq (by rw [abs_of_nonneg hdelta]; ring)
    · rw [he2]
      exact hb2.2.trans_eq (by rw [abs_of_nonneg hdelta]; ring)
  exact globalWave_original_parameter_norms SampleAtlas hSampleAtlas U hU B hBJ u direction hu
    tau delta (2*(Cost)*‖u‖) htau htau1 hdelta (by positivity)
    (fun i x hx => (hBounds i x hx).1) (fun i x hx => (hBounds i x hx).2.1)
    (fun i x hx => (hBounds i x hx).2.2)

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_native_norm_bridge
