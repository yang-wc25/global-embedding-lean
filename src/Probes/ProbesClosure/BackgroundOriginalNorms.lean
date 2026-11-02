import NormalPolar.GlobalWaveResponseLocalNorms
import NormalPolar.GlobalWaveResponseFirstSmooth
import NormalPolar.GlobalWaveResponseBackgroundPhysical

/-!
# Sharp background responses on the literal original atlas and paired ball

This conversion is used after the actual canonical/grouped source constructor.
It multiplies one and the same background by the physical scalar and uses the
existing exact paired linear isometry.  The parameter radius is unchanged.
All native source observations remain on their original samples; only their
already available coverage of the atlas supports is used.  Jointness is
assembled from the actual atlas chart regularity, including when a sample is
empty.  No completed manifold jointness or norm estimate is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade
variable {m N p r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin p)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "Params" => Fin p → ℝ
private local instance : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

/-- The original C1/C2 norms and true jointness of the scaled paired background.
The only analytic input is the already constructed sharp chart response of
that very background; the map, radius, original atlas and samples are fixed. -/
theorem probes_background_original_parameter_norms
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (Samples : Fin A.count → Set (Ep × D))
    (hSamples : ∀ i x, x ∈ A.support i → ∃ y ∈ Samples i, y.2 = A.chart i x)
    (radius tau delta C : ℝ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (wave : Params → M → V)
    (hSharp : ∀ i,
      ContDiffOn ℝ ∞ (fun z : Params × D => wave z.1 ((A.chart i).symm z.2))
        (Metric.ball 0 radius ×ˢ (A.chart i).target) ∧
      ∀ u ∈ Metric.ball (0 : Params) radius, ∀ y ∈ Samples i,
      let f := fun v x => wave v ((A.chart i).symm x)
      (HasFDerivAt (fun v => f v y.2) (fderiv ℝ (fun v => f v y.2) u) u ∧
        ‖fderiv ℝ (fun v => f v y.2) u‖ ≤ C*tau*‖u‖) ∧
      (HasFDerivAt (fun v => fderiv ℝ (f v) y.2)
        (fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u) u ∧
        ‖fderiv ℝ (fun v => fderiv ℝ (f v) y.2) u‖ ≤ C*‖u‖) ∧
      (HasFDerivAt (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2)
        (fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u) u ∧
        ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (f v)) y.2) u‖ ≤ C/tau*‖u‖))
    (label : (Fin r × Bool) ↪ Fin p) :
    let B := fun (u : ProbeParameters r) x => delta • wave (probeParameterEmbedding label u) x
    (∀ i, ContDiffOn ℝ ∞ (fun z : ProbeParameters r × D => B z.1 ((A.chart i).symm z.2))
      (Metric.ball 0 radius ×ˢ (A.chart i).target)) ∧
    ContMDiffOn ((𝓘(ℝ,ProbeParameters r)).prod IM) 𝓘(ℝ,V) ∞ (Function.uncurry B)
      (Metric.ball 0 radius ×ˢ univ) ∧
    ∀ u ∈ Metric.ball (0 : ProbeParameters r) radius, ∀ direction : ProbeParameters r,
      probeAtlasCj A 1 (fun x => fderiv ℝ (fun v => B v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 1*(C*‖u‖)*delta*‖direction‖) ∧
      probeAtlasCj A 2 (fun x => fderiv ℝ (fun v => B v x) u direction) ≤
        ENNReal.ofReal (probeAtlasFromNativeConstant (m+1) N 2*(C*‖u‖)*delta/tau*‖direction‖) := by
  intro B
  have hEmbed (u : ProbeParameters r) (hu : u ∈ Metric.ball (0 : ProbeParameters r) radius) :
      probeParameterEmbedding label u ∈ Metric.ball (0 : Params) radius := by
    simpa only [Metric.mem_ball,dist_zero_right,probeParameterEmbedding_norm] using hu
  have hBJ (i : Fin A.count) : ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × D => B z.1 ((A.chart i).symm z.2))
      (Metric.ball 0 radius ×ˢ (A.chart i).target) := by
    have hmap : ContDiff ℝ ∞ (fun z : ProbeParameters r × D =>
        (probeParameterEmbedding label z.1,z.2)) :=
      ((probeParameterEmbedding label).toContinuousLinearMap.contDiff.comp contDiff_fst).prodMk contDiff_snd
    exact ((hSharp i).1.comp hmap.contDiffOn (fun z hz => ⟨hEmbed z.1 hz.1,hz.2⟩)).const_smul delta
  let Acover : BufferedAtlas M D := { A with support := A.inner }
  have hAcover : IsSmoothBufferedAtlas Acover := ⟨hA.chart_mem,A.inner_subset⟩
  have hJoint := globalWave_joint_of_original_atlas Acover hAcover A.cover
    (Metric.ball (0 : ProbeParameters r) radius) Metric.isOpen_ball B hBJ
  refine ⟨hBJ,hJoint,?_⟩
  intro u hu direction
  have hembed := hEmbed u hu
  have hBounds (i : Fin A.count) (x : M) (hx : x ∈ A.support i) :
      ‖fderiv ℝ (fun v => B v x) u‖ ≤ (C*‖u‖)*delta*tau ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (B v ∘ (A.chart i).symm) (A.chart i x)) u‖ ≤
        (C*‖u‖)*delta ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (B v ∘ (A.chart i).symm)) (A.chart i x)) u‖ ≤
        (C*‖u‖)*delta/tau := by
    obtain ⟨y,hy,heq⟩ := hSamples i x hx
    have hn := (hSharp i).2 (probeParameterEmbedding label u) hembed y hy
    rw [heq] at hn
    let f := fun v z => wave v ((A.chart i).symm z)
    have h0 : HasFDerivAt (fun v => wave v x)
        (fderiv ℝ (fun v => wave v x) (probeParameterEmbedding label u)) (probeParameterEmbedding label u) ∧
        ‖fderiv ℝ (fun v => wave v x) (probeParameterEmbedding label u)‖ ≤ C*tau*‖probeParameterEmbedding label u‖ := by
      simpa only [(A.chart i).left_inv (hA.support_subset i hx)] using hn.1
    have hv := globalWave_paired_scaled_native_bound label (fun v => wave v x) u delta (C*tau) h0.1 h0.2
    have hd := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (f v) (A.chart i x))
      u delta C hn.2.1.1 hn.2.1.2
    have hh := globalWave_paired_scaled_native_bound label (fun v => fderiv ℝ (fderiv ℝ (f v)) (A.chart i x))
      u delta (C/tau) hn.2.2.1 hn.2.2.2
    have he1 : (fun v => fderiv ℝ (B v ∘ (A.chart i).symm) (A.chart i x)) =
        (fun v => delta • fderiv ℝ (f (probeParameterEmbedding label v)) (A.chart i x)) := by
      funext v
      exact globalWave_native_first_smul _ _ _
    have he2 : (fun v => fderiv ℝ (fderiv ℝ (B v ∘ (A.chart i).symm)) (A.chart i x)) =
        (fun v => delta • fderiv ℝ (fderiv ℝ (f (probeParameterEmbedding label v))) (A.chart i x)) := by
      funext v
      exact globalWave_native_hessian_smul _ _ _
    refine ⟨hv.2.trans_eq (by rw [abs_of_nonneg hdelta]; ring),?_,?_⟩
    · rw [he1]
      exact hd.2.trans_eq (by rw [abs_of_nonneg hdelta]; ring)
    · rw [he2]
      exact hh.2.trans_eq (by rw [abs_of_nonneg hdelta]; ring)
  exact globalWave_original_parameter_norms_from_charts A hA
    (Metric.ball (0 : ProbeParameters r) radius) Metric.isOpen_ball B hBJ u direction hu
    tau delta (C*‖u‖) htau htau1 hdelta (mul_nonneg hC (norm_nonneg u))
    (fun i x hx => (hBounds i x hx).1) (fun i x hx => (hBounds i x hx).2.1)
    (fun i x hx => (hBounds i x hx).2.2)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.probes_background_original_parameter_norms
