import Round2.ProbeBridgeSecondForm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Native mixed derivatives of the actual probe map

The parameter first-jet derivative used in the moving-tangent correction is
the spatial derivative of the actual parameter response. This file proves
that identity from joint smoothness and bounds it using the original atlas
C¹ norm. No normal-identification derivative estimate is supplied.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

section MixedDerivatives
variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual parameter derivative is smooth jointly on the original open
product domain. The equality is the native derivative restriction. -/
theorem contDiffOn_actual_parameter_fderiv
    {Ω : Set (P × X)} (hΩ : IsOpen Ω) {f : P × X → Y}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fun u ↦ f (u, z.2)) z.1) Ω := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω := hf.fderiv_of_isOpen hΩ (by simp)
  have hP := hD.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ P X))
  apply hP.congr
  intro z hz
  exact actual_parameter_fderiv_eq_joint f
    ((hf.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))

/-- Native mixed derivatives commute for the same jointly smooth map.
The statement differentiates the parameter response field, never an angular
linear-combination coefficient chosen after evaluating the derivative. -/
theorem actual_parameter_spatial_fderiv_comm
    (f : P × X → Y) (u : P) (x : X) (d : P)
    (hf : ContDiffAt ℝ ∞ f (u, x)) :
    fderiv ℝ (fun v ↦ fderiv ℝ (fun s ↦ f (v, s)) x) u d =
      fderiv ℝ (fun s ↦ fderiv ℝ (fun v ↦ f (v, s)) u d) x := by
  have hDC : ContDiffAt ℝ ∞ (fderiv ℝ f) (u, x) := hf.fderiv_right (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (u, x) := hDC.differentiableAt (by simp)
  have hnear : ∀ᶠ z in 𝓝 (u, x), DifferentiableAt ℝ f z := by
    filter_upwards [(hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)]
      with z hz
    exact hz.differentiableAt (by simp)
  have hleft : (fun v ↦ fderiv ℝ (fun s ↦ f (v, s)) x) =ᶠ[𝓝 u]
      (fun v ↦ (fderiv ℝ f (v, x)).comp (ContinuousLinearMap.inr ℝ P X)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear]
      with v hv
    exact actual_spatial_fderiv_eq_joint f hv
  have hright : (fun s ↦ fderiv ℝ (fun v ↦ f (v, s)) u d) =ᶠ[𝓝 x]
      (fun s ↦ fderiv ℝ f (u, s) (d, 0)) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hnear]
      with s hs
    have hs' : DifferentiableAt ℝ f (u, s) := hs
    exact congrArg (fun L : P →L[ℝ] Y ↦ L d) (actual_parameter_fderiv_eq_joint f hs')
  have hDL : HasFDerivAt (fun v : P ↦ fderiv ℝ f (v, x))
      ((fderiv ℝ (fderiv ℝ f) (u, x)).comp (ContinuousLinearMap.inl ℝ P X)) u :=
    hD.hasFDerivAt.comp u (hasFDerivAt_prodMk_left u x)
  have hDR : HasFDerivAt (fun s : X ↦ fderiv ℝ f (u, s))
      ((fderiv ℝ (fderiv ℝ f) (u, x)).comp (ContinuousLinearMap.inr ℝ P X)) x :=
    hD.hasFDerivAt.comp x (hasFDerivAt_prodMk_right u x)
  have hL := hDL.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ P X) u)
  have hR := hDR.clm_apply (hasFDerivAt_const (d, (0 : X)) x)
  rw [hleft.fderiv_eq, hL.fderiv, hright.fderiv_eq, hR.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simpa using hf.isSymmSndFDerivAt (by simp) (d, 0) (0, v)

end MixedDerivatives

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Actual parameter differentiation of the fixed-atlas first jet is the
fixed-atlas first jet of the actual parameter response. -/
theorem ProbeGeometry.atlas_firstJet_parameter_derivative_eq
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    fderiv ℝ (fun v ↦ probeAtlasFirstJet A (g.map t v) i z) u d =
      probeAtlasFirstJet A (fun y ↦ fderiv ℝ (fun v ↦ g.map t v y) u d) i z := by
  have hf := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, (A.chart i).map_source hz⟩
  exact actual_parameter_spatial_fderiv_comm
    (fun w : ProbeParameters r × E ↦ g.map t w.1 ((A.chart i).symm w.2))
    u (A.chart i z) d
    (hf.contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw))

/-- The actual parameter response has smooth coordinates on every original
atlas chart, by restriction of the jointly smooth parameter derivative. -/
theorem ProbeGeometry.atlas_parameter_response_contDiffOn
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) :
    ContDiffOn ℝ ∞
      ((fun y ↦ fderiv ℝ (fun v ↦ g.map t v y) u d) ∘ (A.chart i).symm)
      (A.chart i).target := by
  have hf := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)
  have hD := (contDiffOn_actual_parameter_fderiv
    (Metric.isOpen_ball.prod (A.chart i).open_target) hf).clm_apply
    (contDiffOn_const (c := d))
  apply hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn
  intro s hs
  exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hu, hs⟩

/-- Original C¹ control of the actual parameter response controls the
parameter derivative of the actual fixed-atlas first jet. Only chart
smoothness, derived above from the same geometry, is used. -/
theorem ProbeGeometry.atlas_firstJet_parameter_derivative_bound_of_originalC1
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ A.support i) {b : ℝ} (hb : 0 ≤ b)
    (hbound : probeAtlasCj A 1
      (fun y ↦ fderiv ℝ (fun v ↦ g.map t v y) u d) ≤ ENNReal.ofReal b) :
    ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (g.map t v) i z) u d‖ ≤
      probeAtlasDerivativeConstant n N 1 * b := by
  rw [g.atlas_firstJet_parameter_derivative_eq A hA i t ht htt u d hu z
    (hA.support_subset i hz)]
  let F := fun y ↦ fderiv ℝ (fun v ↦ g.map t v y) u d
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let O := e '' (A.chart i).target
  let S := e '' ((A.chart i) '' A.support i)
  have hO : IsOpen O := e.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro y ⟨s, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨A.chart i p, (A.chart i).map_source (hA.support_subset i hp), rfl⟩
  have hcoords := g.atlas_parameter_response_contDiffOn A hA i t ht htt u d hu
  have hsmooth : ContDiffOn ℝ ∞
      (euclideanCoordinateRepresentative e (F ∘ (A.chart i).symm)) O := by
    apply (EuclideanSpace.equiv (Fin N) ℝ).contDiff.comp_contDiffOn
    apply hcoords.comp e.symm.contDiff.contDiffOn
    rintro y ⟨s, hs, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hs
  have hlocal : paperCoordinateCj 1
      (euclideanCoordinateRepresentative e (F ∘ (A.chart i).symm)) O S ≤
        ENNReal.ofReal b := (le_iSup
          (fun k ↦ paperCoordinateCj 1
            (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
              (F ((A.chart k).symm (e.symm y))))
            (e '' (A.chart k).target) (e '' ((A.chart k) '' A.support k))) i).trans hbound
  have h := iteratedFDeriv_le_of_euclidean_coordinate_bound_at_normDomain e
    (F ∘ (A.chart i).symm) hO hSO hsmooth hb hlocal (show 1 ≤ 1 by rfl)
    (show e (A.chart i z) ∈ S from ⟨A.chart i z, ⟨z, hz, rfl⟩, rfl⟩)
  rw [norm_iteratedFDeriv_one] at h
  calc
    _ = ‖fderiv ℝ (F ∘ (A.chart i).symm) (A.chart i z)‖ := rfl
    _ ≤ _ := h
    _ = probeAtlasDerivativeConstant n N 1 * b := by
      unfold probeAtlasDerivativeConstant
      dsimp only [e]
      ring

/-- The original probes parameter C¹ estimate gives the real O(t^10)
moving-tangent term, without any quantitative parameter-DQ assumption. -/
theorem ExactProbeFamily.atlas_firstJet_parameter_derivative_bound
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (z : M) (hz : z ∈ A.support i) :
    ‖fderiv ℝ (fun v ↦ probeAtlasFirstJet A (probe.map t v) i z) u d‖ ≤
      probeAtlasDerivativeConstant n N 1 * (probe.constant * t ^ (10 : ℕ) * ‖d‖) := by
  exact probe.toProbeGeometry.atlas_firstJet_parameter_derivative_bound_of_originalC1
    A hA i t ht htt u d hu z hz
    (mul_nonneg (mul_nonneg probe.constant_nonneg (pow_nonneg ht.le _)) (norm_nonneg d))
    (probe.parameter_C1 t ht htt u hu d)

#print axioms actual_parameter_spatial_fderiv_comm
#print axioms ProbeGeometry.atlas_firstJet_parameter_derivative_eq
#print axioms ProbeGeometry.atlas_firstJet_parameter_derivative_bound_of_originalC1
#print axioms ExactProbeFamily.atlas_firstJet_parameter_derivative_bound

end GlobalEmbedding.Upgrade
