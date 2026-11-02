import Upgrade.IncidenceLeadingMargins
import Upgrade.CompactFixedAtlasPhaseGeometry

/-!
# Actual principal and source margins before a finite probe list is chosen

The principal fields are the same wave tensors and values, expressed through
the actual varying atlas source frame. The source derivative is the literal
derivative of the actual reference map in that fixed chart. An interior
enlarged-support point gives a genuine open neighborhood on which the probe
response estimates may be used. No returned probe weight enters the geometry
unless it was deliberately fixed before this construction.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Exact source direction conversion at the actual packet center. -/
theorem probeAtlasFirstJet_inverse_center
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source) (v : E) :
    probeAtlasFirstJet A F i x ((probeAtlasInverseFrameEquiv A hA i x hx).symm v) =
      mfderiv IM 𝓘(ℝ, V) F x v := by
  rw [probeAtlasFirstJet_eq_mfderiv_frame A hA F hF i x hx]
  have he := congrArg (fun T : E →L[ℝ] E ↦
    T ((probeAtlasInverseFrameEquiv A hA i x hx).symm v))
      (probeAtlasInverseFrameEquiv_toContinuousLinearMap A hA i x hx)
  change mfderiv IM 𝓘(ℝ, V) F x
      (probeAtlasFrame A i x ((probeAtlasInverseFrameEquiv A hA i x hx).symm v)) =
    mfderiv IM 𝓘(ℝ, V) F x v
  have he' : probeAtlasFrame A i x ((probeAtlasInverseFrameEquiv A hA i x hx).symm v) =
      (v : E) := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using he.symm
  exact congrArg (fun w : E ↦ mfderiv IM 𝓘(ℝ, V) F x w) he'

/-- Simultaneous genuine source and principal-field neighborhood in one
actual original chart. The first point stays in the support's interior, and
the source-coordinate derivative is compared with its actual center value. -/
theorem exists_actual_principal_source_neighborhood [T2Space M]
    {ι W R : Type*} [Fintype ι]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    (waves : ι → LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ interior (A.support i))
    (normalProjection : V →L[ℝ] W) (D : (SymmetricSquare E →L[ℝ] W) →L[ℝ] R)
    (weight : ι → ℝ) {eps : ℝ} (heps : 0 < eps) :
    let hxc := hA.support_subset i (interior_subset hx)
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ interior (A.support i) ∧
      (∀ z ∈ U, ∀ l,
        ‖atlasIncidencePrincipal (waves l) A hA i x hxc normalProjection D (weight l)
            (A.chart i z) -
          (D (normalProjection.comp ((waves l).tensor x)),
            -(weight l ^ 2)⁻¹ • (waves l).value x)‖ < eps) ∧
      (∀ z ∈ U, ‖probeAtlasFirstJet A F i z - probeAtlasFirstJet A F i x‖ < eps) := by
  intro hxc
  obtain ⟨Wc, hWc, hxWc, _, hprincipal⟩ := exists_finite_actual_principal_neighborhood
    waves A hA i x hxc normalProjection D weight eps heps
  have hfirst : ContinuousAt (probeAtlasFirstJet A F i) x :=
    ((continuousOn_probeAtlasFirstJet A hA F hF i) x hxc).continuousAt
      ((A.chart i).open_source.mem_nhds hxc)
  have hnear : ∀ᶠ z in 𝓝 x, ‖probeAtlasFirstJet A F i z - probeAtlasFirstJet A F i x‖ < eps := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hfirst.tendsto.eventually
      (Metric.ball_mem_nhds (probeAtlasFirstJet A F i x) heps)
  obtain ⟨Us, hUssub, hUs, hxUs⟩ := mem_nhds_iff.mp hnear
  let U := ((A.chart i).source ∩ (A.chart i) ⁻¹' Wc) ∩ (interior (A.support i) ∩ Us)
  refine ⟨U, ((A.chart i).isOpen_inter_preimage hWc).inter (isOpen_interior.inter hUs),
    ⟨⟨hxc, hxWc⟩, hx, hxUs⟩, fun _ hz ↦ hz.2.1,
    fun z hz l ↦ hprincipal (A.chart i z) hz.1.2 l,
    fun z hz ↦ hUssub hz.2.2⟩

end GlobalEmbedding.Upgrade
