import Upgrade.SupportedIdentifiedHessian
import Upgrade.SupportedPartialHessianSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Joint smoothness of the actual supported incidence from full probes

The only family hypotheses here are the original joint smoothness of the map
and of its actual normal-identification operator. The actual spatial Hessian
is differentiated from that same family and descended through the accepted
canonical Hessian lift. The preceding exact geometric dictionary identifies
this smooth expression with the literal true-second-form incidence.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
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

/-- A jointly smooth actual family remains jointly smooth in an actual atlas
inverse chart. The parameter and spatial differentiation domains stay open. -/
theorem contDiffOn_actual_parameter_atlas_pullback
    {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (f : P × M → Y)
    (hf : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, Y) ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × E ↦ f (z.1, (A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target) := by
  have hfst : ContMDiffOn 𝓘(ℝ, P × E) 𝓘(ℝ, P) ∞
      (Prod.fst : P × E → P) (U ×ˢ (A.chart i).target) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, P × E) 𝓘(ℝ, E) ∞
      (Prod.snd : P × E → E) (U ×ˢ (A.chart i).target) :=
    contDiff_snd.contMDiff.contMDiffOn
  have hinv : ContMDiffOn 𝓘(ℝ, P × E) IM ∞
      (fun z : P × E ↦ (A.chart i).symm z.2) (U ×ˢ (A.chart i).target) :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)).comp hsnd (fun _ hz ↦ hz.2)
  exact (hf.comp (hfst.prodMk hinv) (fun z hz ↦ ⟨hz.1, mem_univ _⟩)).contDiffOn

/-- The literal true-second-form coordinate incidence is jointly smooth.
Unlike an abstract smooth-field hypothesis, this conclusion is derived from
the same actual jointly smooth maps and identifications supplied by probes. -/
theorem identifiedTrueSecondForm_in_atlas_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    {U : Set P} (hU : IsOpen U)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (hQ : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (G z.1) (Q z.1) z.2)
      (U ×ˢ univ)) :
    ContDiffOn ℝ ∞
      (fun z : P × E ↦ probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm z.2))
        (identifiedTrueSecondForm (n := n) F₀ (G z.1) (hG z.1) (Q z.1)
          ((A.chart i).symm z.2)))
      (U ×ˢ (A.chart i).target) := by
  have hFcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry G) hjoint
  have hH := contDiffOn_actual_spatial_hessianJet
    (hU.prod (A.chart i).open_target) hFcoords
  have hQcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (G z.1) (Q z.1) z.2) hQ
  apply (hQcoords.clm_comp hH).congr
  intro z hz
  rw [identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (G z.1) (hG z.1)
    (Q z.1) A hA i ((A.chart i).symm z.2) ((A.chart i).map_target hz.2)]
  congr 1
  change coordinateHessianJet (G z.1 ∘ (A.chart i).symm)
    ((A.chart i) ((A.chart i).symm z.2)) = _
  rw [(A.chart i).right_inv hz.2]
  rfl

/-- Fixed normalization and fixed normal projection preserve the actual
joint smoothness, with no additional regularity premise on a second form. -/
theorem actualSupportedProbeCoordinate_contDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) {U : Set P} (hU : IsOpen U)
    (hjoint : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (hQ : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (G z.1) (Q z.1) z.2)
      (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx)
      (U ×ˢ (A.chart i).target) := by
  have hFcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry G) hjoint
  have hH := contDiffOn_actual_spatial_hessianJet
    (hU.prod (A.chart i).open_target) hFcoords
  have hQcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (fun z : P × M ↦ normalIdentificationOperator (n := n) F₀ (G z.1) (Q z.1) z.2) hQ
  have hB := hQcoords.clm_comp hH
  have hBK := hB.clm_comp (contDiffOn_const (c := probeAtlasNormalizationSquare A hA i x hx))
  have hC := (contDiffOn_const (c := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto)).clm_comp hBK
  apply hC.congr
  intro z hz
  exact actualSupportedProbeCoordinate_eq_identified_hessian F₀ G hG Q A hA i x hx z hz.2

/-- The full original probe geometry directly discharges the joint-smoothness
condition in actual supported avoidance on its admitted parameter ball. -/
theorem ProbeGeometry.actual_supported_coordinate_smooth
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htop : t < g.threshold) :
    ContDiffOn ℝ ∞
      (actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
        (g.normalIdentification t) A hA i x hx)
      (Metric.ball 0 g.radius ×ˢ (A.chart i).target) :=
  actualSupportedProbeCoordinate_contDiffOn F₀ (g.map t) (g.slice_smooth t)
    (g.normalIdentification t) A hA i x hx Metric.isOpen_ball
    (g.joint_smooth t ht htop) (g.normalIdentification_smooth t ht htop)

/-- The full probe geometry supplies raw atlas-framed identified true-form
smoothness before either fixed source normalization or fixed normal projection. -/
theorem ProbeGeometry.identified_trueSecondForm_in_atlas_smooth
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htop : t < g.threshold) :
    ContDiffOn ℝ ∞
      (fun z : ProbeParameters r × E ↦
        probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm z.2))
          (identifiedTrueSecondForm (n := n) F₀ (g.map t z.1) (g.slice_smooth t z.1)
            (g.normalIdentification t z.1) ((A.chart i).symm z.2)))
      (Metric.ball 0 g.radius ×ˢ (A.chart i).target) :=
  identifiedTrueSecondForm_in_atlas_contDiffOn F₀ (g.map t) (g.slice_smooth t)
    (g.normalIdentification t) A hA i Metric.isOpen_ball
    (g.joint_smooth t ht htop) (g.normalIdentification_smooth t ht htop)

/-- The very same atlas-framed field occurring in the probe response is
parameter differentiable at every admitted parameter and atlas-source point. -/
theorem ProbeGeometry.identified_trueSecondForm_parameter_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htop : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ
      (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u := by
  have hraw := g.identified_trueSecondForm_in_atlas_smooth A hA i t ht htop
  have hu' : u ∈ Metric.ball 0 g.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨hu', (A.chart i).map_source hz⟩
  have hD : DifferentiableAt ℝ
      (fun w : ProbeParameters r × E ↦
        probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm w.2))
          (identifiedTrueSecondForm (n := n) F₀ (g.map t w.1) (g.slice_smooth t w.1)
            (g.normalIdentification t w.1) ((A.chart i).symm w.2)))
      (u, A.chart i z) :=
    (hraw.contDiffAt ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have hparam := actual_parameter_differentiableAt
    (fun w : ProbeParameters r × E ↦
      probeTensorInFrame (probeAtlasFrame A i ((A.chart i).symm w.2))
        (identifiedTrueSecondForm (n := n) F₀ (g.map t w.1) (g.slice_smooth t w.1)
          (g.normalIdentification t w.1) ((A.chart i).symm w.2))) hD
  simpa only [Function.comp_def, (A.chart i).left_inv hz] using hparam

#print axioms contDiffOn_actual_parameter_atlas_pullback
#print axioms identifiedTrueSecondForm_in_atlas_contDiffOn
#print axioms actualSupportedProbeCoordinate_contDiffOn
#print axioms ProbeGeometry.actual_supported_coordinate_smooth
#print axioms ProbeGeometry.identified_trueSecondForm_in_atlas_smooth
#print axioms ProbeGeometry.identified_trueSecondForm_parameter_differentiable

end GlobalEmbedding.Upgrade
