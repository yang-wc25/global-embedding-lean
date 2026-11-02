import Upgrade.IncidenceSupportedTolerance
import Upgrade.SupportedProbeJointSmooth

/-!
# The literal two-point supported incidence

Both source charts and the actual global new map occur in this function.
Its zero set is the original supported-coincidence set. Its smoothness is
derived from the actual jointly smooth map and actual normal identification,
which are fields of the full probes interface. No rank or avoidance premise
is used in the geometric dictionary.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

namespace SupportedJointWavePacket
variable {F₀ : M → EuclideanSpace ℝ (Fin N)}
  {hF₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F₀} {x y : M}
  {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y}
  {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))} {hA : IsSmoothBufferedAtlas A} {i : Fin A.count}
  {hx : x ∈ (A.chart i).source}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

include A hA i hx

/-- The original supported predicate and the equality of the two actual
values are exactly the two normalized equations, on the actual normal chart. -/
theorem IncidenceData.zero_iff (data : IncidenceData p A hA i hx P)
    (w : P × (E × E)) (hσ : data.sigma ≠ 0) (ha : data.a ≠ 0)
    (hw : w.2.1 ∈ (A.chart i).target)
    (hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2.1)).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (hdom : actualSupportedProbeCoordinate F₀ data.map data.smooth data.identification
      A hA i x hx (w.1, w.2.1) ∈ p.chart.domain) :
    data.incidence w = 0 ↔
      HasSupportedKernel (trueSecondForm (data.map w.1) (data.smooth w.1)
        ((A.chart i).symm w.2.1)) ∧
      data.map w.1 ((A.chart i).symm w.2.1) =
        data.map w.1 ((A.chart data.secondChart).symm w.2.2) := by
  have hzero := actualSupportedProbeCoordinate_equation_zero_iff
    F₀ data.map data.smooth data.identification A hA i x hx (w.1, w.2.1)
    hw hgap _ p.chart hdom
  change jointScaledIncidence
    (fun u z ↦ actualSupportedProbeCoordinate F₀ data.map data.smooth data.identification
      A hA i x hx (u, z))
    (fun u z ↦ data.map u ((A.chart i).symm z))
    (fun u z ↦ data.map u ((A.chart data.secondChart).symm z))
    p.chart.equation data.sigma data.a w = 0 ↔ _
  rw [jointScaledIncidence_eq_zero_iff _ _ _ _ _ _ hσ ha]
  exact and_congr hzero Iff.rfl

/-- Joint smoothness of the actual family and its chosen identification
implies joint smoothness of its literal supported-coincidence equations. -/
theorem IncidenceData.contDiffOn_incidence (data : IncidenceData p A hA i hx P)
    {U : Set P} (hU : IsOpen U)
    (hmap : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry data.map) (U ×ˢ univ))
    (hQ : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun z : P × M ↦ normalIdentificationOperator (n := n)
        F₀ (data.map z.1) (data.identification z.1) z.2) (U ×ˢ univ))
    {Ω : Set (P × (E × E))}
    (hΩ : ∀ w ∈ Ω, w.1 ∈ U ∧ w.2.1 ∈ (A.chart i).target ∧
      w.2.2 ∈ (A.chart data.secondChart).target)
    (hdom : ∀ w ∈ Ω, actualSupportedProbeCoordinate F₀ data.map data.smooth
      data.identification A hA i x hx (w.1, w.2.1) ∈ p.chart.domain) :
    ContDiffOn ℝ ∞ data.incidence Ω := by
  have hfirst : ContDiff ℝ ∞ (fun w : P × (E × E) ↦ (w.1, w.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hsecond : ContDiff ℝ ∞ (fun w : P × (E × E) ↦ (w.1, w.2.2)) :=
    contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hC := (actualSupportedProbeCoordinate_contDiffOn F₀ data.map data.smooth
    data.identification A hA i x hx hU hmap hQ).comp hfirst.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.1⟩)
  have hR := p.chart.contDiffOn_equation.comp hC hdom
  have hFx := (contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry data.map) hmap).comp hfirst.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.1⟩)
  have hFy := (contDiffOn_actual_parameter_atlas_pullback A hA data.secondChart
    (Function.uncurry data.map) hmap).comp hsecond.contDiffOn
      (fun w hw ↦ ⟨(hΩ w hw).1, (hΩ w hw).2.2⟩)
  exact (hR.const_smul data.sigma⁻¹).prodMk ((hFx.sub hFy).const_smul data.a⁻¹)

end SupportedJointWavePacket

#print axioms SupportedJointWavePacket.IncidenceData.zero_iff
#print axioms SupportedJointWavePacket.IncidenceData.contDiffOn_incidence

end GlobalEmbedding.Upgrade
