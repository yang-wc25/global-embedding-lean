import Upgrade.RankQProbeResponse
import Upgrade.IncidencePairedColumns

/-!
# Full actual probe errors after the incidence equation

The same exact probe family supplies the parameter derivative of its actual
identified true form and both actual value derivatives. The first source
frame varies with the point and is normalized only by the fixed center frame.
The current nonlinear defining equation is differentiated at the actual form.
At the second point only the leading cutoff term vanishes: its global value
derivatives remain in the estimate. No incidence rank is an input.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance incidenceTrueFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance incidenceTrueFormNormedSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- Native parameter differentiability of the actual value at a point follows
from the original joint smoothness, with no extra slice-in-parameter premise. -/
theorem ProbeGeometry.value_parameter_differentiable_in_atlas
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius) (z : M)
    (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ (fun v ↦ g.map t v z) u := by
  have hcoords := contDiffOn_actual_parameter_atlas_pullback A hA i
    (Function.uncurry (g.map t)) (g.joint_smooth t ht htt)
  have hu' : u ∈ Metric.ball 0 g.radius := by simpa using hu
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨hu', (A.chart i).map_source hz⟩
  have hD := (hcoords.contDiffAt
    ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have hp := actual_parameter_differentiableAt
    (fun w : ProbeParameters r × E ↦ g.map t w.1 ((A.chart i).symm w.2)) hD
  simpa only [Function.comp_def, (A.chart i).left_inv hz] using hp

/-- Native parameter differentiability of the literal fixed-normal,
normalized-source true form follows from the same full probe geometry. -/
theorem ProbeGeometry.projected_trueSecondForm_parameter_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius) (z : M)
    (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ
      (fun v ↦ projectedIdentifiedTrueForm F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) x z (probeAtlasNormalizedFrame A hA i x hx z)) u := by
  have hcoords := g.actual_supported_coordinate_smooth A hA i x hx t ht htt
  have hu' : u ∈ Metric.ball 0 g.radius := by simpa using hu
  have hw : (u, A.chart i z) ∈ Metric.ball 0 g.radius ×ˢ (A.chart i).target :=
    ⟨hu', (A.chart i).map_source hz⟩
  have hD := (hcoords.contDiffAt
    ((Metric.isOpen_ball.prod (A.chart i).open_target).mem_nhds hw)).differentiableAt (by simp)
  have hp := actual_parameter_differentiableAt
    (actualSupportedProbeCoordinate F₀ (g.map t) (g.slice_smooth t)
      (g.normalIdentification t) A hA i x hx) hD
  simpa only [actualSupportedProbeCoordinate, Function.comp_def,
    (A.chart i).left_inv hz] using hp

/-- Full original probe estimates imply the actual normalized paired
incidence error. The derivative-variation term and both global value tails
are explicit. The equation may be the actual Schur or supported equation. -/
theorem ExactProbeFamily.actual_paired_incidence_error
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (i j : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source)
    (z y : M) (hz : z ∈ A.support i) (hy : y ∈ (A.chart j).source)
    (haway : (waves l).cutoff y = 0)
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (equation : (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) → R)
    (D₀ : (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) →L[ℝ] R)
    (delta : ℝ) :
    let C := fun v q ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
      (probe.normalIdentification t v) x q (probeAtlasNormalizedFrame A hA i x hx q)
    let T := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))
    let theta := probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    DifferentiableAt ℝ equation (C u z) →
    ‖fderiv ℝ equation (C u z) - D₀‖ ≤ delta →
    ‖fderiv ℝ
        (fun v ↦ scaledIncidence C (probe.map t) (probe.map t) equation sigma a v z y) u
        (pairedRadialDirection theta (Pi.single (l, false) 1) (Pi.single (l, true) 1)) -
      (D₀ T, -((probe.weight l ^ 2)⁻¹) • (waves l).value z)‖ ≤
      max (delta * ‖T‖ + 4 * ‖fderiv ℝ equation (C u z)‖ *
        ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) := by
  dsimp only
  let C := fun v q ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
    (probe.normalIdentification t v) x q (probeAtlasNormalizedFrame A hA i x hx q)
  let T := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
    (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))
  let v := -((probe.weight l ^ 2)⁻¹) • (waves l).value z
  let theta := probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5)
  let sigma := t ^ ((44 : ℝ) / 5)
  let a := t ^ ((56 : ℝ) / 5)
  let d0 : ProbeParameters r := Pi.single (l, false) 1
  let d1 : ProbeParameters r := Pi.single (l, true) 1
  let eB0 := fderiv ℝ (fun w ↦ C w z) u d0 - (sigma * Real.cos theta) • T
  let eB1 := fderiv ℝ (fun w ↦ C w z) u d1 - (sigma * Real.sin theta) • T
  let eV0 := fderiv ℝ (fun w ↦ probe.map t w z) u d0 - (a * Real.cos theta) • v
  let eV1 := fderiv ℝ (fun w ↦ probe.map t w z) u d1 - (a * Real.sin theta) • v
  let eY0 := fderiv ℝ (fun w ↦ probe.map t w y) u d0
  let eY1 := fderiv ℝ (fun w ↦ probe.map t w y) u d1
  have hB0 := probe.projected_normalized_secondForm_response hA t ht htt u hu l false i x hx z hz
  have hB1 := probe.projected_normalized_secondForm_response hA t ht htt u hu l true i x hx z hz
  have hV0 := probe.value_response_principal t ht htt u hu l false z
  have hV1 := probe.value_response_principal t ht htt u hu l true z
  have hY0 := probe.value_response_away t ht htt u hu l false y haway
  have hY1 := probe.value_response_away t ht htt u hu l true y haway
  have hC := probe.toProbeGeometry.projected_trueSecondForm_parameter_differentiable
    A hA i x hx t ht htt u hu z (hA.support_subset i hz)
  have hF := probe.toProbeGeometry.value_parameter_differentiable_in_atlas
    A hA i t ht htt u hu z (hA.support_subset i hz)
  have hH := probe.toProbeGeometry.value_parameter_differentiable_in_atlas
    A hA j t ht htt u hu y hy
  intro hR hD
  apply norm_scaledIncidence_paired_error_le
    (fun w (_ : E) ↦ C w z)
    (fun w (_ : E) ↦ probe.map t w z)
    (fun w (_ : E) ↦ probe.map t w y) equation
    sigma a theta (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos ht _)
    u 0 0 d0 d1 T v D₀ eB0 eB1 eV0 eY0 eV1 eY1
    ((probe.etaB t + probe.constant * ‖u‖) * ‖probeAtlasNormalizationSquare A hA i x hx‖)
    (probe.etaV t + probe.constant * ‖u‖) delta
  · exact mul_nonneg (add_nonneg (probe.etaB_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg u))) (norm_nonneg _)
  · exact add_nonneg (probe.etaV_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg u))
  · exact hC
  · exact hR
  · exact hF
  · exact hH
  · dsimp only [eB0]; abel
  · dsimp only [eB1]; abel
  · dsimp only [eV0]; abel
  · dsimp only [eV1]; abel
  · rfl
  · rfl
  · exact hB0
  · exact hB1
  · exact hV0
  · exact hY0
  · exact hV1
  · exact hY1
  · exact hD

#print axioms ProbeGeometry.value_parameter_differentiable_in_atlas
#print axioms ProbeGeometry.projected_trueSecondForm_parameter_differentiable
#print axioms ExactProbeFamily.actual_paired_incidence_error

end GlobalEmbedding.Upgrade
