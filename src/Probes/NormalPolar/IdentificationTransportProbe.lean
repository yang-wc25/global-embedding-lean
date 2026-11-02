import NormalPolar.IdentificationTransportDerivative

/-!
# Changing the identification of a genuine probe geometry safely

The original map, parameter ball and threshold are retained definitionally.
The response transport theorem derives all required differentiability from
the two actual geometry records. It does not reuse a second-form response
for another Q without accounting for the full gauge terms.
-/

noncomputable section
open Manifold Filter Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Select a new actual normal identification on the same actual maps.
No quantitative response is transported by this definition alone. -/
def probeGeometryWithNormalIdentification
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (Q : ∀ t u z, normalSpace (I := IM) (g.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hQ : ∀ t, 0 < t → t < g.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (g.map t w.1) (Q t w.1) w.2) (Metric.ball 0 g.radius ×ˢ univ)) :
    ProbeGeometry (n := n) F₀ r :=
  { g with normalIdentification := Q, normalIdentification_smooth := hQ }

/-- The genuine old identified form is parameter differentiable from the
same joint smooth map and normal operator, before any response estimate. -/
theorem probeGeometry_framed_identifiedSecondForm_parameter_differentiable
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) :
    DifferentiableAt ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) z)) u := by
  obtain ⟨hQ, hH⟩ := g.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz
  let H := fun v : ProbeParameters r ↦
    fderiv ℝ (fderiv ℝ (g.map t v ∘ (A.chart i).symm)) (A.chart i z)
  have hL : DifferentiableAt ℝ (fun v ↦ actualHessianLift (H v)) u :=
    (actualHessianLift («E» := E) (F := V)).differentiableAt.comp u hH
  have heq : (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
      (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
        (g.normalIdentification t v) z)) =
      fun v ↦ (normalIdentificationOperator (n := n) F₀ (g.map t v)
        (g.normalIdentification t v) z).comp (actualHessianLift (H v)) := by
    funext v
    exact identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (g.map t v)
      (g.slice_smooth t v) (g.normalIdentification t v) A hA i z hz
  rw [heq]
  exact hQ.clm_comp hL

/-- The full response transport on the original admitted parameter ball.
The wave gives its true old-normal principal column; differentiability of
both Qops and of the current old-identified form is derived from geometry. -/
theorem probeGeometry_secondForm_response_transport
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r)
    (Q : ∀ t u z, normalSpace (I := IM) (g.map t u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (hQ : ∀ t, 0 < t → t < g.threshold →
      ContMDiffOn ((𝓘(ℝ, ProbeParameters r)).prod IM) 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun w : ProbeParameters r × M ↦ normalIdentificationOperator (n := n) F₀
          (g.map t w.1) (Q t w.1) w.2) (Metric.ball 0 g.radius ×ˢ univ))
    (wave : LocalLegalWave F₀ hF₀)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius)
    (z : M) (hz : z ∈ (A.chart i).source) (coefficient : ℝ) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v) (Q t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ ≤
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ +
      ‖normalIdentificationOperator (n := n) F₀ (g.map t u) (Q t u) z -
        normalIdentificationOperator (n := n) F₀ (g.map t u) (g.normalIdentification t u) z‖ *
        ‖coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ +
      (‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v) (Q t v) z) u d‖ +
        ‖fderiv ℝ (fun v ↦ normalIdentificationOperator (n := n) F₀ (g.map t v)
          (g.normalIdentification t v) z) u d‖) *
        ‖probeTensorInFrame (probeAtlasFrame A i z)
          (identifiedTrueSecondForm (n := n) F₀ (g.map t u) (g.slice_smooth t u)
            (g.normalIdentification t u) z)‖ := by
  let gnew := probeGeometryWithNormalIdentification g Q hQ
  have hold := (g.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz).1
  have hnew := (gnew.atlas_hessian_parameter_factors_differentiable A hA i t ht htt u hu z hz).1
  have hform := probeGeometry_framed_identifiedSecondForm_parameter_differentiable
    g A hA i t ht htt u hu z hz
  apply norm_fderiv_framed_identifiedTrueSecondForm_transport_le F₀ (g.map t)
    (g.slice_smooth t) (g.normalIdentification t) (Q t) u d z (probeAtlasFrame A i z)
    (coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)) _ hold hnew hform
  rw [ContinuousLinearMap.comp_smul, wave.normalProjection_comp_tensor_in_frame]

end GlobalEmbedding.NormalPolar
