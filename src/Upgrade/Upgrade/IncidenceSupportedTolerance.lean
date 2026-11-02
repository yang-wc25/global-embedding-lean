import Upgrade.IncidenceSupportedActualPrincipal
import Upgrade.IncidenceFiniteColumns
import Upgrade.SupportedActualProbeCoordinate

/-!
# A fixed tolerance for the actual supported-coincidence joint derivative

The principal frame is constructed from the same actual legal-wave packet.
Its source vectors are changed by the inverse of the actual atlas frame at
the center. All perturbed derivatives below belong to the literal incidence
of the new global map, its identified true second form, and both value
endpoints. No desired incidence rank is an assumption.
-/

noncomputable section
open Function Manifold Module
open scoped ContDiff Topology BigOperators

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

/-- Literal actual supported-coincidence incidence on two selected charts. -/
def actualIncidence {P : Type*}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i j : Fin A.count)
    (hx : x ∈ (A.chart i).source) (sigma a : ℝ) :
    P × (E × E) → (Fin p.chart.codim → ℝ) × V :=
  jointScaledIncidence
    (fun u s ↦ actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u, s))
    (fun u s ↦ G u ((A.chart i).symm s))
    (fun u s ↦ G u ((A.chart j).symm s)) p.chart.equation sigma a

/-- The reference source derivative in this actual atlas, with no false
identification of the atlas inverse differential with the identity. -/
def sourceReferenceDerivative
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) : E →L[ℝ] V :=
  (incidenceActualTangent (n := n) F₀ x).comp
    (probeAtlasInverseFrameEquiv A hA i x hx).toContinuousLinearMap

/-- Actual atlas-coordinate preimages of the same fixed principal frame. -/
theorem exists_atlas_principal_frame
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (himm : Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source)
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (hlambda : ∀ l b, 0 < lambda l b) (hne : ∀ l, lambda l 0 ≠ lambda l 1) :
    let principal := supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
      p.equationColumns p.valueNormals lambda
    ∃ (c : Fin (n * (n - 1) / 2 + 2 * n) →
        (Fin (n * (n - 1) / 2 + n) × Fin 2) → ℝ)
      (e : Fin (n * (n - 1) / 2 + 2 * n) → E) (margin : ℝ),
      0 < margin ∧ ∀ b : Fin (n * (n - 1) / 2 + 2 * n) → ℝ,
        margin * ‖b‖ ≤ ‖∑ l, b l •
          ((∑ k, c l k • principal k) + (0, p.sourceReferenceDerivative A hA i hx (e l)))‖ := by
  dsimp only
  have hp := principalMap_finite_frame (n := n) (N := N) (F := F₀) (hF := hF₀)
    (x := x) (y := y) p himm lambda hlambda hne
  obtain ⟨d, _, margin, hmargin, hframe⟩ := hp
  let frame := probeAtlasInverseFrameEquiv A hA i x hx
  let c := fun l ↦ (d l).1
  let e := fun l ↦ frame.symm (d l).2
  refine ⟨c, e, margin, hmargin, ?_⟩
  intro b
  simpa only [principalMap, supportedJointPrincipalMap, ContinuousLinearMap.coprod_apply,
    incidenceFiniteSynthesis_apply, ContinuousLinearMap.prod_apply,
    zero_apply, sourceReferenceDerivative,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, c, e, frame] using! hframe b

/-- The actual new global family and the two selected source charts. The
coordinate tensor is computed from these objects by `actualIncidence`; no
incidence equation, derivative, rank, or separation is a data field. -/
structure IncidenceData
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) (P : Type*) where
  map : P → M → V
  smooth : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (map u)
  identification : ∀ u z,
    normalSpace (I := IM) (map u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z
  secondChart : Fin A.count
  sigma : ℝ
  a : ℝ

def IncidenceData.incidence
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y}
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A} {i : Fin A.count}
    {hx : x ∈ (A.chart i).source} {P : Type*}
    (data : IncidenceData p A hA i hx P) :
    P × (E × E) → (Fin p.chart.codim → ℝ) × V :=
  p.actualIncidence data.map data.smooth data.identification A hA i data.secondChart hx
    data.sigma data.a

/-- One positive response tolerance is fixed before all probe parameters,
small scales and fast angles. The principal frame comes from the actual
supported and saturation packets, and the actual source tangent image. -/
theorem exists_parameter_independent_actual_joint_rank_tolerance
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (himm : Injective (mfderiv IM 𝓘(ℝ, V) F₀ x))
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source)
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (hlambda : ∀ l b, 0 < lambda l b) (hne : ∀ l, lambda l 0 ≠ lambda l 1)
    :
    let principal := supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
      p.equationColumns p.valueNormals lambda
    ∃ eps > 0,
      ∀ (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P],
      ∀ (data : IncidenceData p A hA i hx P) (w : P × (E × E)),
      DifferentiableAt ℝ data.incidence w →
      ∀ d : (Fin (n * (n - 1) / 2 + n) × Fin 2) → P,
      (∀ l, ‖fderiv ℝ (fun v ↦ data.incidence (v, w.2)) w.1 (d l) - principal l‖ ≤ eps) →
      (∀ v, ‖fderiv ℝ (fun s ↦ data.incidence (w.1, s, w.2.2)) w.2.1 (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hx v)‖ ≤ eps * ‖v‖) →
      n * (n - 1) / 2 + 2 * n ≤ finrank ℝ (fderiv ℝ data.incidence w).range := by
  dsimp only
  let principal := supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
    p.equationColumns p.valueNormals lambda
  have hf := exists_atlas_principal_frame (n := n) (N := N) p himm A hA i hx
    lambda hlambda hne
  obtain ⟨c, e, margin, hmargin, hframe'⟩ := hf
  have htolExists := exists_universal_joint_scaled_rank_tolerance
    (ι := Fin (n * (n - 1) / 2 + n) × Fin 2)
    (k := n * (n - 1) / 2 + 2 * n)
    (X := E) (Y := E)
    (R := Fin p.chart.codim → ℝ) («V» := V)
    (T := SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    principal (p.sourceReferenceDerivative A hA i hx) c e margin hmargin hframe'
  obtain ⟨eps, heps, htol⟩ := htolExists
  refine ⟨eps, heps, ?_⟩
  intro P instP instPR data w hJ dirs hp hs
  exact htol P
    (fun v s ↦ actualSupportedProbeCoordinate F₀ data.map data.smooth data.identification
      A hA i x hx (v, s))
    (fun v s ↦ data.map v ((A.chart i).symm s))
    (fun v s ↦ data.map v ((A.chart data.secondChart).symm s)) p.chart.equation
    data.sigma data.a w.1 w.2.1 w.2.2 hJ dirs hp hs


end SupportedJointWavePacket
end GlobalEmbedding.Upgrade
