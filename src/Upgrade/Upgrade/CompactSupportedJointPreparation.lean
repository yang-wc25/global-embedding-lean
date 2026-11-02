import Upgrade.CompactSupportedEquationBall
import Upgrade.CompactNormalizedTensors
import Upgrade.IncidenceSupportedTolerance
import Upgrade.RankQFixedWeightSimulation

/-!
# The supported-coincidence cover is prepared with fixed weights

The actual common q+n wave packet yields the actual q+2n principal frame.
Weights 1 and 2 are fixed before the frame, its error budget, the actual
supported-equation derivative ball, and the spatial neighborhood. Returned
weights later simulate these same columns. In dimension three the operation
removes joint supported coincidences while allowing surviving kernels.
-/

noncomputable section
open Set Filter Bundle Manifold Module GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators

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

theorem SupportedJointWavePacket.principalColumn_eq_actual
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : SupportedJointWavePacket F hF x y)
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (l : Fin (n * (n - 1) / 2 + n) × Fin 2) :
    supportedJointPrincipalColumn (incidenceActualTangent (n := n) F x)
      packet.equationColumns packet.valueNormals lambda l =
      (fderiv ℝ packet.chart.equation
        (LinearMap.toContinuousLinearMap
          (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x))
        ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((packet.waves l.1).tensor x)),
      -(lambda l.1 l.2 ^ 2)⁻¹ • (packet.waves l.1).value x) := by
  apply Prod.ext
  · rfl
  · have hp : ((normalSpace (I := IM) F x).orthogonalProjectionOnto
        ((packet.waves l.1).value x) : V) = (packet.waves l.1).value x :=
      Submodule.starProjection_eq_self_iff.mpr ((packet.waves l.1).value_mem_normal x)
    exact congrArg (fun v : V ↦ -(lambda l.1 l.2 ^ 2)⁻¹ • v) hp

structure SupportedJointPreparedNeighborhood
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : SupportedJointWavePacket F hF x y)
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) where
  coefficients : Fin (n * (n - 1) / 2 + 2 * n) →
    (Fin (n * (n - 1) / 2 + n) × Fin 2) → ℝ
  sourceDirections : Fin (n * (n - 1) / 2 + 2 * n) → E
  margin : ℝ
  margin_pos : 0 < margin
  frame_lower : ∀ b : Fin (n * (n - 1) / 2 + 2 * n) → ℝ,
    margin * ‖b‖ ≤ ‖∑ j, b j •
      ((∑ l, coefficients j l •
        supportedJointPrincipalColumn (incidenceActualTangent (n := n) F x)
          packet.equationColumns packet.valueNormals rankQPreparationWeights l) +
        (0, packet.sourceReferenceDerivative A hA i
          (hA.support_subset i (interior_subset hx)) (sourceDirections j)))‖
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  coefficient_budget : ∀ j,
    (Fintype.card (Fin (n * (n - 1) / 2 + n) × Fin 2) : ℝ) *
        tolerance * ‖coefficients j‖ + tolerance * ‖sourceDirections j‖ ≤
      margin / (2 * ((n * (n - 1) / 2 + 2 * n : ℕ) + 1 : ℝ))
  tensorBound : ℝ
  tensorBound_pos : 0 < tensorBound
  derivativeTolerance : ℝ
  derivativeTolerance_pos : 0 < derivativeTolerance
  derivative_budget : derivativeTolerance * tensorBound ≤ tolerance / 4
  formBall : PreparedSupportedEquationBall packet.chart derivativeTolerance
  neighborhood : Set (M × M)
  neighborhood_open : IsOpen neighborhood
  center_mem : (x, y) ∈ neighborhood
  support : ∀ z ∈ neighborhood, z.1 ∈ interior (A.support i)
  cutoff : ∀ z ∈ neighborhood, ∀ l,
    (packet.waves l).cutoff z.1 = 1 ∧ (packet.waves l).cutoff z.2 = 0
  principal_variation : ∀ z ∈ neighborhood, ∀ l : Fin (n * (n - 1) / 2 + n) × Fin 2,
    ‖atlasIncidencePrincipal (packet.waves l.1) A hA i x
        (hA.support_subset i (interior_subset hx))
        (normalSpace (I := IM) F x).orthogonalProjectionOnto
        (fderiv ℝ packet.chart.equation
          (LinearMap.toContinuousLinearMap
            (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)))
        (rankQPreparationWeights l.1 l.2) (A.chart i z.1) -
      supportedJointPrincipalColumn (incidenceActualTangent (n := n) F x)
        packet.equationColumns packet.valueNormals rankQPreparationWeights l‖ < tolerance / 4
  source_variation : ∀ z ∈ neighborhood,
    ‖probeAtlasFirstJet A F i z.1 - probeAtlasFirstJet A F i x‖ < tolerance / 4
  tensor_bound : ∀ z ∈ neighborhood, ∀ l,
    ‖(normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
        (probeTensorInFrame
          (probeAtlasNormalizedFrame A hA i x (hA.support_subset i (interior_subset hx)) z.1)
          ((packet.waves l).tensor z.1))‖ ≤ tensorBound
  reference_variation : ∀ z ∈ neighborhood,
    ‖normalizedReferenceForm A hA F i x (hA.support_subset i (interior_subset hx)) z.1 -
      LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)‖ <
      formBall.radius / 2
  normal_gap : ∀ z ∈ neighborhood,
    ‖(normalSpace (I := IM) F z.1).starProjection -
      (normalSpace (I := IM) F x).starProjection‖ < 1 / 2

theorem SupportedJointWavePacket.exists_prepared_neighborhood [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (packet : SupportedJointWavePacket F hF x y)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (i : Fin A.count) (hx : x ∈ interior (A.support i)) :
    Nonempty (SupportedJointPreparedNeighborhood A hA packet i hx) := by
  classical
  let hxc := hA.support_subset i (interior_subset hx)
  obtain ⟨c, e, margin, hm, hframe⟩ := packet.exists_atlas_principal_frame (himm x) A hA i hxc
    rankQPreparationWeights rankQPreparationWeights_pos rankQPreparationWeights_ne
  obtain ⟨C, hC⟩ := Finite.exists_le (fun j : Fin (n * (n - 1) / 2 + 2 * n) ↦
    (Fintype.card (Fin (n * (n - 1) / 2 + n) × Fin 2) : ℝ) * ‖c j‖ + ‖e j‖)
  let b := margin / (2 * ((n * (n - 1) / 2 + 2 * n : ℕ) + 1 : ℝ))
  have hb : 0 < b := div_pos hm (by positivity)
  let eps := b / (|C| + 1)
  have heps : 0 < eps := div_pos hb (by positivity)
  have hbudget (j : Fin (n * (n - 1) / 2 + 2 * n)) :
      (Fintype.card (Fin (n * (n - 1) / 2 + n) × Fin 2) : ℝ) * eps * ‖c j‖ +
        eps * ‖e j‖ ≤ b := by
    calc
      _ = eps * ((Fintype.card (Fin (n * (n - 1) / 2 + n) × Fin 2) : ℝ) * ‖c j‖ + ‖e j‖) := by ring
      _ ≤ eps * (|C| + 1) := mul_le_mul_of_nonneg_left
        ((hC j).trans ((le_abs_self C).trans (by linarith))) heps.le
      _ = b := div_mul_cancel₀ b (by positivity : |C| + 1 ≠ 0)
  obtain ⟨U, hU, hxU, hUsupport, hprincipal, hsource⟩ :=
    exists_actual_principal_source_neighborhood
      (fun l : Fin (n * (n - 1) / 2 + n) × Fin 2 ↦ packet.waves l.1) A hA i x hx
      (normalSpace (I := IM) F x).orthogonalProjectionOnto
      (fderiv ℝ packet.chart.equation
        (LinearMap.toContinuousLinearMap
          (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x)))
      (fun l ↦ rankQPreparationWeights l.1 l.2) (show 0 < eps / 4 by positivity)
  obtain ⟨L, hL, Ub, hUb, hxUb, _, hbound⟩ :=
    exists_finite_normalized_tensor_bound packet.waves A hA i x hx
  let delta := eps / (4 * (L + 1))
  have hdelta : 0 < delta := div_pos heps (by positivity)
  have hDbudget : delta * L ≤ eps / 4 := by
    have heq : delta * (L + 1) = eps / 4 := by
      dsimp only [delta]
      field_simp
    nlinarith [hdelta.le]
  obtain ⟨ball⟩ := exists_prepared_supported_equation_ball packet.chart hdelta
  obtain ⟨Ur, hUr, hxUr, _, hreference, hnormal⟩ :=
    exists_normalizedReference_neighborhood A hA F hF himm i x hx
      (show 0 < ball.radius / 2 by positivity [ball.radius_pos])
  obtain ⟨Ucut, hUcutsub, hUcut, hxUcut⟩ := mem_nhds_iff.mp packet.one_near
  obtain ⟨Wcut, hWcutsub, hWcut, hyWcut⟩ := mem_nhds_iff.mp packet.zero_near
  refine ⟨{
    coefficients := c
    sourceDirections := e
    margin := margin
    margin_pos := hm
    frame_lower := hframe
    tolerance := eps
    tolerance_pos := heps
    coefficient_budget := hbudget
    tensorBound := L
    tensorBound_pos := hL
    derivativeTolerance := delta
    derivativeTolerance_pos := hdelta
    derivative_budget := hDbudget
    formBall := ball
    neighborhood := (((U ∩ Ub) ∩ Ur) ∩ Ucut) ×ˢ Wcut
    neighborhood_open := (((hU.inter hUb).inter hUr).inter hUcut).prod hWcut
    center_mem := ⟨⟨⟨⟨hxU, hxUb⟩, hxUr⟩, hxUcut⟩, hyWcut⟩
    support := fun z hz ↦ hUsupport hz.1.1.1.1
    cutoff := fun z hz l ↦ ⟨hUcutsub hz.1.2 l, hWcutsub hz.2 l⟩
    principal_variation := ?_
    source_variation := fun z hz ↦ hsource z.1 hz.1.1.1.1
    tensor_bound := fun z hz l ↦ hbound z.1 hz.1.1.1.2 l
    reference_variation := fun z hz ↦ hreference z.1 hz.1.1.2
    normal_gap := fun z hz ↦ hnormal z.1 hz.1.1.2 }⟩
  intro z hz l
  rw [packet.principalColumn_eq_actual]
  exact hprincipal z.1 hz.1.1.1.1 l

end GlobalEmbedding.Upgrade
