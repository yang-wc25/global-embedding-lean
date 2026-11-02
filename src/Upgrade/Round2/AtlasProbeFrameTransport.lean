import Round2.AtlasProbeFrameGeometry
import Upgrade.SupportedProbeJointSmooth

/-!
# The same actual full-probe response in another source atlas

Only the source frame is changed.  The map, its native parameter derivative,
the actual identified true form, the chosen Q, and the legal-wave principal
are all unchanged.  The transition is fixed when parameter differentiation
is performed, so no fast-angle coefficient is differentiated.
-/

noncomputable section
open Function Filter Manifold Set
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

/-- Literal tensor transport by the real transition of the two source
charts, on the same original symmetric-square quotient. -/
theorem probeTensorInFrame_change_atlas
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count)
    (z : M) (hzA : z ∈ (A.chart i).source) (hzB : z ∈ (B.chart j).source)
    (T : SymmetricSquare E →L[ℝ] V) :
    probeTensorInFrame (probeAtlasFrame B j z) T =
      (probeTensorInFrame (probeAtlasFrame A i z) T).comp
        (atlasProbeTransitionSquare A B i j z) := by
  rw [probeAtlasFrame_change_atlas A B hA hB i j z hzA hzB]
  apply ContinuousLinearMap.ext
  intro q
  change T (symmetricSquareLinearMap
      ((probeAtlasFrame A i z).comp
        (fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z))).toLinearMap q) =
    T (symmetricSquareLinearMap (probeAtlasFrame A i z).toLinearMap
      (symmetricSquareLinearMap
        (fderiv ℝ (atlasProbeTransition A B i j) (B.chart j z)).toLinearMap q))
  rw [symmetric_square_linear_map_eq, symmetric_square_linear_map_eq,
    symmetric_square_linear_map_eq, symmetricSquareMap_comp]

/-- The native parameter derivative of the SAME actual identified true form
in B coordinates is the already differentiated A response right-composed
with the actual fixed transition square. -/
theorem ProbeGeometry.actual_secondForm_parameter_derivative_change_atlas
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count)
    (z : M) (hzA : z ∈ (A.chart i).source) (hzB : z ∈ (B.chart j).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) :
    fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame B j z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d =
      (fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d).comp
        (atlasProbeTransitionSquare A B i j z) := by
  simp only [probeTensorInFrame_change_atlas A B hA hB i j z hzA hzB]
  exact fderiv_fixed_tensor_right_transport _
    (g.identified_trueSecondForm_parameter_differentiable A hA i t ht htt u hu z hzA)
    (atlasProbeTransitionSquare A B i j z) d

/-- The whole actual second-form response remainder, including global repair
tails, is transported.  The principal is the same actual local legal wave;
no derivative of the chosen scalar coefficient is introduced. -/
theorem ProbeGeometry.actual_secondForm_parameter_error_change_atlas
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {r : ℕ}
    (g : ProbeGeometry (n := n) F₀ r) (wave : LocalLegalWave F₀ hF₀)
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B) (i : Fin A.count) (j : Fin B.count)
    (z : M) (hzA : z ∈ (A.chart i).source) (hzB : z ∈ (B.chart j).source)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) (coefficient : ℝ) :
    ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame B j z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
      coefficient • probeTensorInFrame (probeAtlasFrame B j z) (wave.tensor z)‖ ≤
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ *
          ‖atlasProbeTransitionSquare A B i j z‖ := by
  simp only [probeTensorInFrame_change_atlas A B hA hB i j z hzA hzB]
  exact fixed_tensor_right_transport_error _
    (g.identified_trueSecondForm_parameter_differentiable A hA i t ht htt u hu z hzA)
    (atlasProbeTransitionSquare A B i j z) d coefficient
    (probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z))

/-- One geometric constant transports the actual parameter response at every
B-support point from the covering A supports.  It is chosen before F₀, the
actual probe family, the wave, parameter, direction, coefficient and error.
No nonemptiness, orientation or connectedness hypothesis is required. -/
theorem exists_uniform_actual_probe_response_atlas_transfer [T2Space M]
    (A B : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hB : IsSmoothBufferedAtlas B)
    (hAc : ∀ i, IsCompact (A.support i))
    (hBc : ∀ j, IsCompact (B.support j))
    (hcoverA : ∀ z : M, ∃ i, z ∈ A.support i) :
    ∃ R : ℝ, 0 < R ∧ ∀ (F₀ : M → V)
      (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀) (r : ℕ)
      (g : ProbeGeometry (n := n) F₀ r) (wave : LocalLegalWave F₀ hF₀)
      (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
      (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) (coefficient error : ℝ)
      (j : Fin B.count) (z : M), z ∈ B.support j →
      (∀ i : Fin A.count, z ∈ A.support i →
        ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame A i z)
          (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
            (g.normalIdentification t v) z)) u d -
          coefficient • probeTensorInFrame (probeAtlasFrame A i z) (wave.tensor z)‖ ≤ error) →
      ‖fderiv ℝ (fun v ↦ probeTensorInFrame (probeAtlasFrame B j z)
        (identifiedTrueSecondForm (n := n) F₀ (g.map t v) (g.slice_smooth t v)
          (g.normalIdentification t v) z)) u d -
        coefficient • probeTensorInFrame (probeAtlasFrame B j z) (wave.tensor z)‖ ≤ R * error := by
  obtain ⟨R, hR, hbound⟩ :=
    exists_uniform_atlasProbeTransitionSquare_bound A B hA hB hAc hBc
  refine ⟨R, hR, ?_⟩
  intro F₀ hF₀ r g wave t ht htt u d hu coefficient error j z hzB herror
  obtain ⟨i, hzA⟩ := hcoverA z
  have herr := herror i hzA
  have hepos : 0 ≤ error := (norm_nonneg _).trans herr
  have htransport := g.actual_secondForm_parameter_error_change_atlas wave
    A B hA hB i j z (hA.support_subset i hzA) (hB.support_subset j hzB)
    t ht htt u d hu coefficient
  exact htransport.trans ((mul_le_mul herr (hbound i j z hzB hzA)
    (norm_nonneg _) hepos).trans_eq (mul_comm error R))

#print axioms probeTensorInFrame_change_atlas
#print axioms ProbeGeometry.actual_secondForm_parameter_derivative_change_atlas
#print axioms ProbeGeometry.actual_secondForm_parameter_error_change_atlas
#print axioms exists_uniform_actual_probe_response_atlas_transfer

end GlobalEmbedding.Upgrade
