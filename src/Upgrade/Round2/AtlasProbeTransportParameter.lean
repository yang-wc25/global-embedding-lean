import Round2.ProbeBridgeIncidenceParameterSmooth
import Round2.AtlasJetTransfer

/-!
# Actual parameter-response coordinates for changing the probe atlas

The original parameter C¹/C² bounds concern the same native parameter
response field. Its coordinate representatives in any genuine smooth atlas
are smooth on the full open chart target, by joint smoothness of the same
probe geometry. No global smoothness premise for a separate response field
is added when the original atlas norms are transferred.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The literal finite-coordinate representative appearing in
`probeAtlasCj` is smooth on its true open chart domain for every admitted
parameter and every fixed parameter direction. -/
theorem ProbeGeometry.parameter_response_coordinate_smooth
    {F₀ : M → V} {r : ℕ} (g : ProbeGeometry (n := n) F₀ r)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (t : ℝ) (ht : 0 < t) (htt : t < g.threshold)
    (u d : ProbeParameters r) (hu : ‖u‖ < g.radius) :
    ContDiffOn ℝ ∞
      (fun y ↦ (EuclideanSpace.equiv (Fin N) ℝ)
        (fderiv ℝ (fun v ↦ g.map t v
          ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm y))) u d))
      ((EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target) := by
  exact probeAtlas_paper_coordinate_smooth_of_native A
    (fun y ↦ fderiv ℝ (fun v ↦ g.map t v y) u d) i
    (g.atlas_parameter_response_contDiffOn A hA i t ht htt u d hu)

#print axioms ProbeGeometry.parameter_response_coordinate_smooth

end GlobalEmbedding.Upgrade
