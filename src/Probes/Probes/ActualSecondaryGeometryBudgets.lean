import Probes.ActualSecondaryQuadraticConstruction

/-! Enlarge the numerical budget of the SAME genuine secondary geometry.
All charts, supports, samples, phases and original geometric expressions
remain definitionally unchanged. Split-scale powers are preserved. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
namespace ActualSecondaryRawGeometry

def enlargeBudget
    {F : Ep → M → V} {hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p)}
    {n j : ℕ} {ell Mg Mg' : ℝ} {W : Set (Ep × M)}
    (data : ActualSecondaryRawGeometry F hF n j ell Mg W) (hMg : Mg ≤ Mg') :
    ActualSecondaryRawGeometry F hF n j ell Mg' W :=
  { data with
    brows_bound := fun i hi z hz => (data.brows_bound i hi z hz).trans hMg
    transverse_bound := fun i hi z hz => (data.transverse_bound i hi z hz).trans hMg
    inverse_bound := fun i hi z hz => (data.inverse_bound i hi z hz).trans hMg
    value_bound := fun i hi z hz => (data.value_bound i hi z hz).trans hMg
    coefficientA_bound := fun i hi z hz => (data.coefficientA_bound i hi z hz).trans hMg
    coefficientB_bound := fun i hi z hz => (data.coefficientB_bound i hi z hz).trans hMg }

end ActualSecondaryRawGeometry
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ActualSecondaryRawGeometry.enlargeBudget
