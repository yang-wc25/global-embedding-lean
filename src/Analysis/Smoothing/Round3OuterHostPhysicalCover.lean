import Smoothing.Round3OuterHostNormalCover
import Smoothing.ParameterRound2OriginalArgumentContinuity

/-! The genuine host-adapted source cover also covers physical points in
the original forward coordinates. This discharges the physical coverage
condition of the actual normal-rebound stage. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round3_actual_host_physical_cover
    {A : Type*}
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hId : ∀ ip, Data.parameterChart ip = OpenPartialHomeomorph.refl Ep)
    (ip : Fin Data.parameterCount) (domain : Set (Ep × M))
    (host : A → Fin Data.atlas.count) (b : A → OpenPartialHomeomorph X X)
    (hCover : ∀ z ∈ domain, ∃ a, z ∈
      (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source) :
    ∀ z ∈ domain, ∃ i : Fin Data.atlas.count × Fin Data.parameterCount,
      z.1 ∈ (Data.parameterChart i.2).source ∧
      z.2 ∈ (Data.atlas.chart i.1).source ∧
      ∃ a, parameterRound2_originalForwardCoordinates Data i z ∈
        incrementsOriginalDifferentiation Data.atlas Data.parameterChart i ∩
        (incrementsOriginalJointPoint Data.atlas Data.parameterChart i) ⁻¹'
          (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source := by
  intro z hz
  obtain ⟨a,ha⟩ := hCover z hz
  let i : Fin Data.atlas.count × Fin Data.parameterCount := (host a,ip)
  have hp : z.1 ∈ (Data.parameterChart i.2).source := by rw [hId]; exact mem_univ _
  have hx : z.2 ∈ (Data.atlas.chart i.1).source := ha.1.2
  refine ⟨i,hp,hx,a,parameterRound2_originalForward_mem Data i z hp hx,?_⟩
  change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
    (parameterRound2_originalForwardCoordinates Data i z) ∈
      (actualHostAdaptedChart (Data.atlas.chart (host a)) (b a)).source
  rw [parameterRound2_originalForward_left_inv Data i z hp hx]
  exact ha

#print axioms round3_actual_host_physical_cover
end GlobalEmbedding.Continuation
