import Smoothing.Round3OuterStablePrimaryFamily
import Smoothing.Round3OuterParameterFixedReferenceProfiles

/-! The actual stable global primary family retains complete original
geometry and exactly the fixed reference observer profiles. Only chart
domains change. This is the interface used before constructing the new
intrinsic normal; g still carries the genuine reference normal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_stable_primary_global_geometry_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (R : ℕ) (hPart : ∀ z, ∑ i, theta i z = 1)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ R)
    (Forward Inverse Meta : ℕ → ℝ)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :
    let g0 := round3ParameterWholePrimaryFamily Ref hd hs hn theta (round3OuterReferencePrimaryPacket Ref hd hs theta packet profiles)
    let g := round3ParameterWholePrimaryFamily Ref hd hs hn theta (round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable)
    Round3ParameterOriginalChartProfiles Ref g0 Forward Inverse Meta →
    Round3ParameterOriginalPrimaryGeometry Ref g (R*5^Module.finrank ℝ (Ep × D)) ∧
      Round3ParameterOriginalChartProfiles Ref g Forward Inverse Meta := by
  intro g0 g hProfile
  have hFunctions := round3_stable_primary_global_functions Ref hd hs hn theta packet profiles F hF stable
  let p := round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable
  have hg : Round3ParameterOriginalPrimaryGeometry Ref g (R*5^Module.finrank ℝ (Ep × D)) :=
    round3Parameter_whole_primary_family_geometry Ref hd hs hn theta p hPart R hCount
  refine ⟨hg,?_⟩
  exact round3Parameter_original_profiles_stage_rebase Ref hd g0 Forward Inverse Meta hProfile
    Ref.F Ref.H Ref.parameterOpen Ref.freeNormal Ref.primaryDomain Ref.tensorNeighborhood
    g _ hg hFunctions.1 hFunctions.2.1 hFunctions.2.2.1

#print axioms round3_stable_primary_global_geometry_profiles
end GlobalEmbedding.Continuation
