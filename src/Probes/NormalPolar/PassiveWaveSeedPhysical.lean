import NormalPolar.PassiveWaveSeedChart
import NormalPolar.ParameterDisplacementPrescribedPhysicalCoordinates

/-! Actual physical geometry of a seed wave on the full passive parameter
family. Spatial slices, inverse maps, the original normal, and the adapted
phase are kept literally, including every original legal-wave label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {S Ep M : Type*} {m N : ℕ}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveWaveSeed_physical
    (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
    (c : S → D → M)
    (nu : (s : S) → (x : D) → normalSpace (I := IM) (F s) (c s x))
    (a : OpenPartialHomeomorph (S × M) (S × D)) (phase : S × M → ℝ)
    (geo : ActualPrescribedPhysicalGeometry F hF c nu a phase) :
    ActualPrescribedPhysicalGeometry
      (fun _ : Ep => F 0) (fun _ => hF 0) (fun _ => c 0) (fun _ => nu 0)
      (passiveParameterChart 0 a) (fun z : Ep × M => phase (0,z.2)) := by
  refine {
    slices := fun _ => geo.slices 0
    maximal := fun _ => geo.maximal 0
    coordinates := ?_
    target := fun z hz => geo.target (0,z.2) hz
    inverse := ?_
    immersion := fun z hz => geo.immersion (0,z.2) hz
    gram := fun z hz => geo.gram (0,z.2) hz
    normal_kernel := fun z hz => geo.normal_kernel (0,z.2) hz
    adaptation := fun z hz => geo.adaptation (0,z.2) hz }
  · funext b x
    exact congrFun (congrFun geo.coordinates 0) x
  · intro z hz
    apply Prod.ext
    · rfl
    · change (a.symm (0,z.2)).2 = c 0 z.2
      exact congrArg (fun y : S × M => y.2) (geo.inverse (0,z.2) hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_physical
