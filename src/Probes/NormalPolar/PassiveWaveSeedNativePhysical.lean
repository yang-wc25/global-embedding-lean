import NormalPolar.PassiveWaveSeedPhysical
import NormalPolar.PassiveWaveSeedNativeChart

/-! The physical normal-source geometry on a genuine original parameter
chart. This is the actual conjugated chart, with its actual parameter target.
Every spatial inverse, normal, Gram form and phase is the seed object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {S P Ep M : Type*} {m N : ℕ}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def passiveWaveSeed_native_physical (B : OpenPartialHomeomorph P Ep)
    (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
    (c : S → D → M)
    (nu : (s : S) → (x : D) → normalSpace (I := IM) (F s) (c s x))
    (a : OpenPartialHomeomorph (S × M) (S × D)) (phase : S × M → ℝ)
    (geo : ActualPrescribedPhysicalGeometry F hF c nu a phase) :
    ActualPrescribedPhysicalGeometry
      (fun _ : Ep => F 0) (fun _ => hF 0) (fun _ => c 0) (fun _ => nu 0)
      (round3ParameterChartPullback B (passiveParameterChart 0 a))
      (fun z : Ep × M => phase (0,z.2)) := by
  let full := passiveWaveSeed_physical (Ep := Ep) F hF c nu a phase geo
  let an := round3ParameterChartPullback B (passiveParameterChart (P := P) 0 a)
  have ht : an.target ⊆ (passiveParameterChart (P := Ep) 0 a).target :=
    fun z hz => ((passiveWaveSeed_native_target 0 B a z).mp hz).2
  refine {
    slices := full.slices
    maximal := full.maximal
    coordinates := full.coordinates
    target := fun z hz => full.target z (ht hz)
    inverse := ?_
    immersion := fun z hz => full.immersion z (ht hz)
    gram := fun z hz => full.gram z (ht hz)
    normal_kernel := fun z hz => full.normal_kernel z (ht hz)
    adaptation := ?_ }
  · intro z hz
    rw [passiveWaveSeed_native_symm 0 B a z
      ((passiveWaveSeed_native_target 0 B a z).mp hz).1]
    exact full.inverse z (ht hz)
  · intro z hz
    have hs := (passiveWaveSeed_native_source 0 B a z).mp hz
    rw [passiveWaveSeed_native_apply 0 B a z hs.1]
    exact full.adaptation z hs.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_native_physical
