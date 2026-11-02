import NormalPolar.JointMixedNativeObservation
import Probes.ActualSecondaryGeometryBudgets

/-! Combining primitive bounds changes no observer map, source, support,
sampling set, local neighborhood or overlap count. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Label Sub : Type*} {m N : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord Label

def JointMixedNativeObserverGeometry.enlargeBudget
    {F : Ep → M → V} {hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b)}
    {n j : ℕ} {ell Mg : ℝ} {W : Set (Ep × M)}
    {geometry : Rec → Sub → ActualSecondaryRawGeometry F hF n (j+1) ell Mg W}
    {e : OpenPartialHomeomorph M D} {Omega S : Set X}
    {K : Label → Set (Ep × M)} {L R : ℕ} {T : ℕ → ℝ}
    (raw : JointMixedNativeObserverGeometry F hF n j ell Mg W geometry e Omega S K L R T)
    {Mg' : ℝ} (hMg : Mg ≤ Mg') :
    JointMixedNativeObserverGeometry F hF n j ell Mg' W
      (fun rec a => (geometry rec a).enlargeBudget hMg) e Omega S K L R T where
  host_maximal := raw.host_maximal
  target := raw.target
  ambient_smooth := raw.ambient_smooth
  primary_support := raw.primary_support
  transition_smooth := raw.transition_smooth
  inverse_smooth := raw.inverse_smooth
  localDomain := raw.localDomain
  local_open := raw.local_open
  local_subset := raw.local_subset
  active_local := raw.active_local
  source := raw.source
  active_sample := raw.active_sample
  transition_bound := raw.transition_bound
  primary_count := raw.primary_count
  secondary_count := raw.secondary_count

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointMixedNativeObserverGeometry.enlargeBudget
