import NormalPolar.JointSecondaryFamilyBinding
import NormalPolar.JointSecondarySource

/-! Raw geometric observations on one genuine native parameter chart.

All fields concern the original ambient map, actual mixed charts, original
support sets, their intersections and their coordinate derivatives.  There
is no primary, secondary, forcing, remainder or normalized error estimate.
The parameter space is an arbitrary normed local model; no compactness of
that model or global Euclidean parameter manifold is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M Label Sub : Type*}
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

structure JointMixedNativeObserverGeometry
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (geometry : Rec → Sub → ActualSecondaryRawGeometry F hF n (j+1) ell Mg W)
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
    (K : Label → Set (Ep × M)) (L R : ℕ) (T : ℕ → ℝ) where
  host_maximal : e ∈ maximalAtlas IM ∞ M
  target : ∀ z ∈ Omega, z.2 ∈ e.target
  ambient_smooth : ContDiffOn ℝ ∞ (fun z : X => F z.1 (e.symm z.2)) Omega
  primary_support : ∀ rec a, (geometry rec a).support ⊆
    K rec.val.1.1 ∩ K rec.val.1.2
  transition_smooth : ∀ rec a, ContDiffOn ℝ ∞
    (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (geometry rec a).chart)
    (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (geometry rec a).chart).source
  inverse_smooth : ∀ rec a, ContDiffOn ℝ ∞
    (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (geometry rec a).chart).symm
    (((OpenPartialHomeomorph.refl Ep).prod e).symm.trans (geometry rec a).chart).target
  localDomain : Rec → Sub → Set X
  local_open : ∀ rec a, IsOpen (localDomain rec a)
  local_subset : ∀ rec a, localDomain rec a ⊆ Omega
  active_local : ∀ rec a, S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
    (geometry rec a).support ⊆ localDomain rec a
  source : ∀ rec a, MapsTo (fun z : X => (z.1,e.symm z.2))
    (localDomain rec a) (geometry rec a).chart.source
  active_sample : ∀ rec a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
    (geometry rec a).support → (geometry rec a).chart (z.1,e.symm z.2) ∈ (geometry rec a).sample
  transition_bound : ∀ rec a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹'
    (geometry rec a).support → ∀ k, 1 ≤ k → k ≤ j+2 →
    ell^(k-1)*‖iteratedFDeriv ℝ k
      ((geometry rec a).chart ∘ (fun z : X => (z.1,e.symm z.2))) z‖ ≤ T k
  primary_count : ∀ z ∈ S,
    (Finset.univ.filter (fun l => (z.1,e.symm z.2) ∈ K l)).card ≤ L
  secondary_count : ∀ rec : Rec, ∀ z ∈ S,
    (Finset.univ.filter (fun a => (z.1,e.symm z.2) ∈ (geometry rec a).support)).card ≤ R

theorem JointMixedNativeObserverGeometry.local_transition_smooth
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (geometry : Rec → Sub → ActualSecondaryRawGeometry F hF n (j+1) ell Mg W)
    (e : OpenPartialHomeomorph M D) (Omega S : Set X)
    (K : Label → Set (Ep × M)) (L R : ℕ) (T : ℕ → ℝ)
    (raw : JointMixedNativeObserverGeometry F hF n j ell Mg W geometry e Omega S K L R T)
    (rec : Rec) (a : Sub) :
    ContDiffOn ℝ ∞ ((geometry rec a).chart ∘ (fun z : X => (z.1,e.symm z.2)))
      (raw.localDomain rec a) := by
  apply (raw.transition_smooth rec a).mono
  intro z hz
  exact ⟨⟨mem_univ _,raw.target z (raw.local_subset rec a hz)⟩,raw.source rec a hz⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.JointMixedNativeObserverGeometry.local_transition_smooth
