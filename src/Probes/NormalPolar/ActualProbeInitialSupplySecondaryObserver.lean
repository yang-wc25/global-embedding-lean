import NormalPolar.ActualProbeInitialSupplySecondaryAffine
import NormalPolar.JointMixedNativeObservation

/-! The native observer of the actual carrier construction supplies the
low-level physical secondary observation. Only primitive source identities
are used; no complete-wave derivative or response is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m N n j : ℕ} {Ep M Label Sub : Type*}
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

def actualProbeInitialSupply_secondary_observation
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (ell Mg CH delta : ℝ) (W : Set (Ep × M))
    (geometry : Rec → Sub → ActualSecondaryRawGeometry F hF n (j+1) ell Mg W)
    (e : OpenPartialHomeomorph M D) (OmegaOld S : Set X)
    (K : Label → Set (Ep × M)) (L Rcount : ℕ) (T : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k)
    (raw : JointMixedNativeObserverGeometry F hF n j ell Mg W geometry e OmegaOld S K L Rcount T)
    (data : Rec → Sub → ActualSecondaryPhysicalPieceData F hF n (j+1) ell Mg CH delta W)
    (hchart : ∀ rec s, (data rec s).base.chart = (geometry rec s).chart)
    (hsupport : ∀ rec s, (data rec s).base.support = (geometry rec s).support)
    (hsample : ∀ rec s, (data rec s).base.sample = (geometry rec s).sample)
    (Omega : Set X) (hO : IsOpen Omega) (hSO : S ⊆ Omega)
    (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
    (hWmap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W) :
    ActualSecondaryProbeObservation F hF data X where
  kappa := fun z => (z.1,e.symm z.2)
  domain := Omega
  sample := S
  domain_open := hO
  sample_subset := hSO
  smooth := by
    have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1) Omega :=
      contDiffOn_fst.contMDiffOn
    have hs : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ (fun z : X => z.2) Omega :=
      contDiffOn_snd.contMDiffOn
    exact hf.prodMk ((contMDiffOn_symm_of_mem_maximalAtlas raw.host_maximal).comp hs hTarget)
  mapsTo := hWmap
  primarySupport := K
  primary_support := fun rec s => by rw [hsupport]; exact raw.primary_support rec s
  localDomain := raw.localDomain
  local_open := raw.local_open
  active_local := fun rec s => by rw [hsupport]; exact raw.active_local rec s
  source := fun rec s => by rw [hchart]; exact raw.source rec s
  transition_smooth := fun rec s => by
    rw [hchart]
    exact raw.local_transition_smooth F hF n j ell Mg W geometry e OmegaOld S K L Rcount T rec s
  transitionCost := T
  transitionCost_nonneg := hT
  active_sample := fun rec s z hz => by
    rw [hchart,hsample]
    exact raw.active_sample rec s z (by simpa only [hsupport] using hz)
  transition_bound := fun rec s z hz k hk hkj => by
    rw [hchart]
    exact raw.transition_bound rec s z (by simpa only [hsupport] using hz) k hk (by omega)
  primaryCount := L
  secondaryCount := Rcount
  primary_count := raw.primary_count
  secondary_count := fun rec z hz => by
    simpa only [hsupport] using raw.secondary_count rec z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_secondary_observation
