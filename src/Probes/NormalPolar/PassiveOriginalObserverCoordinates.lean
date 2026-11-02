import Probes.Round3ParameterObserverChartProfiles
import Smoothing.ParameterRound2OriginalHostArgument

/-! Actual coordinates of a new spatial observer in one unchanged original
chart. Both the overlap and the original parameter target remain explicit.
Compactness of a geometric sample produces every transition constant before
the derivative scale or tensor input is selected. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m d count : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

def passiveOriginalObserverDomain (B : OpenPartialHomeomorph P Ep)
    (e host : OpenPartialHomeomorph M D) : Set X :=
  B.target ×ˢ (host.symm.trans e).source

def passiveOriginalObserverCoordinates (e host : OpenPartialHomeomorph M D) :
    X → Fin (m+1+d) → ℝ :=
  fun z => parameterTensorModelEquiv (m+1) d (z.1,e (host.symm z.2))

theorem passiveOriginalObserverDomain_open (B : OpenPartialHomeomorph P Ep)
    (e host : OpenPartialHomeomorph M D) :
    IsOpen (passiveOriginalObserverDomain B e host) :=
  B.open_target.prod (host.symm.trans e).open_source

theorem passiveOriginalObserverCoordinates_smooth
    (B : OpenPartialHomeomorph P Ep) (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (passiveOriginalObserverCoordinates e host)
      (passiveOriginalObserverDomain B e host) := by
  have ht : ContDiffOn ℝ ∞ (e ∘ host.symm) (host.symm.trans e).source :=
    ((contMDiffOn_of_mem_maximalAtlas he).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hh).mono (fun z hz => hz.1))
      (fun z hz => hz.2)).contDiffOn
  have hp : ContDiffOn ℝ ∞ (fun z : X => (z.1,e (host.symm z.2)))
      (passiveOriginalObserverDomain B e host) :=
    contDiffOn_fst.prodMk (ht.comp contDiffOn_snd (fun z hz => hz.2))
  exact (parameterTensorModelEquiv (m+1) d).contDiff.comp_contDiffOn hp

theorem passiveOriginalObserverCoordinates_point
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (i : Fin A.count × Fin count) (host : OpenPartialHomeomorph M D)
    (z : X) (hz : z ∈ passiveOriginalObserverDomain (B i.2) (A.chart i.1) host) :
    incrementsOriginalJointPoint A B i (passiveOriginalObserverCoordinates (A.chart i.1) host z) =
      ((B i.2).symm z.1,host.symm z.2) := by
  change ((B i.2).symm (((parameterTensorModelEquiv (m+1) d).symm
      (parameterTensorModelEquiv (m+1) d (z.1,(A.chart i.1) (host.symm z.2)))).1),
    (A.chart i.1).symm (((parameterTensorModelEquiv (m+1) d).symm
      (parameterTensorModelEquiv (m+1) d (z.1,(A.chart i.1) (host.symm z.2)))).2)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact Prod.ext rfl ((A.chart i.1).left_inv hz.2.2)

theorem passiveOriginalObserverCoordinates_target
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (i : Fin A.count × Fin count) (host : OpenPartialHomeomorph M D) :
    MapsTo (passiveOriginalObserverCoordinates (A.chart i.1) host)
      (passiveOriginalObserverDomain (B i.2) (A.chart i.1) host)
      (incrementsOriginalDifferentiation A B i) := by
  intro z hz
  change ((parameterTensorModelEquiv (m+1) d).symm
      (parameterTensorModelEquiv (m+1) d (z.1,(A.chart i.1) (host.symm z.2)))).2 ∈
        (A.chart i.1).target ∧
    ((parameterTensorModelEquiv (m+1) d).symm
      (parameterTensorModelEquiv (m+1) d (z.1,(A.chart i.1) (host.symm z.2)))).1 ∈ (B i.2).target
  simpa only [ContinuousLinearEquiv.symm_apply_apply,OpenPartialHomeomorph.symm_symm] using
    And.intro ((A.chart i.1).map_source hz.2.2) hz.1

theorem passiveOriginalObserverCoordinates_compact_profiles
    (B : OpenPartialHomeomorph P Ep) (e host : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (hh : host ∈ maximalAtlas IM ∞ M)
    (R : Set X) (hR : IsCompact R) (hRO : R ⊆ passiveOriginalObserverDomain B e host) :
    ∃ T : ℕ → ℝ, (∀ k, 0 ≤ T k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ k z, z ∈ R →
        ell^(k-1)*‖iteratedFDeriv ℝ k (passiveOriginalObserverCoordinates e host) z‖ ≤ T k := by
  obtain ⟨T,hT,hb⟩ := round3_prepared_compact_profiles
    (passiveOriginalObserverCoordinates e host) (passiveOriginalObserverDomain B e host) R
    (passiveOriginalObserverDomain_open B e host) hR hRO
    (passiveOriginalObserverCoordinates_smooth B e host he hh)
  exact ⟨T,hT,fun ell he he1 k z hz => (hb ell he he1 k z hz).2⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginalObserverCoordinates_point
#print axioms GlobalEmbedding.Continuation.passiveOriginalObserverCoordinates_compact_profiles
