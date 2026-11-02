import NormalPolar.OriginalWaveSeedObserverBounds

/-! Complete grouped observation profiles for the actually constructed
original-wave family, on the actual original compact atlas samples. There
are no supplied transition costs or active-sampling coverage assumptions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedFamily

theorem exists_observation_profiles (family : OriginalWaveSeedFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ h, IsCompact (A.support h)) :
    ∃ T P : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < P k) ∧
      ∀ (n j : ℕ) (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ h : Fin A.count,
      Nonempty (JointGroupedPrescribedObservationProfiles
        (fun _ : Z => F) (fun _ => hF)
        (fun l s _ => (family.outer l s).spatialChart.symm)
        (fun l s => (family.refinement l).cutoffCoordinates s)
        (fun l s _ x => (waves l).normal ((family.outer l s).spatialChart.symm x))
        (fun l s => (family.inner l s).chart)
        univ (fun l s => tsupport ((family.refinement l).cutoff s))
        n j ell (family.geometryBudget (max n j)) (family.cutoffBudget n) (family.normalBudget n)
        (fun z : X => (z.1,(A.chart h).symm z.2))
        ((univ : Set Z) ×ˢ (A.chart h).target)
        ((univ : Set Z) ×ˢ ((A.chart h) '' A.support h))
        T (fun l z => weight l * (waves l).phase z.2) (P j)) := by
  obtain ⟨T,P,hpos,hbound⟩ := family.exists_observation_bounds A hA hcompact
  refine ⟨T,P,hpos,?_⟩
  intro n j ell hell hell1 h
  refine ⟨{
    raw := fun l s => family.raw l s n j ell hell hell1
    domains := fun l s => (family.inner l s).observerDomain (A.chart h)
    domains_open := fun l s => (family.inner l s).observerDomain_open _
    active_domain := fun l s => (family.inner l s).observerDomain_active _
    source := fun l s => (family.inner l s).observerDomain_source _
    transition_smooth := fun l s => (family.inner l s).observer_transition_smooth _ (hA.chart_mem _)
    sample := ?_
    transition_jets := ?_
    phase_smooth := fun l s => (family.inner l s).observer_phase_smooth _ (hA.chart_mem _)
    phase_jets := ?_ }⟩
  · intro l s z hz
    rw [family.raw_sample l s n j ell hell hell1]
    exact (family.inner l s).chart.map_source ((family.inner l s).cutoff_support hz.2)
  · intro l s k _ _ z hz
    exact (hbound h l s ell hell hell1 k z hz.1 hz.2).1
  · intro l s k hkj z hz
    exact (hbound h l s ell hell hell1 k z hz.1 hz.2).2 j hkj

end OriginalWaveSeedFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedFamily.exists_observation_profiles

