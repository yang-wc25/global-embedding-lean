import NormalPolar.OriginalWaveSeedObservationProfiles

/-! Preserve arbitrary original compact coordinate sampling sets. The
auxiliary support used solely to prove a bound is the actual inverse image
of that same sample, and its chart image is proved to be exactly the original
sample. No norm domain or differentiation domain is changed. -/

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
local notation "X" => Z × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedFamily

theorem exists_observation_profiles_samples (family : OriginalWaveSeedFamily F hF waves weight)
    (A : BufferedAtlas M D) (hA : IsSmoothBufferedAtlas A)
    (R : Fin A.count → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (A.chart h).target) :
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
        ((univ : Set Z) ×ˢ R h)
        T (fun l z => weight l * (waves l).phase z.2) (P j)) := by
  let A' : BufferedAtlas M D := { A with support := fun h => (A.chart h).symm '' R h }
  have hA' : IsSmoothBufferedAtlas A' := {
    chart_mem := hA.chart_mem
    support_subset := by
      intro h x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact (A.chart h).map_target (hRt h hy) }
  have hcompact (h : Fin A'.count) : IsCompact (A'.support h) :=
    (hR h).image_of_continuousOn ((A.chart h).symm.continuousOn.mono (hRt h))
  have himage (h : Fin A'.count) : (A'.chart h) '' A'.support h = R h := by
    change (A.chart h) '' ((A.chart h).symm '' R h) = R h
    ext y
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      simpa only [(A.chart h).right_inv (hRt h hz)] using hz
    · intro hy
      exact ⟨(A.chart h).symm y,⟨y,hy,rfl⟩,(A.chart h).right_inv (hRt h hy)⟩
  obtain ⟨T,P,hpos,hprofiles⟩ := family.exists_observation_profiles A' hA' hcompact
  refine ⟨T,P,hpos,?_⟩
  intro n j ell hell hell1 h
  simpa only [himage h] using hprofiles n j ell hell hell1 h

end OriginalWaveSeedFamily
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedFamily.exists_observation_profiles_samples

