import NormalPolar.JointSecondaryPrescribedHostProfiles
import NormalPolar.OriginalWaveSeedRescaledFamily

/-! One finite-host observation sequence for the whole positive contraction
interval. The spatial charts and phases are fixed, and the actual raw family
at each contraction supplies the geometry and rescaled normal unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N r : ℕ} {M Host : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [Fintype Host]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

theorem jointSecondary_prescribed_finite_rescaled_host_profiles
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ h, host h ∈ maximalAtlas IM ∞ M)
    (R : Host → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (host h).target) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) (n j : ℕ) (ell : ℝ),
      0 ≤ ell → ell ≤ 1 → ∀ h : Host,
      Nonempty (JointGroupedPrescribedObservationProfiles
        (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
        (fun l s _ => (family.outer l s).spatialChart.symm)
        (fun l s => (family.refinement l).cutoffCoordinates s)
        (fun l s _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
        (fun l s => (family.inner l s).chart)
        univ (fun l s => tsupport ((family.refinement l).cutoff s))
        n j ell (family.geometryBudget (max n j)) (family.cutoffBudget n) (family.normalBudget n)
        (fun z : X => (z.1,(host h).symm z.2))
        ((univ : Set Z) ×ˢ (host h).target) ((univ : Set Z) ×ˢ R h)
        T (fun l z => weight l * (waves l).phase z.2) (Pphase j)) := by
  have hOne : (1 : ℝ) ∈ Icc (1/2 : ℝ) 1 := ⟨by norm_num,le_rfl⟩
  obtain ⟨T,Pphase,hpos,hprofiles⟩ := jointSecondary_prescribed_finite_host_profiles
    (family.slice 1 hOne) host hhost R hR hRt
  refine ⟨T,Pphase,hpos,?_⟩
  intro c hc n j ell hell hell1 h
  let old := Classical.choice (hprofiles n j ell hell hell1 h)
  refine ⟨{
    raw := fun l s => family.raw c hc l s n j ell hell hell1
    domains := old.domains
    domains_open := old.domains_open
    active_domain := old.active_domain
    source := old.source
    transition_smooth := old.transition_smooth
    sample := ?_
    transition_jets := old.transition_jets
    phase_smooth := old.phase_smooth
    phase_jets := old.phase_jets }⟩
  intro l s z hz
  rw [family.raw_sample c hc l s n j ell hell hell1]
  exact (family.inner l s).chart.map_source
    (old.source l s (old.active_domain l s ⟨⟨hz.1.1,hRt h hz.1.2⟩,hz.2⟩))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_prescribed_finite_rescaled_host_profiles
