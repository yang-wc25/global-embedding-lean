import NormalPolar.JointSecondaryPrescribedRescaledHost
import NormalPolar.PassiveWaveSeedObservation

/-! Actual grouped prescribed raw data at every additional secondary host,
in any true parameter chart. Compact spatial host samples determine all
costs before contraction, parameters, orders and ell. The caller may use the
actual open secondary transition domain and its actual inverse-image sample;
only geometric inclusion in the already bounded sample is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.NormalPolar
variable {m N r : ℕ} {M Host P Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M] [Fintype Host]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

theorem jointSecondary_prescribed_finite_native_host_profiles
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (host : Host → OpenPartialHomeomorph M D)
    (hhost : ∀ h, host h ∈ maximalAtlas IM ∞ M)
    (R : Host → Set D) (hR : ∀ h, IsCompact (R h))
    (hRt : ∀ h, R h ⊆ (host h).target) :
    ∃ T Pphase : ℕ → ℝ, (∀ k, 0 < T k ∧ 0 < Pphase k) ∧
      ∀ (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) (n j : ℕ) (ell : ℝ),
      0 ≤ ell → ell ≤ 1 → ∀ (h : Host) (B : OpenPartialHomeomorph P Ep)
      (Omega Sn : Set X), Omega ⊆ B.target ×ˢ (host h).target →
      (∀ z ∈ Sn, z.1 ∈ B.target) → (∀ z ∈ Sn, z.2 ∈ R h) →
      Nonempty (JointGroupedPrescribedObservationProfiles
        (fun _ : Ep => c • F) (fun _ => contMDiff_const_rescale F hF c)
        (fun l s _ => (family.outer l s).spatialChart.symm)
        (fun l s (z : X) => (family.refinement l).cutoffCoordinates s (0,z.2))
        (fun l s _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
          ((family.outer l s).spatialChart.symm x)
          ((waves l).normal ((family.outer l s).spatialChart.symm x)))
        (fun l s => round3ParameterChartPullback B
          (passiveParameterChart (0 : Z) (family.inner l s).chart))
        {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ (univ : Set (Z × M))}
        (fun l s => {z : Ep × M | z.1 ∈ B.target ∧
          (0,z.2) ∈ tsupport ((family.refinement l).cutoff s)})
        n j ell (family.geometryBudget (max n j)) (family.cutoffBudget n) (family.normalBudget n)
        (fun z : X => (z.1,(host h).symm z.2)) Omega Sn
        T (fun l z => weight l * (waves l).phase z.2) (Pphase j)) := by
  obtain ⟨T,Pphase,hpos,hprofiles⟩ := jointSecondary_prescribed_finite_rescaled_host_profiles
    family host hhost R hR hRt
  refine ⟨fun k => 1+T k,Pphase,fun k => ⟨by linarith [(hpos k).1],(hpos k).2⟩,?_⟩
  intro c hc n j ell hell hell1 h B Omega Sn hOmega hSnB hSnR
  obtain ⟨profiles⟩ := hprofiles c hc n j ell hell hell1 h
  have out := passiveWaveSeed_observation B (host h)
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun l s _ => (family.outer l s).spatialChart.symm)
    (fun l s => (family.refinement l).cutoffCoordinates s)
    (fun l s _ x => actualRescaledNormal F hF c (originalWave_contraction_ne_zero c hc)
      ((family.outer l s).spatialChart.symm x)
      ((waves l).normal ((family.outer l s).spatialChart.symm x)))
    (fun l s => (family.inner l s).chart) univ
    (fun l s => tsupport ((family.refinement l).cutoff s))
    n j ell (family.geometryBudget (max n j)) (family.cutoffBudget n) (family.normalBudget n)
    hell ((univ : Set Z) ×ˢ (host h).target) ((univ : Set Z) ×ˢ R h)
    (fun z hz => ⟨mem_univ _,hRt h hz.2⟩) T (fun k => (hpos k).1.le)
    (fun l z => weight l * (waves l).phase z.2) (Pphase j) profiles
    Sn hSnB (fun z hz => ⟨mem_univ _,hSnR z hz⟩)
  have hdomain : {z : X | z.1 ∈ B.target ∧
      (0,z.2) ∈ ((univ : Set Z) ×ˢ (host h).target)} = B.target ×ˢ (host h).target := by
    ext z
    simp only [mem_setOf_eq,mem_prod,mem_univ,true_and]
  rw [hdomain] at out
  exact ⟨{
    raw := out.raw
    domains := out.domains
    domains_open := out.domains_open
    active_domain := fun l s z hz => out.active_domain l s ⟨hOmega hz.1,hz.2⟩
    source := out.source
    transition_smooth := out.transition_smooth
    sample := out.sample
    transition_jets := out.transition_jets
    phase_smooth := out.phase_smooth
    phase_jets := out.phase_jets }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_prescribed_finite_native_host_profiles
