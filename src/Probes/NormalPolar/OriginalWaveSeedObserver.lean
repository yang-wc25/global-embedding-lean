import NormalPolar.OriginalWaveSeedFamily
import NormalPolar.JointSecondaryGroupedProfiles

/-! Actual local observation domains and compact active samples for each
constructed original wave piece. No host chart is required to lie in every
adapted source chart. Only the true active carrier is localized. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
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
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

def observerChart (e : OpenPartialHomeomorph M D) : OpenPartialHomeomorph (Z × M) X :=
  (OpenPartialHomeomorph.refl Z).prod e

def observerDomain (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D) : Set X :=
  ((observerChart e).symm.trans b.chart).source

def observerActiveSample (e : OpenPartialHomeomorph M D) (S : Set M)
    (d : OriginalWaveSeedRefinement (m := m) F hF w weight) (i : Fin d.count) : Set X :=
  observerChart e '' ((univ ×ˢ S) ∩ tsupport (d.cutoff i))

theorem observerDomain_open (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D) :
    IsOpen (b.observerDomain e) :=
  ((observerChart e).symm.trans b.chart).open_source

theorem observerDomain_source (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D) :
    MapsTo (fun z : X => (z.1,e.symm z.2)) (b.observerDomain e) b.chart.source :=
  fun _ hz => hz.2

theorem observerDomain_active (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D) :
    ((univ : Set Z) ×ˢ e.target) ∩
      (fun z : X => (z.1,e.symm z.2)) ⁻¹' tsupport (d.cutoff i) ⊆ b.observerDomain e :=
  fun _ hz => ⟨hz.1,b.cutoff_support hz.2⟩

theorem observer_sample_compact (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    IsCompact (observerActiveSample e S d i) := by
  have hK : IsCompact (((univ : Set Z) ×ˢ S) ∩ tsupport (d.cutoff i)) :=
    (isCompact_univ.prod hS).inter_right (isClosed_tsupport _)
  exact hK.image_of_continuousOn ((observerChart e).continuousOn.mono
    (fun z hz => ⟨mem_univ _,hSe hz.1.2⟩))

theorem observer_sample_domain (b : OriginalWaveSeedBuffer d i) (e : OpenPartialHomeomorph M D)
    (S : Set M) (hSe : S ⊆ e.source) :
    observerActiveSample e S d i ⊆ b.observerDomain e := by
  rintro _ ⟨z,hz,rfl⟩
  have hs : z ∈ (observerChart e).source := ⟨mem_univ _,hSe hz.1.2⟩
  refine ⟨(observerChart e).map_source hs,?_⟩
  change (observerChart e).symm (observerChart e z) ∈ b.chart.source
  rw [(observerChart e).left_inv hs]
  exact b.cutoff_support hz.2

theorem observer_active_mem_sample (b : OriginalWaveSeedBuffer d i)
    (e : OpenPartialHomeomorph M D) (S : Set M) (hSe : S ⊆ e.source)
    (z : X) (hz : z ∈ (univ : Set Z) ×ˢ (e '' S))
    (hactive : (z.1,e.symm z.2) ∈ tsupport (d.cutoff i)) :
    z ∈ observerActiveSample e S d i := by
  obtain ⟨x,hx,he⟩ := hz.2
  refine ⟨(z.1,x),⟨⟨mem_univ _,hx⟩,?_⟩,?_⟩
  · have hh : (z.1,x) = (z.1,e.symm z.2) := by
      rw [←he,e.left_inv (hSe hx)]
    exact hh.symm ▸ hactive
  · exact Prod.ext rfl he

theorem observer_inverse_smooth (e : OpenPartialHomeomorph M D)
    (he : e ∈ IsManifold.maximalAtlas IM ∞ M) :
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Z)).prod IM) ∞
      (fun z : X => (z.1,e.symm z.2)) ((univ : Set Z) ×ˢ e.target) := by
  have hfirst : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Z) ∞ (fun z : X => z.1)
      ((univ : Set Z) ×ˢ e.target) := contDiffOn_fst.contMDiffOn
  have hsecond := (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (contDiffOn_snd.contMDiffOn : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ Prod.snd
      ((univ : Set Z) ×ˢ e.target)) (fun z hz => hz.2)
  exact hfirst.prodMk hsecond

theorem observer_transition_smooth (b : OriginalWaveSeedBuffer d i)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (b.chart ∘ (fun z : X => (z.1,e.symm z.2))) (b.observerDomain e) := by
  exact (b.chart_smooth.comp ((observer_inverse_smooth e he).mono (fun z hz => hz.1))
    (b.observerDomain_source e)).contDiffOn

theorem observer_phase_smooth (b : OriginalWaveSeedBuffer d i)
    (e : OpenPartialHomeomorph M D) (he : e ∈ IsManifold.maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (fun z : X => weight * w.phase (e.symm z.2)) (b.observerDomain e) := by
  have hmap : MapsTo (fun z : X => e.symm z.2) (b.observerDomain e) w.domain := by
    intro z hz
    exact (d.chart_source i (b.chart_source_subset hz.2)).2
  have hs : ContMDiffOn 𝓘(ℝ,X) IM ∞ (fun z : X => e.symm z.2) (b.observerDomain e) :=
    contMDiff_snd.comp_contMDiffOn
      ((observer_inverse_smooth e he).mono (fun z hz => hz.1))
  exact (contMDiffOn_const.mul (w.phase_smooth.comp hs hmap)).contDiffOn

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.observer_sample_compact
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.observer_transition_smooth
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.observer_phase_smooth

