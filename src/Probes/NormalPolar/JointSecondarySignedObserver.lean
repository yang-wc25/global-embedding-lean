import NormalPolar.JointSecondarySignedBuffers
import NormalPolar.OriginalWaveSeedObserverBounds
import NormalPolar.PassiveWaveSeedObserverJets

/-! Actual active-local observation of each signed secondary piece. The
original observer is not required to land in every adapted source. The
compact active sample is its image of the original atlas support intersected
with the real partition support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.NormalPolar
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "X" => Z × D
variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer

def seedChart (b : JointSecondarySignedBuffer d i) : OpenPartialHomeomorph (Z × M) X :=
  (OpenPartialHomeomorph.refl Z).prod b.chart

def observerDomain (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D) : Set X :=
  (((OpenPartialHomeomorph.refl Z).prod e).symm.trans b.seedChart).source

def observerActiveSample (e : OpenPartialHomeomorph M D) (S : Set M)
    (d : JointSecondarySignedRefinement (m := m) phase K O) (i : Fin d.count) : Set X :=
  ((OpenPartialHomeomorph.refl Z).prod e) ''
    (univ ×ˢ (S ∩ tsupport (d.cutoff i)))

theorem seedChart_smooth (b : JointSecondarySignedBuffer d i) :
    ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,X) ∞ b.seedChart b.seedChart.source := by
  have hc : ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,D) ∞
      (fun z : Z × M => b.chart z.2) (univ ×ˢ b.chart.source) :=
    (contMDiffOn_of_mem_maximalAtlas b.maximal).comp contMDiffOn_snd (fun z hz => hz.2)
  exact contMDiffOn_fst.prodMk_space hc

theorem observerDomain_open (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D) :
    IsOpen (b.observerDomain e) :=
  (((OpenPartialHomeomorph.refl Z).prod e).symm.trans b.seedChart).open_source

theorem observerDomain_source (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D) :
    MapsTo (fun z : X => (z.1,e.symm z.2)) (b.observerDomain e) b.seedChart.source :=
  fun _ hz => hz.2

theorem observerDomain_active (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D) :
    ((univ : Set Z) ×ˢ e.target) ∩
      (fun z : X => e.symm z.2) ⁻¹' tsupport (d.cutoff i) ⊆ b.observerDomain e :=
  fun _ hz => ⟨hz.1,mem_univ _,b.support_source hz.2⟩

theorem observer_sample_compact (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    IsCompact (observerActiveSample e S d i) := by
  have hK : IsCompact ((univ : Set Z) ×ˢ (S ∩ tsupport (d.cutoff i))) :=
    isCompact_univ.prod (hS.inter_right (isClosed_tsupport _))
  exact hK.image_of_continuousOn (((OpenPartialHomeomorph.refl Z).prod e).continuousOn.mono
    (fun z hz => ⟨mem_univ _,hSe hz.2.1⟩))

theorem observer_sample_domain (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D)
    (S : Set M) (hSe : S ⊆ e.source) :
    observerActiveSample e S d i ⊆ b.observerDomain e := by
  rintro _ ⟨z,hz,rfl⟩
  have hs : z ∈ ((OpenPartialHomeomorph.refl Z).prod e).source := ⟨mem_univ _,hSe hz.2.1⟩
  refine ⟨((OpenPartialHomeomorph.refl Z).prod e).map_source hs,?_⟩
  change ((OpenPartialHomeomorph.refl Z).prod e).symm
    (((OpenPartialHomeomorph.refl Z).prod e) z) ∈ b.seedChart.source
  rw [((OpenPartialHomeomorph.refl Z).prod e).left_inv hs]
  exact ⟨mem_univ _,b.support_source hz.2.2⟩

theorem observer_active_mem_sample (b : JointSecondarySignedBuffer d i)
    (e : OpenPartialHomeomorph M D) (S : Set M) (hSe : S ⊆ e.source)
    (z : X) (hz : z ∈ (univ : Set Z) ×ˢ (e '' S))
    (hactive : e.symm z.2 ∈ tsupport (d.cutoff i)) :
    z ∈ observerActiveSample e S d i := by
  obtain ⟨x,hx,he⟩ := hz.2
  refine ⟨(z.1,x),⟨mem_univ _,hx,?_⟩,Prod.ext rfl he⟩
  have hh : x = e.symm z.2 := by rw [←he,e.left_inv (hSe hx)]
  exact hh.symm ▸ hactive

theorem observer_inverse_smooth (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) :
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Z)).prod IM) ∞
      (fun z : X => (z.1,e.symm z.2)) ((univ : Set Z) ×ˢ e.target) := by
  have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Z) ∞ (fun z : X => z.1)
      ((univ : Set Z) ×ˢ e.target) := contDiffOn_fst.contMDiffOn
  have hs := (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (contDiffOn_snd.contMDiffOn : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ Prod.snd
      ((univ : Set Z) ×ˢ e.target)) (fun z hz => hz.2)
  exact hf.prodMk hs

theorem observer_transition_smooth (b : JointSecondarySignedBuffer d i)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (b.seedChart ∘ (fun z : X => (z.1,e.symm z.2))) (b.observerDomain e) :=
  (b.seedChart_smooth.comp ((observer_inverse_smooth e he).mono (fun z hz => hz.1))
    (b.observerDomain_source e)).contDiffOn

/-- Real joint observation jets, on the active original compact support.
The positive sequence is chosen before every ell and all derivative orders. -/
theorem exists_observer_jets {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    (b : JointSecondarySignedBuffer d i) (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧ ∀ ell, 0 ≤ ell → ell ≤ 1 →
      ∀ (k : ℕ), 1 ≤ k → ∀ z : Ep × D,
      z.2 ∈ e '' S → e.symm z.2 ∈ tsupport (d.cutoff i) →
      ell^(k-1)*‖iteratedFDeriv ℝ k
        (fun y : Ep × D => (y.1,b.chart (e.symm y.2))) z‖ ≤ T k := by
  let f : X → X := b.seedChart ∘ (fun z : X => (z.1,e.symm z.2))
  have hf := b.observer_transition_smooth e he
  obtain ⟨C,hC,hbound⟩ := exists_compact_native_prefix (observerActiveSample e S d i)
    (b.observerDomain e) (b.observer_sample_compact e S hS hSe)
    (b.observerDomain_open e) (b.observer_sample_domain e S hSe) f hf
  refine ⟨fun k => 1+C k,fun k => by linarith [hC k],?_⟩
  intro ell hell hell1 k hk z hz hactive
  have hzS : ((0 : Z),z.2) ∈ observerActiveSample e S d i :=
    b.observer_active_mem_sample e S hSe (0,z.2) ⟨mem_univ _,hz⟩ hactive
  have hbudget : ell^(k-1)*‖iteratedFDeriv ℝ k f (0,z.2)‖ ≤ C k :=
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq
      (one_mul _)).trans (hbound k k le_rfl (0,z.2) hzS)
  exact passiveWaveSeed_transition_jets f (b.observerDomain e) (b.observerDomain_open e)
    hf z (b.observer_sample_domain e S hSe hzS) ell hell k hk (C k) (hC k).le hbudget

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_observer_jets
