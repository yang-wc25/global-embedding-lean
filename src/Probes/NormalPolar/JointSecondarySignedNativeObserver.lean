import NormalPolar.JointSecondarySignedNativeHost

/-! Genuine joint jets of the canonical parameter-chart conjugate. The
parameter component agrees with the identity on the open B target, so the
comparison is an equality of germs before taking any derivative. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M Ep P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

theorem jointSecondary_observer_inverse_smooth (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) :
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞
      (fun z : X => (z.1,e.symm z.2)) ((univ : Set Ep) ×ˢ e.target) := by
  have hf : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun z : X => z.1)
      ((univ : Set Ep) ×ˢ e.target) := contDiffOn_fst.contMDiffOn
  have hs := (contMDiffOn_symm_of_mem_maximalAtlas he).comp
    (contDiffOn_snd.contMDiffOn : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,D) ∞ Prod.snd
      ((univ : Set Ep) ×ˢ e.target)) (fun z hz => hz.2)
  exact hf.prodMk hs

theorem jointSecondary_product_chart_smooth (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞
      ((OpenPartialHomeomorph.refl Ep).prod e) ((OpenPartialHomeomorph.refl Ep).prod e).source :=
  contMDiffOn_fst.prodMk_space
    ((contMDiffOn_of_mem_maximalAtlas he).comp contMDiffOn_snd (fun z hz => hz.2))

theorem jointSecondary_native_chart_smooth (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod IM) 𝓘(ℝ,X) ∞
      (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e))
      (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).source := by
  have hs : (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).source ⊆
      ((OpenPartialHomeomorph.refl Ep).prod e).source :=
    fun z hz => ⟨mem_univ _,((passiveSecondarySeed_chart_source B e z).mp hz).2⟩
  exact ((jointSecondary_product_chart_smooth e he).mono hs).congr
    (fun z hz => passiveSecondarySeed_chart_apply B e z
      ((passiveSecondarySeed_chart_source B e z).mp hz).1)

theorem jointSecondary_native_chart_inverse_smooth (B : OpenPartialHomeomorph P Ep)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M) :
    ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod IM) ∞
      (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).symm
      (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).target := by
  have ht : (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)).target ⊆
      ((univ : Set Ep) ×ˢ e.target) :=
    fun z hz => ⟨mem_univ _,((passiveSecondarySeed_chart_target B e z).mp hz).2⟩
  exact ((jointSecondary_observer_inverse_smooth e he).mono ht).congr
    (fun z hz => passiveSecondarySeed_chart_symm B e z
      ((passiveSecondarySeed_chart_target B e z).mp hz).1)

variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer
variable (b : JointSecondarySignedBuffer (m := m) d i) (B : OpenPartialHomeomorph P Ep)
  (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1))))

def nativeObserverTransition : OpenPartialHomeomorph X X :=
  ((OpenPartialHomeomorph.refl Ep).prod e).symm.trans
    (round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod b.chart))

theorem nativeObserverTransition_smooth (he : e ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (b.nativeObserverTransition B e) (b.nativeObserverTransition B e).source :=
  ((jointSecondary_native_chart_smooth B b.chart b.maximal).comp
    ((jointSecondary_observer_inverse_smooth e he).mono (fun z hz => hz.1))
    (fun z hz => hz.2)).contDiffOn

theorem nativeObserverTransition_inverse_smooth (he : e ∈ maximalAtlas IM ∞ M) :
    ContDiffOn ℝ ∞ (b.nativeObserverTransition B e).symm (b.nativeObserverTransition B e).target :=
  ((jointSecondary_product_chart_smooth e he).comp
    ((jointSecondary_native_chart_inverse_smooth B b.chart b.maximal).mono (fun z hz => hz.1))
    (fun z hz => hz.2)).contDiffOn

theorem nativeObserverTransition_active (z : X) (hzB : z.1 ∈ B.target)
    (hze : z.2 ∈ e.target) (hcut : e.symm z.2 ∈ tsupport (d.cutoff i)) :
    z ∈ (b.nativeObserverTransition B e).source :=
  ⟨⟨mem_univ _,hze⟩,(passiveSecondarySeed_chart_source B b.chart (z.1,e.symm z.2)).mpr
    ⟨hzB,b.support_source hcut⟩⟩

theorem nativeObserverTransition_jets_eq (z : X) (hzB : z.1 ∈ B.target) (k : ℕ) :
    iteratedFDeriv ℝ k
      ((round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod b.chart)) ∘
        (fun y : X => (y.1,e.symm y.2))) z =
      iteratedFDeriv ℝ k (fun y : X => (y.1,b.chart (e.symm y.2))) z := by
  have hB : ∀ᶠ y : X in 𝓝 z, y.1 ∈ B.target :=
    continuous_fst.continuousAt (B.open_target.mem_nhds hzB)
  have heq :
      ((round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod b.chart)) ∘
        (fun y : X => (y.1,e.symm y.2))) =ᶠ[𝓝 z]
        (fun y : X => (y.1,b.chart (e.symm y.2))) :=
    hB.mono (fun y hy => passiveSecondarySeed_chart_apply B b.chart (y.1,e.symm y.2) hy)
  exact (heq.iteratedFDeriv ℝ k).eq_of_nhds

/-- The sequence is independent of the parameter chart B, scale, and order. -/
theorem exists_native_observer_jets (he : e ∈ maximalAtlas IM ∞ M)
    (S : Set M) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧
      ∀ B : OpenPartialHomeomorph P Ep, ∀ ell, 0 ≤ ell → ell ≤ 1 →
      ∀ (k : ℕ), 1 ≤ k → ∀ z : X, z.1 ∈ B.target →
      z.2 ∈ e '' S → e.symm z.2 ∈ tsupport (d.cutoff i) →
      ell^(k-1)*‖iteratedFDeriv ℝ k
        ((round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod b.chart)) ∘
          (fun y : X => (y.1,e.symm y.2))) z‖ ≤ T k := by
  obtain ⟨T,hT,hbound⟩ := b.exists_observer_jets (Ep := Ep) e he S hS hSe
  refine ⟨T,hT,?_⟩
  intro B ell hell hell1 k hk z hzB hz hcut
  rw [b.nativeObserverTransition_jets_eq B e z hzB k]
  exact hbound ell hell hell1 k hk z hz hcut

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_chart_inverse_smooth
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.nativeObserverTransition_inverse_smooth
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_native_observer_jets
