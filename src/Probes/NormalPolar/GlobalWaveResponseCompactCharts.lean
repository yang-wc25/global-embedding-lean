import NormalPolar.GlobalWaveResponseObserver

/-!
# Uniform transition jets on the original atlas and actual wave carriers

The charts and carriers in this module are fixed before the oscillation scale
and the probe parameter are introduced. Compactness of the original atlas
supports bounds both derivatives of their actual transitions to the selected
mode charts. The carrier specialization uses the original cutoff itself.
-/

noncomputable section
open Set Filter Function Manifold IsManifold GlobalEmbedding.Paper
  GlobalEmbedding.Offline GlobalEmbedding.Continuation
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {E D M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {r : ℕ}

private noncomputable local instance transitionHessianSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] D) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance transitionHessianNorm :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] D) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance transitionHessianSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] D) := ContinuousLinearMap.toNormedSpace

/-- The literal transition from an original atlas chart to a fixed mode chart. -/
def globalWaveAtlasTransition (A : BufferedAtlas M E)
    (source : Fin r → OpenPartialHomeomorph M D)
    (i : Fin A.count) (l : Fin r) : E → D :=
  source l ∘ (A.chart i).symm

theorem globalWaveAtlasTransition_contDiffOn
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,D) ∞ (source l) (source l).source)
    (i : Fin A.count) (l : Fin r) :
    ContDiffOn ℝ ∞ (globalWaveAtlasTransition A source i l)
      ((A.chart i).symm.trans (source l)).source := by
  have hsymm := contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i)
  have hsymm' : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (A.chart i).symm
      ((A.chart i).symm.trans (source l)).source := hsymm.mono (by
    intro y hy
    exact hy.1)
  have hh := (hsource l).comp hsymm' (by
      intro y hy
      change y ∈ (A.chart i).target ∧ (A.chart i).symm y ∈ (source l).source at hy
      exact hy.2)
  exact hh.contDiffOn

/-- One pair of strictly positive constants controls all actual transitions
on every original support intersected with its selected fixed closed carrier.
No scale, probe parameter, or moving map occurs in this existential choice. -/
theorem exists_uniform_globalWaveAtlasTransition_jets
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,D) ∞ (source l) (source l).source)
    (K : Fin r → Set M) (hK : ∀ l, IsClosed (K l))
    (hKsource : ∀ l, K l ⊆ (source l).source) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧
      ∀ (i : Fin A.count) (l : Fin r) (x : M), x ∈ A.support i → x ∈ K l →
        ‖fderiv ℝ (globalWaveAtlasTransition A source i l) (A.chart i x)‖ ≤ B1 ∧
        ‖fderiv ℝ (fderiv ℝ (globalWaveAtlasTransition A source i l))
          (A.chart i x)‖ ≤ B2 := by
  let J := Fin A.count × Fin r
  let S : J → Set E := fun j => A.chart j.1 '' (A.support j.1 ∩ K j.2)
  have hS (j : J) : IsCompact (S j) :=
    ((hcompact j.1).inter_right (hK j.2)).image_of_continuousOn
      ((A.chart j.1).continuousOn.mono (fun x hx => hA.support_subset j.1 hx.1))
  have hsub (j : J) : S j ⊆ ((A.chart j.1).symm.trans (source j.2)).source := by
    rintro _ ⟨x,hx,rfl⟩
    have hs := hA.support_subset j.1 hx.1
    change A.chart j.1 x ∈ (A.chart j.1).target ∧
      (A.chart j.1).symm (A.chart j.1 x) ∈ (source j.2).source
    exact ⟨(A.chart j.1).map_source hs, by
      simpa only [(A.chart j.1).left_inv hs] using hKsource j.2 hx.2⟩
  have hfirst (j : J) : ContinuousOn
      (fderiv ℝ (globalWaveAtlasTransition A source j.1 j.2)) (S j) := by
    have hs := globalWaveAtlasTransition_contDiffOn A hA source hsource j.1 j.2
    exact (hs.continuousOn_fderiv_of_isOpen
      ((A.chart j.1).symm.trans (source j.2)).open_source (by simp)).mono (hsub j)
  have hsecond (j : J) : ContinuousOn
      (fderiv ℝ (fderiv ℝ (globalWaveAtlasTransition A source j.1 j.2))) (S j) := by
    have hs := globalWaveAtlasTransition_contDiffOn A hA source hsource j.1 j.2
    have hd := hs.fderiv_of_isOpen ((A.chart j.1).symm.trans (source j.2)).open_source
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
    exact (hd.continuousOn_fderiv_of_isOpen
      ((A.chart j.1).symm.trans (source j.2)).open_source (by simp)).mono (hsub j)
  choose C1 hC1 using fun j => (hS j).exists_bound_of_continuousOn (hfirst j)
  choose C2 hC2 using fun j => (hS j).exists_bound_of_continuousOn (hsecond j)
  obtain ⟨B1,hB1⟩ := Finite.exists_le C1
  obtain ⟨B2,hB2⟩ := Finite.exists_le C2
  refine ⟨|B1|+1, |B2|+1, by positivity, by positivity, ?_⟩
  intro i l x hx hk
  have hs : A.chart i x ∈ S (i,l) := ⟨x,⟨hx,hk⟩,rfl⟩
  constructor
  · exact ((hC1 (i,l) _ hs).trans (hB1 (i,l))).trans (by linarith [le_abs_self B1])
  · exact ((hC2 (i,l) _ hs).trans (hB2 (i,l))).trans (by linarith [le_abs_self B2])

section OriginalWaves
variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

/-- The original wave cutoffs supply the closed carriers; no independently
postulated transition derivative budgets are needed. -/
theorem exists_uniform_originalWaveAtlasTransition_jets
    (F₀ : M → EuclideanSpace ℝ (Fin N))
    (hF₀ : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F₀)
    (waves : Fin r → LocalLegalWave F₀ hF₀)
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i))
    (source : Fin r → OpenPartialHomeomorph M D)
    (hsource : ∀ l, ContMDiffOn 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) 𝓘(ℝ,D) ∞
      (source l) (source l).source)
    (hcarrier : ∀ l, tsupport ((waves l).cutoff : M → ℝ) ⊆ (source l).source) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧
      ∀ (i : Fin A.count) (l : Fin r) (x : M), x ∈ A.support i →
        x ∈ tsupport ((waves l).cutoff : M → ℝ) →
        ‖fderiv ℝ (globalWaveAtlasTransition A source i l) (A.chart i x)‖ ≤ B1 ∧
        ‖fderiv ℝ (fderiv ℝ (globalWaveAtlasTransition A source i l))
          (A.chart i x)‖ ≤ B2 :=
  exists_uniform_globalWaveAtlasTransition_jets A hA hcompact source hsource
    (fun l => tsupport ((waves l).cutoff : M → ℝ)) (fun _ => isClosed_tsupport _) hcarrier

end OriginalWaves
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.exists_uniform_originalWaveAtlasTransition_jets
