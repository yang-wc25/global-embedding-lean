import NormalPolar.PassiveOriginalPrimaryChart
import Probes.Round3ParameterNativeRefinementSamples

/-! Fixed whole-parameter primary profiles from actual seed primitive
smoothness and the original compact sample sets. No derivative budget or
completed wave estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M S P Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace S] [Subsingleton S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) S]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin 0)) ∞ S]
  [TopologicalSpace P] [CompactSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- Actual full joint transition, inverse and eta profiles on the unchanged
original samples. The constants come from smooth primitive charts on compact
active samples and are fixed before every derivative scale. -/
theorem passiveOriginal_primary_profiles
    (s₀ : S) (seed : IncrementsOriginalNativeData (m+1) 0 N M S)
    (hd : IncrementsOriginalDomainConditions seed)
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hB : IsSmoothBufferedAtlas B)
    (Q : Fin B.count → Set (EuclideanSpace ℝ (Fin d)))
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation seed.atlas B.chart
      seed.sourceNormDomain Q univ i))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m)
      (Λ := Fin seed.primaryCount) (Β := Β) (fun s x => seed.F (s,x)))
    (R : ℕ) (geom : Round3ParameterOriginalPrimaryGeometry seed g R)
    (hChart : ∀ nu a,
      ContMDiffOn ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod IM)
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod IM) ∞ (g.chart nu a) (g.chart nu a).source ∧
      ContMDiffOn ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod IM)
        ((𝓘(ℝ,EuclideanSpace ℝ (Fin 0))).prod IM) ∞ (g.chart nu a).symm (g.chart nu a).target) :
    let Data := passiveOriginalData s₀ seed B Q
    let gp := passiveParameterPrimary (P := P) s₀ (fun s x => seed.F (s,x)) g
    ∃ Forward Inverse Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Inverse k) ∧ (∀ k, 0 ≤ Meta k) ∧
      Round3ParameterOriginalChartProfiles Data gp Forward Inverse Meta := by
  intro Data gp
  let J := Fin seed.primaryCount × Β × (Fin seed.atlas.count × Fin B.count)
  let Samples := incrementsOriginalEvaluation seed.atlas B.chart seed.sourceNormDomain Q univ
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' Samples i
  have hSn (i) : IsCompact (Sn i) :=
    (parameterTensorModelEquiv (m+1) d).toHomeomorph.isCompact_preimage.mpr (hS i)
  have hSnTarget (i) : Sn i ⊆ (B.chart i.2).target ×ˢ (seed.atlas.chart i.1).target := by
    intro z hz
    have hh := hz.1
    change ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).2 ∈
        (seed.atlas.chart i.1).target ∧
      ((parameterTensorModelEquiv (m+1) d).symm (parameterTensorModelEquiv (m+1) d z)).1 ∈
        (B.chart i.2).target at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply,mem_prod] using hh.symm
  have hg := passiveOriginal_primary_geometry s₀ seed B Q g R geom
  have hsmooth (nu) (a) := passiveOriginal_primary_chart_smooth (P := P) (d := d) s₀
    (g.chart nu a) (hChart nu a).1 (hChart nu a).2
  have hOne (j : J) := round3Parameter_actual_observer_chart_profiles
    (B.chart j.2.2.2) (hB.chart_mem j.2.2.2)
    (gp.chart j.1 j.2.1) (hg.preserves j.1 j.2.1)
    (hsmooth j.1 j.2.1).1 (hsmooth j.1 j.2.1).2
    (gp.eta j.1 j.2.1) (hg.smooth j.1 j.2.1) (hg.support j.1 j.2.1)
    (seed.atlas.chart j.2.2.1) (hd.atlas_smooth.chart_mem j.2.2.1)
    (Sn j.2.2) (hSn j.2.2) (hSnTarget j.2.2)
  choose Tf Ti Te hTf hTi hTe hb using hOne
  refine ⟨fun k => round3PreparedFiniteMaximum (fun j : J => Tf j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Ti j k),
    fun k => round3PreparedFiniteMaximum (fun j : J => Te j k),
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,
    fun k => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro ell hell hell1 nu beta i gN t etaN k z hz hEtaZ
  have hh := hb (nu,beta,i) ell hell hell1 k z ⟨hz,hEtaZ⟩
  exact ⟨hh.1,hh.2.1,
    hh.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Tf j k) (nu,beta,i)),
    hh.2.2.2.1.trans (round3PreparedFiniteMaximum_bound (fun j : J => Ti j k) (nu,beta,i)),
    hh.2.2.2.2.trans (round3PreparedFiniteMaximum_bound (fun j : J => Te j k) (nu,beta,i))⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_primary_profiles
