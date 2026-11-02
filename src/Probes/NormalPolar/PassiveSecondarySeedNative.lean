import NormalPolar.PassiveSecondarySeedChart
import Probes.ActualSecondaryQuadraticConstruction
import Probes.Round3ParameterRawAtlasData

/-! Actual secondary raw geometry in a genuine physical parameter chart.
The old spatial geometry and every budget are kept literally. The source,
target, support and samples retain the necessary B target, and the chart is
the canonical pullback of the actual physical product chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M P Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

def passiveSecondarySeed_native_raw (B : OpenPartialHomeomorph P Ep)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (n j : ℕ) (ell Mg : ℝ) (e : OpenPartialHomeomorph M D)
    (raw : ActualSecondaryRawGeometry F hF n j ell Mg univ)
    (hchart : raw.chart = (OpenPartialHomeomorph.refl Ep).prod e) :
    ActualSecondaryRawGeometry F hF n j ell Mg
      (round3ParameterNativeDomain B (univ : Set (P × M))) := by
  let an := round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod e)
  have hs : an.source ⊆ raw.chart.source := by
    intro z hz
    rw [hchart]
    exact ⟨mem_univ _,((passiveSecondarySeed_chart_source B e z).mp hz).2⟩
  have ht : an.target ⊆ raw.chart.target := by
    intro z hz
    rw [hchart]
    exact ⟨mem_univ _,((passiveSecondarySeed_chart_target B e z).mp hz).2⟩
  refine {
    c := raw.c
    chart := an
    sample := {z : X | z.1 ∈ B.target ∧ z ∈ raw.sample}
    sample_subset := ?_
    support := {z : Ep × M | z.1 ∈ B.target ∧ z ∈ raw.support}
    support_closed := ?_
    support_source := ?_
    source_domain := fun z hz =>
      ⟨((passiveSecondarySeed_chart_source B e z).mp hz).1,mem_univ _⟩
    chart_smooth := (raw.chart_smooth.mono hs).congr (fun z hz => by
      rw [hchart]
      exact passiveSecondarySeed_chart_apply B e z
        ((passiveSecondarySeed_chart_source B e z).mp hz).1)
    inverse := ?_
    phase := raw.phase
    phase_smooth := raw.phase_smooth.mono hs
    adaptation := ?_
    brows_smooth := raw.brows_smooth.mono ht
    inverse_smooth := raw.inverse_smooth.mono ht
    transverse_smooth := raw.transverse_smooth.mono ht
    value_smooth := raw.value_smooth.mono ht
    coefficientA_smooth := raw.coefficientA_smooth.mono ht
    coefficientB_smooth := raw.coefficientB_smooth.mono ht
    brows_bound := fun k hk z hz => raw.brows_bound k hk z hz.2
    transverse_bound := fun k hk z hz => raw.transverse_bound k hk z hz.2
    inverse_bound := fun k hk z hz => raw.inverse_bound k hk z hz.2
    value_bound := fun k hk z hz => raw.value_bound k hk z hz.2
    coefficientA_bound := fun k hk z hz => raw.coefficientA_bound k hk z hz.2
    coefficientB_bound := fun k hk z hz => raw.coefficientB_bound k hk z hz.2
    spatialChart := raw.spatialChart
    coordinate := raw.coordinate
    maximal := raw.maximal
    target := fun z hz => raw.target z (ht hz)
    immersion := fun z hz => raw.immersion z (ht hz)
    gram := fun z hz => raw.gram z (ht hz) }
  · intro z hz
    have h := raw.sample_subset hz.2
    rw [hchart] at h
    exact (passiveSecondarySeed_chart_target B e z).mpr ⟨hz.1,h.2⟩
  · let Wn := round3ParameterNativeDomain B (univ : Set (P × M))
    let κ : Wn → (univ : Set (Ep × M)) := fun z => ⟨z.val,mem_univ _⟩
    have hκ : Continuous κ := continuous_subtype_val.subtype_mk _
    have he : (Subtype.val ⁻¹' {z : Ep × M | z.1 ∈ B.target ∧ z ∈ raw.support} : Set Wn) =
        κ ⁻¹' (Subtype.val ⁻¹' raw.support : Set (univ : Set (Ep × M))) := by
      ext z
      exact and_iff_right z.property.1
    rw [he]
    exact raw.support_closed.preimage hκ
  · intro z hz
    have h := raw.support_source hz.2
    rw [hchart] at h
    exact (passiveSecondarySeed_chart_source B e z).mpr ⟨hz.1,h.2⟩
  · intro z hz
    rw [passiveSecondarySeed_chart_symm B e z
      ((passiveSecondarySeed_chart_target B e z).mp hz).1]
    simpa only [hchart,OpenPartialHomeomorph.prod_symm_apply,OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply,id_eq] using raw.inverse z (ht hz)
  · intro z hz
    rw [passiveSecondarySeed_chart_apply B e z
      ((passiveSecondarySeed_chart_source B e z).mp hz).1]
    simpa only [hchart,OpenPartialHomeomorph.prod_apply,OpenPartialHomeomorph.refl_apply] using
      raw.adaptation z (hs hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_native_raw
