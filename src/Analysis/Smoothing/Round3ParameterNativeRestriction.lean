import Smoothing.Round3ParameterPrimaryRestriction
import Smoothing.ParameterRound2PrimaryRestriction
import Probes.Round3ParameterRawAtlasData

/-! Restricting the one physical family and taking its canonical parameter
representative commute exactly, including actual chart domains. This keeps
the original raw proof on the same global family used by the mean solver. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

theorem round3Parameter_nativeDomain_open
    {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
    (B : OpenPartialHomeomorph P Q) (G : Set (P × M)) (hG : IsOpen G) :
    IsOpen (round3ParameterNativeDomain (M := M) B G) := by
  have h := ((B.continuousOn_symm.comp continuousOn_fst (fun _ hz => hz.1)).prodMk continuousOn_snd).isOpen_inter_preimage
    (B.open_target.prod isOpen_univ) hG
  convert h using 1
  ext z
  simp only [round3ParameterNativeDomain,mem_setOf_eq,mem_inter_iff,mem_prod,mem_univ,mem_preimage,and_true,Function.comp_apply]

theorem round3Parameter_chart_restriction_commutes
    {P Q M D : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace M] [TopologicalSpace D]
    (B : OpenPartialHomeomorph P Q) (a : OpenPartialHomeomorph (P × M) (P × D))
    (G : Set (P × M)) (hG : IsOpen G) :
    round3ParameterChartPullback B (a.restrOpen G hG) =
      (round3ParameterChartPullback B a).restrOpen (round3ParameterNativeDomain B G)
        (round3Parameter_nativeDomain_open B G hG) := by
  apply OpenPartialHomeomorph.ext
  · intro z; rfl
  · intro z; rfl
  · ext z
    rw [round3ParameterChartPullback_source]
    change (z.1 ∈ B.target ∧ ((B.symm z.1,z.2) ∈ a.source ∧ (B.symm z.1,z.2) ∈ G) ∧
      (a (B.symm z.1,z.2)).1 ∈ B.source) ↔
      z ∈ (round3ParameterChartPullback B a).source ∧
        (z.1 ∈ B.target ∧ (B.symm z.1,z.2) ∈ G)
    rw [round3ParameterChartPullback_source]
    constructor
    · rintro ⟨hp,⟨ha,hg⟩,hout⟩
      exact ⟨⟨hp,ha,hout⟩,hp,hg⟩
    · rintro ⟨⟨hp,ha,hout⟩,_,hg⟩
      exact ⟨hp,⟨ha,hg⟩,hout⟩

variable {m d N : ℕ} {M P Λ Β : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

private theorem nativeFamily_eq_of_fields (F : Ep → M → V)
    (g g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hPhase : g.phase = g'.phase) (hCut : g.cutoff = g'.cutoff)
    (hNormal : g.normal = g'.normal) (hLinear : g.linearArgument = g'.linearArgument)
    (hEta : g.eta = g'.eta) (hChart : g.chart = g'.chart) (hInverse : g.inverse = g'.inverse) :
    g = g' := by
  cases g
  cases g'
  cases hPhase
  cases hCut
  cases hNormal
  cases hLinear
  cases hEta
  cases hChart
  cases hInverse
  rfl

theorem round3Parameter_native_primary_restriction_commutes
    (F : P → M → V)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (B : OpenPartialHomeomorph P Ep) (G : Set (P × M)) (hG : IsOpen G) :
    round3ParameterNativePrimary F (round3Parameter_restrictPrimaryFamily F g G hG) B =
      parameterRound2_restrictPrimaryFamily (fun p => F (B.symm p)) (round3ParameterNativePrimary F g B)
        (round3ParameterNativeDomain B G) (round3Parameter_nativeDomain_open B G hG) := by
  apply nativeFamily_eq_of_fields (fun p => F (B.symm p))
    (round3ParameterNativePrimary F (round3Parameter_restrictPrimaryFamily F g G hG) B)
    (parameterRound2_restrictPrimaryFamily (fun p => F (B.symm p)) (round3ParameterNativePrimary F g B)
      (round3ParameterNativeDomain B G) (round3Parameter_nativeDomain_open B G hG))
    rfl rfl rfl rfl rfl _ rfl
  funext nu a
  exact round3Parameter_chart_restriction_commutes B (g.chart nu a) G hG

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_chart_restriction_commutes
#print axioms GlobalEmbedding.Continuation.round3Parameter_native_primary_restriction_commutes
