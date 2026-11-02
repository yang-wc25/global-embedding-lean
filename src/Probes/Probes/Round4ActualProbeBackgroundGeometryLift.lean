import Probes.Round4ActualProbeParameterLift
import Probes.ActualIncrementPrimaryGlobalSupport

/-! The same primary charts and true relative cutoff supports survive a passive
external parameter. These lemmas derive the lifted geometric hypotheses used
by the original finite solver; they do not assume regularity of its outputs. -/
noncomputable section
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {P E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))

theorem round4_primary_parameter_projection_smooth :
    ContMDiff ((𝓘(ℝ,P×Ep)).prod I) ((𝓘(ℝ,Ep)).prod I) ∞
      (fun z : (P×Ep)×M => (z.1.2,z.2)) :=
  (contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd

theorem round4_primary_parameter_chart_smooth
    (a : OpenPartialHomeomorph (Ep×M) (Ep×D))
    (ha : ContMDiffOn ((𝓘(ℝ,Ep)).prod I) 𝓘(ℝ,Ep×D) ∞ a a.source)
    (hai : ContMDiffOn 𝓘(ℝ,Ep×D) ((𝓘(ℝ,Ep)).prod I) ∞ a.symm a.target) :
    ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,(P×Ep)×D) ∞
      (round4ProbeParameterChartLift (P := P) a) (round4ProbeParameterChartLift (P := P) a).source ∧
    ContMDiffOn 𝓘(ℝ,(P×Ep)×D) ((𝓘(ℝ,P×Ep)).prod I) ∞
      (round4ProbeParameterChartLift (P := P) a).symm (round4ProbeParameterChartLift (P := P) a).target := by
  have hp := (round4_primary_parameter_projection_smooth (P := P) (I := I) (M := M) (Ep := Ep))
  have hc := ha.comp hp.contMDiffOn (fun z hz => (round4ProbeParameterChartLift_mem_source a z).mp hz)
  have hu : ContMDiffOn ((𝓘(ℝ,P×Ep)).prod I) 𝓘(ℝ,P) ∞
      (fun z : (P×Ep)×M => z.1.1) (round4ProbeParameterChartLift (P := P) a).source :=
    (contDiff_fst.contMDiff.comp contMDiff_fst).contMDiffOn
  have hfc := contDiff_fst.contMDiff.comp_contMDiffOn hc
  have hsc := contDiff_snd.contMDiff.comp_contMDiffOn hc
  have hforward := (hu.prodMk_space hfc).prodMk_space hsc
  have hp' : ContDiff ℝ ∞ (fun z : (P×Ep)×D => (z.1.2,z.2)) :=
    contDiff_fst.snd.prodMk contDiff_snd
  have hi := hai.comp hp'.contMDiff.contMDiffOn
    (fun z hz => (round4ProbeParameterChartLift_mem_target a z).mp hz)
  have hu' : ContMDiffOn 𝓘(ℝ,(P×Ep)×D) 𝓘(ℝ,P) ∞
      (fun z : (P×Ep)×D => z.1.1) (round4ProbeParameterChartLift (P := P) a).target :=
    contDiff_fst.fst.contMDiff.contMDiffOn
  have hinverse := (hu'.prodMk_space (contMDiff_fst.comp_contMDiffOn hi)).prodMk
    (contMDiff_snd.comp_contMDiffOn hi)
  exact ⟨hforward,hinverse⟩

theorem round4_relative_support_open {Y Y' : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace Y']
    (U : Set (Y×Y')) (hU : IsOpen U) (g : Y×Y' → ℝ) :
    incrementsGlobalRelativeSupport U g = U ∩ tsupport g := by
  unfold incrementsGlobalRelativeSupport
  change Subtype.val '' closure (Subtype.val ⁻¹' Function.support g : Set U) =
    U ∩ closure (Function.support g)
  rw [← hU.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Function.support g), Set.image_preimage_eq_inter_range]
  simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, Set.inter_comm]

theorem round4_relative_support_passive_parameter
    (W : Set (Ep×M)) (hW : IsOpen W) (f : Ep×M → ℝ) :
    incrementsGlobalRelativeSupport ((fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' W)
      (fun z : (P×Ep)×M => f (z.1.2,z.2)) ⊆
    (fun z : (P×Ep)×M => (z.1.2,z.2)) ⁻¹' incrementsGlobalRelativeSupport W f := by
  have hp : Continuous (fun z : (P×Ep)×M => (z.1.2,z.2)) :=
    continuous_fst.snd.prodMk continuous_snd
  rw [round4_relative_support_open _ (hW.preimage hp),round4_relative_support_open _ hW]
  intro z hz
  exact ⟨hz.1,tsupport_comp_subset_preimage f hp hz.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_primary_parameter_chart_smooth
#print axioms GlobalEmbedding.Continuation.round4_relative_support_passive_parameter
