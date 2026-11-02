import Repair.EntranceDirectMetaGeometry
import Repair.EntranceCutoffCoordinateTransfer

/-!
# Actual original scalar cutoff jets supply the numerical primary Meta

The full family, both nonlinear parameter conjugations, the original
sampling domains and the selected inverse charts are unchanged. All
smoothness and the adapted-coordinate identity are proved from the actual
prepared pieces. Only the primitive original scalar cutoff derivatives
remain to be supplied by the literal parent times owner plateau producer.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem repairEntrance_actual_primary_cutoff_from_original_jets
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (Cutoff Forward Inverse OldMeta : ℕ → ℝ)
    (hCutoff : ∀ j, 0 ≤ Cutoff j) (hInverse : ∀ j, 0 ≤ Inverse j) :
    let g := round3ParameterWholePrimaryFamily Ref hd hs hn theta packet
    Round3ParameterOriginalChartProfiles Ref g Forward Inverse OldMeta →
    (∀ nu beta i k z, parameterTensorModelEquiv (m+1) d z ∈
      incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i →
      ((Ref.parameterChart i.2).symm z.1,(Ref.atlas.chart i.1).symm z.2) ∈ tsupport (g.eta nu beta) →
      ‖iteratedFDeriv ℝ k (fun w : X =>
        g.eta nu beta ((Ref.parameterChart i.2).symm w.1,(Ref.atlas.chart i.1).symm w.2)) z‖ ≤ Cutoff k) →
    RepairOriginalPrimaryCutoffJets Ref g (repairEntranceCompositionProfile Cutoff Inverse) := by
  intro g hProfiles hOriginal nu beta i gN t etaN j z hz hPhysical
  let B := Ref.parameterChart i.2
  let e := (OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)
  let a := gN.chart nu beta
  have hOld := hProfiles 1 (by norm_num) le_rfl nu beta i j z hz hPhysical
  have hChart := round3ParameterLiftedPrimaryChart_smooth Ref hd beta.1.2 nu _
    (round3ParameterWholePrimaryPiece Ref hd theta packet nu beta)
  have hNative := round3ParameterChartPullback_smooth B (hd.parameter_charts_smooth i.2)
    (g.chart nu beta) hChart.1 hChart.2
  have hTransition := round3Parameter_native_observer_transition_smooth a hNative.1 hNative.2
    (Ref.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
  have hEta := (round3ParameterWholePrimaryFamily_cutoff_geometry Ref hd hs hn theta packet nu beta).1
  have hParam (w : X) (hw : w ∈ t.source) : w.1 ∈ B.target := by
    exact ((round3ParameterChartPullback_source B (g.chart nu beta) (e.symm w)).mp hw.2).1
  have hOriginalSmooth : ContDiffOn ℝ ∞ (gN.eta nu beta ∘ e.symm) t.source := by
    have hB : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,Ep) ∞ (fun w : X => B.symm w.1) t.source :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).comp
        contDiff_fst.contMDiff.contMDiffOn hParam
    have hA : ContMDiffOn 𝓘(ℝ,X) 𝓙 ∞
        (fun w : X => (Ref.atlas.chart i.1).symm w.2) t.source :=
      (contMDiffOn_symm_of_mem_maximalAtlas (hd.atlas_smooth.chart_mem i.1)).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hw => hw.1.2)
    exact (hEta.comp_contMDiffOn (hB.prodMk hA)).contDiffOn
  exact repairEntrance_actual_cutoff_coordinate_transfer e a (gN.eta nu beta)
    Cutoff Inverse hCutoff hInverse hOriginalSmooth hTransition.2 j z hOld.1
    (fun k _ => hOriginal nu beta i k z hz hPhysical) (by
      intro k _ _
      have hh := (hProfiles 1 (by norm_num) le_rfl nu beta i k z hz hPhysical).2.2.2.1
      simpa only [one_pow,one_mul] using hh)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_primary_cutoff_from_original_jets
