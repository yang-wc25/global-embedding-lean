import Probes.Round3PreparedParameterSecondaryLift
import Probes.Round3ParameterNativeParent

/-! One physical signed-secondary choice is constructed from a fixed actual
reference piece. Every observer receives its canonical two-sided conjugate;
the real host/slice packet is supplied for that same native choice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_parameter_secondary_chart_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      ((round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart)
      ((round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart).source ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      ((round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart).symm
      ((round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart).target := by
  let B := Data.parameterChart i.2
  let qM := round3ParameterProductChart (M := M) B
  let qD := round3ParameterProductChart (M := D) B
  let a := actualHostAdaptedChart (Data.atlas.chart i.1) piece.native
  have hM := round3ParameterProductChart_smooth (n := m+1) (M := M) B (hd.parameter_charts_smooth i.2)
  have hMi := round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B (hd.parameter_charts_smooth i.2)
  have hD : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ep × D) ∞ qD qD.source :=
    ((contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).comp
      contMDiffOn_fst (fun _ hz => hz.1)).prodMk_space contMDiffOn_snd
  have hDi : ContMDiffOn 𝓘(ℝ,Ep × D) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ qD.symm qD.target :=
    ((contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth i.2)).comp
      contDiff_fst.contMDiff.contMDiffOn (fun _ hz => hz.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  have hEq : (round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart = (qM.trans a).trans qD.symm := by
    simp only [round3PreparedParameterSecondaryChoice,round3ParameterChartPullback,
      OpenPartialHomeomorph.prod_symm,OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.refl_symm]
    rfl
  rw [hEq]
  exact ⟨round3Parameter_partial_trans_smooth (qM.trans a) qD.symm
      (round3Parameter_partial_trans_smooth qM a hM piece.data.2.1) hDi,
    round3Parameter_partial_trans_symm_smooth (qM.trans a) qD.symm
      (round3Parameter_partial_trans_symm_smooth qM a hMi piece.data.2.2.1) hD⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_chart_smooth
