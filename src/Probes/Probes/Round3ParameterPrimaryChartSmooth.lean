import Probes.Round3ParameterPrimaryPhysicalGeometry
import Probes.Round3ParameterNativeParent

/-! Smoothness of the actual all-chart conjugation on its real open source
and target. Both nonlinear parameter coordinate maps are retained. This is
used to bound the total parameter/spatial derivatives on actual compact
original observation sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
section Composition
variable {E₁ E₂ E₃ H₁ H₂ H₃ X₁ X₂ X₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace H₃]
  [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace X₃]
  [ChartedSpace H₁ X₁] [ChartedSpace H₂ X₂] [ChartedSpace H₃ X₃]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂} {I₃ : ModelWithCorners ℝ E₃ H₃}

theorem round3Parameter_partial_trans_smooth
    (q : OpenPartialHomeomorph X₁ X₂) (r : OpenPartialHomeomorph X₂ X₃)
    (hq : ContMDiffOn I₁ I₂ ∞ q q.source) (hr : ContMDiffOn I₂ I₃ ∞ r r.source) :
    ContMDiffOn I₁ I₃ ∞ (q.trans r) (q.trans r).source :=
  hr.comp (hq.mono inter_subset_left) (fun _ hz => hz.2)

theorem round3Parameter_partial_trans_symm_smooth
    (q : OpenPartialHomeomorph X₁ X₂) (r : OpenPartialHomeomorph X₂ X₃)
    (hq : ContMDiffOn I₂ I₁ ∞ q.symm q.target) (hr : ContMDiffOn I₃ I₂ ∞ r.symm r.target) :
    ContMDiffOn I₃ I₁ ∞ (q.trans r).symm (q.trans r).target :=
  hq.comp (hr.mono inter_subset_left) (fun _ hz => hz.2)
end Composition

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3ParameterLiftedPrimaryChart_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3ParameterLiftedPrimaryChart Data ip nu W piece)
      (round3ParameterLiftedPrimaryChart Data ip nu W piece).source ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (round3ParameterLiftedPrimaryChart Data ip nu W piece).symm
      (round3ParameterLiftedPrimaryChart Data ip nu W piece).target := by
  let B := Data.parameterChart ip
  let qM := round3ParameterProductChart (M := M) B
  let qD := round3ParameterProductChart (M := D) B
  let a := actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native
  have hM := round3ParameterProductChart_smooth (n := m+1) (M := M) B (hd.parameter_charts_smooth ip)
  have hMi := round3ParameterProductChart_symm_smooth (n := m+1) (M := M) B (hd.parameter_charts_smooth ip)
  have hD : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ep × D) ∞ qD qD.source :=
    ((contMDiffOn_of_mem_maximalAtlas (hd.parameter_charts_smooth ip)).comp
      contMDiffOn_fst (fun _ hz => hz.1)).prodMk_space contMDiffOn_snd
  have hDi : ContMDiffOn 𝓘(ℝ,Ep × D) ((𝓘(ℝ,Ep)).prod 𝓙) ∞ qD.symm qD.target :=
    ((contMDiffOn_symm_of_mem_maximalAtlas (hd.parameter_charts_smooth ip)).comp
      contDiff_fst.contMDiff.contMDiffOn (fun _ hz => hz.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn
  have hEq : round3ParameterLiftedPrimaryChart Data ip nu W piece = (qM.trans a).trans qD.symm := by
    simp only [round3ParameterLiftedPrimaryChart,round3ParameterChartPullback,
      OpenPartialHomeomorph.prod_symm,OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.refl_symm]
    rfl
  rw [hEq]
  exact ⟨round3Parameter_partial_trans_smooth (qM.trans a) qD.symm
      (round3Parameter_partial_trans_smooth qM a hM piece.data.2.1) hDi,
    round3Parameter_partial_trans_symm_smooth (qM.trans a) qD.symm
      (round3Parameter_partial_trans_symm_smooth qM a hMi piece.data.2.2.1) hD⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterLiftedPrimaryChart_smooth
