import Upgrade.SupportedProbeAtlasTransport
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth actual leading fields in fixed source coordinates

These are consequences of the existing legal-wave data, not a new wave
construction. They allow finite principal margins to be extended from packet
centers to neighboring actual incidences. The native tensor is not asserted
to be a globally smooth function in unrelated pointwise tangent charts.
-/

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology TensorProduct

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The original rank-one tensor, using the original symmetric-square norm. -/
def incidenceLegalTensor (xi : E →L[ℝ] ℝ) (nu : V) : SymmetricSquare E →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (supportedRankLegalVariation xi.toLinearMap nu)

/-- Source transport acts on the same original covector. -/
theorem incidenceLegalTensor_comp_square (xi : E →L[ℝ] ℝ) (nu : V)
    (frame : E →L[ℝ] E) :
    (incidenceLegalTensor xi nu).comp
      (LinearMap.toContinuousLinearMap (symmetricSquareLinearMap frame.toLinearMap)) =
        incidenceLegalTensor (xi.comp frame) nu := by
  apply ContinuousLinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      change supportedRankLegalVariation xi.toLinearMap nu
        (symmetricSquareLinearMap frame.toLinearMap (symmetricSquareProduct E u v)) = _
      rw [symmetric_square_linear_map_eq]
      change supportedRankLegalVariation xi.toLinearMap nu
        (symmetricSquareMapL frame (symmetricSquareProduct E u v)) = _
      rw [symmetricSquareMapL_product, supportedRankLegalVariation_product]
      exact (supportedRankLegalVariation_product (xi.comp frame).toLinearMap nu u v).symm
    | add a b ha hb =>
      have hmk := (symmetricSquareQuotient E).map_add a b
      change Submodule.Quotient.mk (a + b) =
        (Submodule.Quotient.mk a : SymmetricSquare E) + Submodule.Quotient.mk b at hmk
      rw [hmk, map_add, map_add, ha, hb]

/-- Smooth dependence of the literal original rank-one column on its actual
covector and normal value. This does not introduce a new quotient or norm. -/
theorem contDiff_incidenceLegalTensor :
    ContDiff ℝ ∞ (fun z : (E →L[ℝ] ℝ) × V ↦ incidenceLegalTensor z.1 z.2) := by
  apply contDiff_clm_apply_iff.mpr
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      change ContDiff ℝ ∞ (fun z : (E →L[ℝ] ℝ) × V ↦
        supportedRankLegalVariation z.1.toLinearMap z.2 (symmetricSquareProduct E u v))
      simp only [supportedRankLegalVariation_product, ContinuousLinearMap.coe_coe]
      exact ((contDiff_fst.clm_apply contDiff_const).mul
        (contDiff_fst.clm_apply contDiff_const)).smul contDiff_snd
    | add a b ha hb =>
      convert ha.add hb using 1
      funext z
      exact (congrArg (incidenceLegalTensor z.1 z.2)
        ((symmetricSquareQuotient E).map_add a b)).trans
          (map_add (incidenceLegalTensor z.1 z.2) _ _)

variable {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, E)

namespace LocalLegalWave

/-- Leading values stay in the original actual normal space at every point. -/
theorem value_mem_normal
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF) (z : M) :
    w.value z ∈ normalSpace (I := IM) F z :=
  (normalSpace (I := IM) F z).smul_mem (w.cutoff z) (w.normal z).property

theorem tensor_in_frame
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (z : M) (frame : E →L[ℝ] E) :
    probeTensorInFrame frame (w.tensor z) =
      w.cutoff z • incidenceLegalTensor
        ((mfderiv IM 𝓘(ℝ, ℝ) w.phase z).comp frame) (w.normal z : V) := by
  have hw : w.tensor z = w.cutoff z •
      incidenceLegalTensor (mfderiv IM 𝓘(ℝ, ℝ) w.phase z) (w.normal z : V) := by
    apply ContinuousLinearMap.ext
    intro q
    rfl
  rw [probeTensorInFrame, hw, ContinuousLinearMap.smul_comp]
  simpa only [] using! congrArg
    (fun L : SymmetricSquare E →L[ℝ] V ↦ w.cutoff z • L)
    (incidenceLegalTensor_comp_square
      (show E →L[ℝ] ℝ from mfderiv IM 𝓘(ℝ, ℝ) w.phase z) (w.normal z : V) frame)

/-- The actual cutoff-normal leading value is globally smooth, although the
un-cut normal section was only required to be smooth on the original chart. -/
theorem value_contMDiff [T2Space M]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF) :
    ContMDiff IM 𝓘(ℝ, V) ∞ w.value := by
  intro z
  by_cases hz : z ∈ tsupport (w.cutoff : M → ℝ)
  · have hdom := w.support_subset hz
    exact w.cutoff.contMDiffAt.smul
      ((w.normal_smooth z hdom).contMDiffAt (w.domain_open.mem_nhds hdom))
  · apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (w.cutoff : M → ℝ)).isOpen_compl.mem_nhds hz]
      with p hp
    simp only [value, image_eq_zero_of_notMem_tsupport hp, zero_smul]

/-- At an actual atlas point the covector in the inverse source frame is the
ordinary derivative of the SAME phase composed with that chart inverse. -/
theorem phase_covector_in_atlas
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} (w : LocalLegalWave F hF)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : E) (hz : z ∈ (A.chart i).target) (hw : (A.chart i).symm z ∈ w.domain) :
    (mfderiv IM 𝓘(ℝ, ℝ) w.phase ((A.chart i).symm z)).comp
      (probeAtlasFrame A i ((A.chart i).symm z)) =
        fderiv ℝ (w.phase ∘ (A.chart i).symm) z := by
  have hp := ((w.phase_smooth _ hw).contMDiffAt
    (w.domain_open.mem_nhds hw)).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas (hA.chart_mem i) hz).mdifferentiableAt
    (by simp)
  rw [probeAtlasFrame, (A.chart i).right_inv hz]
  simpa only [mfderiv_eq_fderiv] using! (mfderiv_comp z hp hc).symm

end LocalLegalWave
end GlobalEmbedding.Upgrade
