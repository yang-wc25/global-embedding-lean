import Probes.Round4ParameterProbeMeanCoordinates
import Probes.Round4ParameterProbeCombinedPrimary
import Smoothing.ParameterRound2MeanRawNative

/-! The literal common-array metric remainder in original coordinates.
The source observer keeps the real parameter fixed; the actual inverse
parameter chart is composed afterward, before taking joint derivatives.
There is no coordinate equality or output estimate supplied as an oracle. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M Label : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def actualRepairModelFirstDefectArrayRest
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V) :=
  incrementsOriginalMetricError F U (round4ParameterProbeArrayMean (I := 𝓙) phase tau R Q) 1

def actualRepairModelFirstDefectObservedRest
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V) (e : OpenPartialHomeomorph M D) : X → Tensor :=
  fun z => actualFiniteMetricError
    (fun w => F (w.1,e.symm w.2)) (fun w => U (w.1,e.symm w.2)) (fun _ => 0) 1 z -
    actualPrimaryOppositeMeanTensor
      (fun l t x => phase l (t,e.symm x)) tau
      (fun (_ : Label) (_ : Ep) (_ : Unit) (_ : D) => 1)
      (fun l t (_ : Unit) x => R l (t,e.symm x))
      (fun l t (_ : Unit) x => Q l (t,e.symm x)) z

theorem actualRepairModelFirstDefect_array_mean_symmetric
    (phase : Label → Ep × M → ℝ) (tau : ℝ) (R Q : Label → Ep × M → V)
    (p : Ep) (x : M) :
    (round4ParameterProbeArrayMean (I := 𝓙) phase tau R Q p x).IsSymm := by
  constructor
  intro v w
  simp only [round4ParameterProbeArrayMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul]
  simp_rw [real_inner_comm]

theorem actualRepairModelFirstDefect_array_rest_symmetric
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V) (p : Ep) (x : M) :
    (actualRepairModelFirstDefectArrayRest (m := m) F U phase tau R Q p x).IsSymm := by
  exact ((inducedMetric_isPosSemidef (I := 𝓙) (fun y => F (p,y)+U (p,y)) x).isSymm.sub
    (inducedMetric_isPosSemidef (I := 𝓙) (fun y => F (p,y)) x).isSymm).sub
      ((actualRepairModelFirstDefect_array_mean_symmetric (m := m) phase tau R Q p x).smul (1^2))

theorem actualRepairModelFirstDefect_array_rest_pullback
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V)
    (i : Fin A.count × Fin count) (z : X)
    (hz : z ∈ (B i.2).target ×ˢ (A.chart i.1).target)
    (hp : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (phase l)
      ((B i.2).symm z.1,(A.chart i.1).symm z.2))
    (hR : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (R l)
      ((B i.2).symm z.1,(A.chart i.1).symm z.2))
    (hQ : ∀ l, ContMDiffAt ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Q l)
      ((B i.2).symm z.1,(A.chart i.1).symm z.2)) :
    actualOriginalNativeTargetTensor A B
      (actualRepairModelFirstDefectArrayRest F U phase tau R Q) i z =
    (actualRepairModelFirstDefectObservedRest F U phase tau R Q (A.chart i.1) ∘
      parameterRound2_meanParameterMap (m := m) (B i.2)) z := by
  rw [actualRepairModelFirstDefectArrayRest,
    actual_original_native_metric_error_pullback_total A B hA F U _ 1 i z hz]
  have hm := round4ParameterProbe_array_mean_original A B hA phase tau R Q i z hz.2 hp hR hQ
  simp only [actualOriginalNativeMetricError,actualFiniteMetricError,one_pow,one_smul]
  rw [hm]
  simp only [actualRepairModelFirstDefectObservedRest,Function.comp_apply,
    parameterRound2_meanParameterMap,actualFiniteMetricError,one_pow,one_smul,sub_zero]
  apply actual_bilinear_tensor_eq_of_basis
  intro k l
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,sub_zero]
  rfl

/-- The total native error is exactly its same-array three-term remainder
plus its same-array physical mean defect. No derivative identity is needed. -/
theorem actualRepairModelFirstDefect_array_error_split
    (F U : Ep × M → V) (phase : Label → Ep × M → ℝ)
    (tau : ℝ) (R Q : Label → Ep × M → V)
    (H : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) (delta : ℝ) :
    incrementsOriginalMetricError F U H delta =
      actualRepairModelFirstDefectArrayRest F U phase tau R Q +
        (round4ParameterProbeArrayMean (I := 𝓙) phase tau R Q-delta^2 • H) := by
  funext p x
  simp only [actualRepairModelFirstDefectArrayRest,incrementsOriginalMetricError,
    one_pow,one_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
  abel

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_array_rest_pullback
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_array_error_split
