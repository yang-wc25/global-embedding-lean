import Probes.Round3ParameterPrimaryGlobalNaturality

/-!
# The actual finite primary construction depends only on its parameter slice

The source polynomial differentiates the spatial variable. The original
parameter-preserving chart extension then preserves this slice locality all
the way to the actual native mean. This fact permits induction in the real
background recurrence without a global extension identity outside a chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (input₁ input₂ : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ) (b : P) (hinput : input₁ b = input₂ b)

include hinput

theorem actualParameterPrimaryLocalFree_input_slice_congr (l : Λ) (k : Β) :
    round3ParameterPrimaryLocalFree F g input₁ tau l k b =
      round3ParameterPrimaryLocalFree F g input₂ tau l k b := by
  funext x
  simp only [round3ParameterPrimaryLocalFree,round3ParameterPrimaryB,hinput]

theorem actualParameterPrimarySource_input_slice_congr (l : Λ) (k : Β) (x : D) :
    round3ParameterPrimarySource F hF g input₁ tau l k (b,x) =
      round3ParameterPrimarySource F hF g input₂ tau l k (b,x) := by
  unfold round3ParameterPrimarySource
  rw [actualParameterPrimaryLocalFree_input_slice_congr F g input₁ input₂ tau b hinput l k]

theorem actualParameterPrimaryFiniteU_input_slice_congr (l : Λ) (k : Β) :
    round3ParameterPrimaryFiniteU F hF g input₁ length tau l k b =
      round3ParameterPrimaryFiniteU F hF g input₂ length tau l k b := by
  have hs := funext (actualParameterPrimarySource_input_slice_congr F hF g input₁ input₂ tau b hinput l k)
  unfold round3ParameterPrimaryFiniteU
  rw [hs]

theorem actualParameterPrimaryLocalZ_input_slice_congr
    (ch : Bool) (l : Λ) (k : Β) (x : D) :
    round3ParameterPrimaryLocalZ F hF g input₁ length tau ch l k (b,x) =
      round3ParameterPrimaryLocalZ F hF g input₂ length tau ch l k (b,x) := by
  unfold round3ParameterPrimaryLocalZ
  rw [actualParameterPrimaryFiniteU_input_slice_congr F hF g input₁ input₂ length tau b hinput l k,
    actualParameterPrimaryLocalFree_input_slice_congr F g input₁ input₂ tau b hinput l k]

variable (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
include hg

theorem actualParameterPrimaryExtension_input_slice_congr
    (ch : Bool) (l : Λ) (k : Β) (x : M) :
    round3ParameterPrimaryExtension F hF g input₁ length tau ch l k (b,x) =
      round3ParameterPrimaryExtension F hF g input₂ length tau ch l k (b,x) := by
  by_cases hx : (b,x) ∈ (g.chart l k).source
  · have hchart : g.chart l k (b,x) = (b,(g.chart l k (b,x)).2) := Prod.ext (hg l k _ hx) rfl
    simp only [round3ParameterPrimaryExtension,hx,ite_true]
    rw [hchart]
    exact actualParameterPrimaryLocalZ_input_slice_congr F hF g input₁ input₂ length tau b hinput ch l k _
  · simp only [round3ParameterPrimaryExtension,hx,ite_false]

theorem actualParameterPrimaryAmplitude_input_slice_congr
    (ch : Bool) (l : Λ) (x : M) :
    round3ParameterPrimaryAmplitude F hF g input₁ length tau ch l (b,x) =
      round3ParameterPrimaryAmplitude F hF g input₂ length tau ch l (b,x) := by
  exact Finset.sum_congr rfl (fun k _ =>
    actualParameterPrimaryExtension_input_slice_congr F hF g input₁ input₂ length tau b hinput hg ch l k x)

theorem actualParameterPrimaryWave_input_slice_congr (x : M) :
    round3ParameterPrimaryWave F hF g input₁ length tau (b,x) =
      round3ParameterPrimaryWave F hF g input₂ length tau (b,x) := by
  simp only [round3ParameterPrimaryWave,
    actualParameterPrimaryAmplitude_input_slice_congr F hF g input₁ input₂ length tau b hinput hg]

theorem actualParameterPrimaryCoefficient_input_slice_congr
    (ch : Bool) (l : Λ) (x : M) :
    round3ParameterPrimaryCoefficient F hF g input₁ length tau ch l (b,x) =
      round3ParameterPrimaryCoefficient F hF g input₂ length tau ch l (b,x) := by
  have hown := funext (actualParameterPrimaryAmplitude_input_slice_congr
    F hF g input₁ input₂ length tau b hinput hg ch l)
  have hother := actualParameterPrimaryAmplitude_input_slice_congr
    F hF g input₁ input₂ length tau b hinput hg (!ch) l x
  have hd := congrArg (fun f : M → V => mvfderiv I f x) hown
  have hf := congrArg
    (fun value : V => (incrementsGlobalScalarDerivative (I := I) (g.phase l) (b,x)).smulRight (tau⁻¹ • value)) hother
  cases ch
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f+g) hd hf
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f-g) hd hf

theorem actualParameterPrimaryMean_input_slice_congr (x : M) :
    round3ParameterPrimaryMean F hF g input₁ length tau b x =
      round3ParameterPrimaryMean F hF g input₂ length tau b x := by
  simp only [round3ParameterPrimaryMean,
    actualParameterPrimaryCoefficient_input_slice_congr F hF g input₁ input₂ length tau b hinput hg]

theorem actualParameterPrimaryMeanError_input_slice_congr (x : M) :
    round3ParameterPrimaryMeanError F hF g input₁ length tau b x =
      round3ParameterPrimaryMeanError F hF g input₂ length tau b x := by
  rw [round3ParameterPrimaryMeanError,round3ParameterPrimaryMeanError,
    actualParameterPrimaryMean_input_slice_congr F hF g input₁ input₂ length tau b hinput hg,hinput]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterPrimaryWave_input_slice_congr
#print axioms GlobalEmbedding.Continuation.actualParameterPrimaryMeanError_input_slice_congr
