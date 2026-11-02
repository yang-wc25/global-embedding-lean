import Repair.FullIncrementNovPrimaryAtCongruence
import Probes.Round3ParameterPrimaryNative

/-! Exact actual-wave and coefficient-mean identities at an original open
parameter.  Only equality of the represented source slice is needed.  The
finite length is arbitrary and no observation order is an argument of the
constructed wave.  Parameter derivatives are handled separately by an open
neighborhood equality; a single-point equality is not used for them.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Manifold Set
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable
  (F : P → M → EuclideanSpace ℝ (Fin N)) (Fn : Ep → M → EuclideanSpace ℝ (Fin N))
  (hFn : ∀ t, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (Fn t))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) F)
  (gn : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Label) (Β := Sub) Fn)
  (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
    ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F z.1))
  (B : OpenPartialHomeomorph P Ep)
  (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (inputn : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ) (t : Ep) (ht : t ∈ B.target)
  (hFt : F (B.symm t) = Fn t) (hInput : input (B.symm t) = inputn t)
  (hCut : ∀ nu x, g.cutoff nu (B.symm t,x) = gn.cutoff nu (t,x))
  (hNormal : ∀ nu x, g.normal nu (B.symm t,x) = gn.normal nu (t,x))
  (hLinear : ∀ nu x, g.linearArgument nu (B.symm t) x = gn.linearArgument nu t x)
  (hEta : ∀ nu beta x, g.eta nu beta (B.symm t,x) = gn.eta nu beta (t,x))
  (hChart : ∀ nu beta, gn.chart nu beta = round3ParameterChartPullback B (g.chart nu beta))
  (hInverse : ∀ nu beta, g.inverse nu beta (B.symm t) = gn.inverse nu beta t)

include hPreserves ht hFt hInput hCut hNormal hLinear hEta hChart hInverse

theorem fullIncrementNov_open_native_extension_eq
    (channel : Bool) (nu : Label) (beta : Sub) (x : M) :
    incrementsGlobalPrimaryExtension Fn hFn gn inputn length tau channel nu beta (t,x) =
      fullIncrementNovPrimaryExtension F g input hActive length tau channel nu beta (B.symm t,x) := by
  have hSource : (t,x) ∈ (gn.chart nu beta).source ↔
      (B.symm t,x) ∈ (g.chart nu beta).source := by
    rw [hChart]
    exact round3ParameterChartPullback_source_iff B (g.chart nu beta) (hPreserves nu beta) (t,x) ht
  by_cases hx : (B.symm t,x) ∈ (g.chart nu beta).source
  · have hn := hSource.mpr hx
    have hPair : gn.chart nu beta (t,x) =
        (t,(g.chart nu beta (B.symm t,x)).2) := by
      rw [hChart,round3ParameterChartPullback_apply]
      rw [hPreserves nu beta (B.symm t,x) hx,B.right_inv ht]
    have hTarget (y : D) : (B.symm t,y) ∈ (g.chart nu beta).target ↔
        (t,y) ∈ (gn.chart nu beta).target := by
      rw [hChart]
      exact (round3ParameterChartPullback_target_iff B (g.chart nu beta) (hPreserves nu beta) (t,y) ht).symm
    have hh := fullIncrementNov_primary_evaluation_congr F Fn g
      (Round3ParameterPrimaryFamily.ofNative Fn gn) input inputn length tau nu beta (B.symm t) t
      (hActive nu beta (B.symm t,x) hx) (hFn t) hFt hInput
      (hCut nu) (hNormal nu) (hLinear nu) (hEta nu beta) hTarget (hInverse nu beta)
    simp only [incrementsGlobalPrimaryExtension,fullIncrementNovPrimaryExtension,hn,hx,ite_true,dite_true,hPair]
    exact (hh.2.2 channel _).symm
  · have hn := mt hSource.mp hx
    simp only [incrementsGlobalPrimaryExtension,fullIncrementNovPrimaryExtension,hn,hx,ite_false,dite_false]

theorem fullIncrementNov_open_native_amplitude_eq
    (channel : Bool) (nu : Label) (x : M) :
    incrementsGlobalPrimaryAmplitude Fn hFn gn inputn length tau channel nu (t,x) =
      fullIncrementNovPrimaryAmplitude F g input hActive length tau channel nu (B.symm t,x) :=
  Finset.sum_congr rfl (fun beta _ => fullIncrementNov_open_native_extension_eq
    F Fn hFn g gn hActive B hPreserves input inputn length tau t ht hFt hInput
    hCut hNormal hLinear hEta hChart hInverse channel nu beta x)

variable (hPhase : ∀ nu x, g.phase nu (B.symm t,x) = gn.phase nu (t,x))
include hPhase

theorem fullIncrementNov_open_native_wave_eq (x : M) :
    incrementsGlobalPrimaryWave Fn hFn gn inputn length tau (t,x) =
      fullIncrementNovPrimaryWave F g input hActive length tau (B.symm t,x) := by
  unfold incrementsGlobalPrimaryWave fullIncrementNovPrimaryWave
  apply Finset.sum_congr rfl
  intro nu _
  rw [← hPhase nu x]
  rw [fullIncrementNov_open_native_amplitude_eq F Fn hFn g gn hActive B hPreserves input inputn
    length tau t ht hFt hInput hCut hNormal hLinear hEta hChart hInverse true nu x,
    fullIncrementNov_open_native_amplitude_eq F Fn hFn g gn hActive B hPreserves input inputn
    length tau t ht hFt hInput hCut hNormal hLinear hEta hChart hInverse false nu x]

theorem fullIncrementNov_open_native_coefficient_eq
    (channel : Bool) (nu : Label) (x : M) :
    incrementsGlobalPrimaryCoefficient Fn hFn gn inputn length tau channel nu (t,x) =
      fullIncrementNovPrimaryCoefficient F g input hActive length tau channel nu (B.symm t,x) := by
  have hAmp (ch : Bool) := funext (fullIncrementNov_open_native_amplitude_eq
    F Fn hFn g gn hActive B hPreserves input inputn length tau t ht hFt hInput
    hCut hNormal hLinear hEta hChart hInverse ch nu)
  have hPh := (funext (hPhase nu)).symm
  have hSlow : incrementsGlobalSpatialDerivative (I := I)
      (incrementsGlobalPrimaryAmplitude Fn hFn gn inputn length tau channel nu) (t,x) =
      incrementsGlobalSpatialDerivative (I := I)
        (fullIncrementNovPrimaryAmplitude F g input hActive length tau channel nu) (B.symm t,x) := by
    unfold incrementsGlobalSpatialDerivative
    rw [hAmp channel]
    rw [congrFun (hAmp channel) x]
  have hFast : incrementsGlobalScalarDerivative (I := I) (gn.phase nu) (t,x) =
      incrementsGlobalScalarDerivative (I := I) (g.phase nu) (B.symm t,x) := by
    unfold incrementsGlobalScalarDerivative
    rw [hPh]
    rw [← hPhase nu x]
  simp only [incrementsGlobalPrimaryCoefficient,fullIncrementNovPrimaryCoefficient,hSlow,hFast,
    congrFun (hAmp (!channel)) x]

theorem fullIncrementNov_open_native_mean_eq (x : M) :
    incrementsGlobalPrimaryMean Fn hFn gn inputn length tau t x =
      fullIncrementNovPrimaryMean F g input hActive length tau (B.symm t) x := by
  simp only [incrementsGlobalPrimaryMean,fullIncrementNovPrimaryMean,
    fullIncrementNov_open_native_coefficient_eq F Fn hFn g gn hActive B hPreserves input inputn
      length tau t ht hFt hInput hCut hNormal hLinear hEta hChart hInverse hPhase]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_native_extension_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_native_amplitude_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_native_wave_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_native_coefficient_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_open_native_mean_eq
