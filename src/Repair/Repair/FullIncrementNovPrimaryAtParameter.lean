import Probes.Round3ParameterPrimaryConstruction
import Probes.Round3ParameterChartPullback

/-!
Evaluation of the existing finite differential primary formula at one
parameter.  Only that original source slice needs a smoothness proof.
This does not extend the original map or replace any input primitive.

The supported extension evaluates this formula only on its actual adapted
source, where original admissibility supplies the required source slice.
The exact equalities below identify every construction with the existing
global definitions whenever their stronger global smoothness argument exists.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Label Sub : Type*} [Fintype Label] [Fintype Sub]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (N := N) (Λ := Label) (Β := Sub) F)
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

def fullIncrementNovPrimarySourceAt
    (tau : ℝ) (nu : Label) (beta : Sub) (p : P)
    (hp : ContMDiff I 𝓘(ℝ,V) ∞ (F p)) (x : D) : Fin (m+1) → ℂ :=
  incrementsModeComplexInclude (incrementsModeSource (I := I) (F p) hp
    (g.inverse nu beta p) (fun _ _ _ => 0)
    (round3ParameterPrimaryLocalFree F g input tau nu beta p) x)

def fullIncrementNovPrimaryFiniteUAt
    (length : ℕ) (tau : ℝ) (nu : Label) (beta : Sub) (p : P)
    (hp : ContMDiff I 𝓘(ℝ,V) ∞ (F p)) : D → Fin (m+1) → ℂ :=
  incrementsActualModeSum
    (incrementsModeComplexFirstOrderA (I := I) (F p) hp (g.inverse nu beta p))
    (incrementsModeComplexFirstOrderB (I := I) (F p) hp (g.inverse nu beta p))
    ((tau : ℂ)/Complex.I) length
    (fullIncrementNovPrimarySourceAt F g input tau nu beta p hp)

def fullIncrementNovPrimaryLocalZAt
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (beta : Sub) (p : P)
    (hp : ContMDiff I 𝓘(ℝ,V) ∞ (F p)) (x : D) : V :=
  let ch := if channel then incrementsModeRealPart else incrementsModeImagPart
  incrementsModeFullReconstruction (I := I) (F p) hp (g.inverse nu beta p)
    (fun y => ch (fullIncrementNovPrimaryFiniteUAt F g input length tau nu beta p hp y))
    (fun _ _ _ => 0)
    (fun y => if channel then round3ParameterPrimaryLocalFree F g input tau nu beta p y else 0) x

variable
  (hActive : ∀ nu beta z, z ∈ (g.chart nu beta).source →
    ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F z.1))

def fullIncrementNovPrimaryExtension
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (beta : Sub) (z : P × M) : V :=
  if hz : z ∈ (g.chart nu beta).source then
    fullIncrementNovPrimaryLocalZAt F g input length tau channel nu beta z.1
      (hActive nu beta z hz) ((g.chart nu beta z).2)
  else 0

def fullIncrementNovPrimaryAmplitude
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (z : P × M) : V :=
  ∑ beta, fullIncrementNovPrimaryExtension F g input hActive length tau channel nu beta z

def fullIncrementNovPrimaryWave
    (length : ℕ) (tau : ℝ) (z : P × M) : V :=
  ∑ nu, (Real.cos (g.phase nu z/tau) •
    fullIncrementNovPrimaryAmplitude F g input hActive length tau true nu z -
    Real.sin (g.phase nu z/tau) • fullIncrementNovPrimaryAmplitude F g input hActive length tau false nu z)

def fullIncrementNovPrimaryCoefficient
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (z : P × M) :
    TangentSpace I z.2 →L[ℝ] V :=
  let own := fullIncrementNovPrimaryAmplitude F g input hActive length tau channel nu
  let other := fullIncrementNovPrimaryAmplitude F g input hActive length tau (!channel) nu
  let slow := incrementsGlobalSpatialDerivative (I := I) own z
  let fast := (incrementsGlobalScalarDerivative (I := I) (g.phase nu) z).smulRight ((tau⁻¹) • other z)
  if channel then slow-fast else slow+fast

def fullIncrementNovPrimaryMean
    (length : ℕ) (tau : ℝ) (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (1/2 : ℝ) • ∑ nu, (
    LinearMap.BilinForm.comp (innerₗ V)
      (fullIncrementNovPrimaryCoefficient F g input hActive length tau true nu (p,x)).toLinearMap
      (fullIncrementNovPrimaryCoefficient F g input hActive length tau true nu (p,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (fullIncrementNovPrimaryCoefficient F g input hActive length tau false nu (p,x)).toLinearMap
      (fullIncrementNovPrimaryCoefficient F g input hActive length tau false nu (p,x)).toLinearMap)

def fullIncrementNovPrimaryMeanError
    (length : ℕ) (tau : ℝ) (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  fullIncrementNovPrimaryMean F g input hActive length tau p x-input p x

variable (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))

theorem fullIncrementNov_primary_sourceAt_eq
    (tau : ℝ) (nu : Label) (beta : Sub) (p : P) (x : D) :
    fullIncrementNovPrimarySourceAt F g input tau nu beta p (hF p) x =
      round3ParameterPrimarySource F hF g input tau nu beta (p,x) := rfl

theorem fullIncrementNov_primary_finiteUAt_eq
    (length : ℕ) (tau : ℝ) (nu : Label) (beta : Sub) (p : P) :
    fullIncrementNovPrimaryFiniteUAt F g input length tau nu beta p (hF p) =
      round3ParameterPrimaryFiniteU F hF g input length tau nu beta p := rfl

theorem fullIncrementNov_primary_localZAt_eq
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (beta : Sub) (p : P) (x : D) :
    fullIncrementNovPrimaryLocalZAt F g input length tau channel nu beta p (hF p) x =
      round3ParameterPrimaryLocalZ F hF g input length tau channel nu beta (p,x) := rfl

variable (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
include hPreserves

theorem fullIncrementNov_primary_extension_eq
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (beta : Sub) (z : P × M) :
    fullIncrementNovPrimaryExtension F g input hActive length tau channel nu beta z =
      round3ParameterPrimaryExtension F hF g input length tau channel nu beta z := by
  classical
  by_cases hz : z ∈ (g.chart nu beta).source
  · have hzPair : g.chart nu beta z = (z.1,(g.chart nu beta z).2) :=
      Prod.ext (hPreserves nu beta z hz) rfl
    simp only [fullIncrementNovPrimaryExtension,round3ParameterPrimaryExtension,hz,dite_true,ite_true]
    rw [hzPair]
    rfl
  · simp only [fullIncrementNovPrimaryExtension,round3ParameterPrimaryExtension,hz,dite_false,ite_false]

theorem fullIncrementNov_primary_amplitude_eq
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) :
    fullIncrementNovPrimaryAmplitude F g input hActive length tau channel nu =
      round3ParameterPrimaryAmplitude F hF g input length tau channel nu := by
  funext z
  exact Finset.sum_congr rfl (fun beta _ =>
    fullIncrementNov_primary_extension_eq F g input hActive hF hPreserves length tau channel nu beta z)

theorem fullIncrementNov_primary_wave_eq (length : ℕ) (tau : ℝ) :
    fullIncrementNovPrimaryWave F g input hActive length tau =
      round3ParameterPrimaryWave F hF g input length tau := by
  funext z
  simp only [fullIncrementNovPrimaryWave,round3ParameterPrimaryWave,
    fullIncrementNov_primary_amplitude_eq F g input hActive hF hPreserves]

theorem fullIncrementNov_primary_coefficient_eq
    (length : ℕ) (tau : ℝ) (channel : Bool) (nu : Label) (z : P × M) :
    fullIncrementNovPrimaryCoefficient F g input hActive length tau channel nu z =
      round3ParameterPrimaryCoefficient F hF g input length tau channel nu z := by
  simp only [fullIncrementNovPrimaryCoefficient,round3ParameterPrimaryCoefficient,
    fullIncrementNov_primary_amplitude_eq F g input hActive hF hPreserves]

theorem fullIncrementNov_primary_mean_eq (length : ℕ) (tau : ℝ) (p : P) (x : M) :
    fullIncrementNovPrimaryMean F g input hActive length tau p x =
      round3ParameterPrimaryMean F hF g input length tau p x := by
  simp only [fullIncrementNovPrimaryMean,round3ParameterPrimaryMean,
    fullIncrementNov_primary_coefficient_eq F g input hActive hF hPreserves]

theorem fullIncrementNov_primary_meanError_eq (length : ℕ) (tau : ℝ) (p : P) (x : M) :
    fullIncrementNovPrimaryMeanError F g input hActive length tau p x =
      round3ParameterPrimaryMeanError F hF g input length tau p x := by
  simp only [fullIncrementNovPrimaryMeanError,round3ParameterPrimaryMeanError,
    fullIncrementNov_primary_mean_eq F g input hActive hF hPreserves]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimarySourceAt
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryFiniteUAt
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryLocalZAt
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryExtension
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryAmplitude
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryWave
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryCoefficient
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryMean
#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryMeanError
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_wave_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_primary_mean_eq
