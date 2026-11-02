import Repair.FullIncrementNovOpenSourceModel
import Repair.FullIncrementNovPrimaryAtCongruence
import Smoothing.Round3ParameterPrimaryRestrictionMean
import Smoothing.ParameterRound2TensorGermTransfer

/-!
# The same physical mean in the original open parameter region

The finite-norm mean producer uses the original map and its actual supported
primary formula.  The verified secondary solver uses the internal totalized
source-slice presentation.  These theorems identify their literal primary
amplitudes and coefficient means on the original open parameter region.  No
input map is replaced in the public construction.  The final-domain theorem
preserves every original weighted norm by an open-neighborhood identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable {Β : Type*} [Fintype Β]

theorem incrementsCompletion_original_open_primary_extension
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
    (fun p x => Data.F (p,x)))
  (hg : ∀ (nu : Fin Data.primaryCount) (beta : Β), Round3ParameterChartPreserves (g.chart nu beta))
  (hTarget : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × D),
    z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
  (hActive : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × M),
    z ∈ (g.chart nu beta).source →
    ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
  (length : ℕ) (tau : ℝ)
    (channel : Bool) (nu : Fin Data.primaryCount) (beta : Β)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    round3ParameterPrimaryExtension (fullIncrementNovOriginalSourceSlice Data)
      (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (fullIncrementNovOriginalOpenFamily Data g hTarget) input length tau channel nu beta (p,x) =
    fullIncrementNovPrimaryExtension (fun p x => Data.F (p,x)) g input hActive
      length tau channel nu beta (p,x) := by
  let F := fullIncrementNovOriginalSourceSlice Data
  let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
  let gO := fullIncrementNovOriginalOpenFamily Data g hTarget
  by_cases hx : (p,x) ∈ (g.chart nu beta).source
  · have hPair : gO.chart nu beta (p,x) = (p,(g.chart nu beta (p,x)).2) :=
      Prod.ext (hg nu beta (p,x) hx) rfl
    have heval := fullIncrementNov_primary_evaluation_congr
      (fun p x => Data.F (p,x)) F g gO input input length tau nu beta p p
      (hActive nu beta (p,x) hx) (hF p)
      (fullIncrementNov_original_source_slice_eq Data p hp).symm rfl
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => Iff.rfl) rfl
    change round3ParameterPrimaryExtension F hF gO input length tau channel nu beta (p,x) = _
    simp only [round3ParameterPrimaryExtension,fullIncrementNovPrimaryExtension,
      show (p,x) ∈ (gO.chart nu beta).source from hx,hx,ite_true,dite_true,hPair]
    exact (heval.2.2 channel ((g.chart nu beta (p,x)).2)).symm
  · change round3ParameterPrimaryExtension F hF gO input length tau channel nu beta (p,x) = _
    simp only [round3ParameterPrimaryExtension,fullIncrementNovPrimaryExtension,
      show (p,x) ∉ (gO.chart nu beta).source from hx,hx,ite_false,dite_false]

theorem incrementsCompletion_original_open_primary_amplitude
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
    (fun p x => Data.F (p,x)))
  (hg : ∀ (nu : Fin Data.primaryCount) (beta : Β), Round3ParameterChartPreserves (g.chart nu beta))
  (hTarget : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × D),
    z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
  (hActive : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × M),
    z ∈ (g.chart nu beta).source →
    ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
  (length : ℕ) (tau : ℝ)
    (channel : Bool) (nu : Fin Data.primaryCount)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    round3ParameterPrimaryAmplitude (fullIncrementNovOriginalSourceSlice Data)
      (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (fullIncrementNovOriginalOpenFamily Data g hTarget) input length tau channel nu (p,x) =
    fullIncrementNovPrimaryAmplitude (fun p x => Data.F (p,x)) g input hActive
      length tau channel nu (p,x) :=
  Finset.sum_congr rfl (fun beta _ => incrementsCompletion_original_open_primary_extension
    Data hd hs g hg hTarget hActive input length tau channel nu beta p hp x)

theorem incrementsCompletion_original_open_primary_coefficient
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
    (fun p x => Data.F (p,x)))
  (hg : ∀ (nu : Fin Data.primaryCount) (beta : Β), Round3ParameterChartPreserves (g.chart nu beta))
  (hTarget : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × D),
    z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
  (hActive : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × M),
    z ∈ (g.chart nu beta).source →
    ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
  (length : ℕ) (tau : ℝ)
    (channel : Bool) (nu : Fin Data.primaryCount)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    round3ParameterPrimaryCoefficient (fullIncrementNovOriginalSourceSlice Data)
      (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (fullIncrementNovOriginalOpenFamily Data g hTarget) input length tau channel nu (p,x) =
    fullIncrementNovPrimaryCoefficient (fun p x => Data.F (p,x)) g input hActive
      length tau channel nu (p,x) := by
  let F := fullIncrementNovOriginalSourceSlice Data
  let hF := fullIncrementNov_original_source_slice_smooth Data hd hs
  let gO := fullIncrementNovOriginalOpenFamily Data g hTarget
  have hAmp (ch : Bool) :
      (fun x => round3ParameterPrimaryAmplitude F hF gO input length tau ch nu (p,x)) =
      fun x => fullIncrementNovPrimaryAmplitude (fun p x => Data.F (p,x)) g input hActive
        length tau ch nu (p,x) :=
    funext (incrementsCompletion_original_open_primary_amplitude
      Data hd hs g hg hTarget hActive input length tau ch nu p hp)
  have hSlow : incrementsGlobalSpatialDerivative (I := 𝓙)
      (round3ParameterPrimaryAmplitude F hF gO input length tau channel nu) (p,x) =
      incrementsGlobalSpatialDerivative (I := 𝓙)
        (fullIncrementNovPrimaryAmplitude (fun p x => Data.F (p,x)) g input hActive
          length tau channel nu) (p,x) := by
    unfold incrementsGlobalSpatialDerivative
    rw [hAmp channel]
    rw [congrFun (hAmp channel) x]
  change round3ParameterPrimaryCoefficient F hF gO input length tau channel nu (p,x) = _
  simp only [round3ParameterPrimaryCoefficient,fullIncrementNovPrimaryCoefficient,hSlow,
    congrFun (hAmp (!channel)) x]
  rfl

theorem incrementsCompletion_original_open_primary_mean
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
    (fun p x => Data.F (p,x)))
  (hg : ∀ (nu : Fin Data.primaryCount) (beta : Β), Round3ParameterChartPreserves (g.chart nu beta))
  (hTarget : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × D),
    z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
  (hActive : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × M),
    z ∈ (g.chart nu beta).source →
    ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
  (length : ℕ) (tau : ℝ)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    round3ParameterPrimaryMean (fullIncrementNovOriginalSourceSlice Data)
      (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (fullIncrementNovOriginalOpenFamily Data g hTarget) input length tau p x =
    fullIncrementNovPrimaryMean (fun p x => Data.F (p,x)) g input hActive length tau p x := by
  have hCoefficient (channel : Bool) (nu : Fin Data.primaryCount) :=
    incrementsCompletion_original_open_primary_coefficient Data hd hs g hg hTarget hActive
      input length tau channel nu p hp x
  simp only [round3ParameterPrimaryMean,fullIncrementNovPrimaryMean,hCoefficient]

theorem incrementsCompletion_original_open_primary_meanError
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
  (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
  (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Β)
    (fun p x => Data.F (p,x)))
  (hg : ∀ (nu : Fin Data.primaryCount) (beta : Β), Round3ParameterChartPreserves (g.chart nu beta))
  (hTarget : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × D),
    z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
  (hActive : ∀ (nu : Fin Data.primaryCount) (beta : Β) (z : P × M),
    z ∈ (g.chart nu beta).source →
    ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (z.1,x)))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
  (length : ℕ) (tau : ℝ)
    (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    round3ParameterPrimaryMeanError (fullIncrementNovOriginalSourceSlice Data)
      (fullIncrementNov_original_source_slice_smooth Data hd hs)
      (fullIncrementNovOriginalOpenFamily Data g hTarget) input length tau p x =
    fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x)) g input hActive length tau p x := by
  simp only [round3ParameterPrimaryMeanError,fullIncrementNovPrimaryMeanError,
    incrementsCompletion_original_open_primary_mean Data hd hs g hg hTarget hActive
      input length tau p hp x]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_open_primary_extension
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_open_primary_amplitude
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_open_primary_coefficient
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_open_primary_mean
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_original_open_primary_meanError
