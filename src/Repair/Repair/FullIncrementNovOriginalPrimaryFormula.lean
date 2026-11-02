import Repair.FullIncrementNovPrimaryAtParameter
import Probes.Round3ParameterPreparedPrimaryLift

/-! The original given datum has a literal physical primary wave and mean
without requiring all parameters to lie in the original compact parameter
set.  The needed smooth source slice is derived only when an actual adapted
source is active.  The map, decomposition, phase, cutoff, normal, atlas,
sampling domains and norm definitions are not replaced or extended.

Every finite length and every real scale use this same formula.  This file
constructs the primary expression; it does not claim its missing full
increment estimates or mean-iteration domain bounds.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold IsManifold
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_original_primary_source_parameter_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (z : P × M)
    (hz : z ∈ (round3ParameterLiftedPrimaryChart Data ip nu W piece).source) :
    z.1 ∈ Data.parameterOpen := by
  have h := (round3ParameterChartPullback_source (Data.parameterChart ip).symm
    (actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native) z).mp hz
  have hActive := piece.active ((Data.parameterChart ip) z.1,z.2) h.2.1
  simpa only [(Data.parameterChart ip).left_inv h.1] using hActive.2.1

theorem fullIncrementNov_original_primary_active_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (EuclideanSpace ℝ (Fin d) × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a)) :
    ∀ nu a z, z ∈ ((round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece).chart nu a).source →
      ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (z.1,x)) := by
  intro nu a z hz
  exact incrementsOriginal_slice_contMDiff Data hd hs z.1
    (fullIncrementNov_original_primary_source_parameter_open Data (ip nu a) nu (W nu a) (piece nu a) z hz)

variable
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    {Sub : Type*} [Fintype Sub]
    (ip : Fin Data.primaryCount → Sub → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Sub → Set (EuclideanSpace ℝ (Fin d) × M))
    (piece : ∀ nu a, Round3PreparedPrimaryPiece Data (ip nu a) nu (W nu a))
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))

def fullIncrementNovOriginalPrimaryWave (length : ℕ) (tau : ℝ) : P × M → Ey :=
  fullIncrementNovPrimaryWave (fun p x => Data.F (p,x))
    (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) input
    (fullIncrementNov_original_primary_active_smooth Data hd hs hn ip W piece) length tau

def fullIncrementNovOriginalPrimaryMean (length : ℕ) (tau : ℝ) :
    (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) :=
  fullIncrementNovPrimaryMean (fun p x => Data.F (p,x))
    (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) input
    (fullIncrementNov_original_primary_active_smooth Data hd hs hn ip W piece) length tau

def fullIncrementNovOriginalPrimaryMeanError (length : ℕ) (tau : ℝ) :
    (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) :=
  fullIncrementNovPrimaryMeanError (fun p x => Data.F (p,x))
    (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) input
    (fullIncrementNov_original_primary_active_smooth Data hd hs hn ip W piece) length tau

theorem fullIncrementNov_original_primary_wave_eq_of_global_slices
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x))) (length : ℕ) (tau : ℝ) :
    fullIncrementNovOriginalPrimaryWave Data hd hs hn ip W piece input length tau =
      round3ParameterPrimaryWave (fun p x => Data.F (p,x)) hF
        (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) input length tau :=
  fullIncrementNov_primary_wave_eq _ _ _ _ hF
    (round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn ip W piece) length tau

theorem fullIncrementNov_original_primary_mean_eq_of_global_slices
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fun x => Data.F (p,x))) (length : ℕ) (tau : ℝ) (p : P) (x : M) :
    fullIncrementNovOriginalPrimaryMean Data hd hs hn ip W piece input length tau p x =
      round3ParameterPrimaryMean (fun p x => Data.F (p,x)) hF
        (round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece) input length tau p x :=
  fullIncrementNov_primary_mean_eq _ _ _ _ hF
    (round3ParameterOriginalPrimaryFamily_preserves Data hd hs hn ip W piece) length tau p x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_primary_source_parameter_open
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_primary_active_smooth
#print axioms GlobalEmbedding.Continuation.fullIncrementNovOriginalPrimaryWave
#print axioms GlobalEmbedding.Continuation.fullIncrementNovOriginalPrimaryMean
#print axioms GlobalEmbedding.Continuation.fullIncrementNovOriginalPrimaryMeanError
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_primary_wave_eq_of_global_slices
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_primary_mean_eq_of_global_slices
