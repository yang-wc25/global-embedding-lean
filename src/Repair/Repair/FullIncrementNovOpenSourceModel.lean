import Repair.FullIncrementNovOriginalPrimaryFormula
import Repair.FullIncrementNovOpenPreparedMean
import Smoothing.Round3ParameterNativeRestriction

/-! An internal source-slice model for reusing the already verified finite
primary/secondary solver.  It agrees with the unchanged original F at every
point of parameterOpen, and each source slice is smooth by construction.
No global joint smoothness is claimed.  No field of the original Data, chart,
norm, phase, decomposition or normal is replaced.  Native observers of this
auxiliary model are literally the existing actualOriginalOpenParameterSlice.
Every physical metric statement is transported back to Data.F on its original
open region, including the original source-only induced metric.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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
variable {Sub : Type*} [Fintype Sub]

def fullIncrementNovOriginalSourceSlice
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P) (x : M) : Ey :=
  if p ∈ Data.parameterOpen then Data.F (p,x) else 0

theorem fullIncrementNov_original_source_slice_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (p : P) (hp : p ∈ Data.parameterOpen) :
    fullIncrementNovOriginalSourceSlice Data p = fun x => Data.F (p,x) := by
  funext x
  simp only [fullIncrementNovOriginalSourceSlice,if_pos hp]

theorem fullIncrementNov_original_source_slice_smooth
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data) (p : P) :
    ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (fullIncrementNovOriginalSourceSlice Data p) := by
  by_cases hp : p ∈ Data.parameterOpen
  · rw [fullIncrementNov_original_source_slice_eq Data p hp]
    exact incrementsOriginal_slice_contMDiff Data hd hs p hp
  · have heq : fullIncrementNovOriginalSourceSlice Data p = fun _ => (0 : Ey) := by
      funext x
      simp only [fullIncrementNovOriginalSourceSlice,if_neg hp]
    rw [heq]
    exact contMDiff_const

theorem fullIncrementNov_original_source_native_slice
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    (fun p => fullIncrementNovOriginalSourceSlice Data ((Data.parameterChart i.2).symm p)) =
      actualOriginalOpenParameterSlice Data i := rfl

theorem fullIncrementNov_physical_primary_target_parameter_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hPreserves : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (hSource : ∀ nu beta y, y ∈ (g.chart nu beta).source → y.1 ∈ Data.parameterOpen)
    (nu : Fin Data.primaryCount) (beta : Sub) (z : P × D) (hz : z ∈ (g.chart nu beta).target) :
    z.1 ∈ Data.parameterOpen := by
  have h := hPreserves nu beta ((g.chart nu beta).symm z) ((g.chart nu beta).map_target hz)
  rw [(g.chart nu beta).right_inv hz] at h
  exact h.symm ▸ hSource nu beta _ ((g.chart nu beta).map_target hz)

def fullIncrementNovOriginalOpenFamily
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen) :
    Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fullIncrementNovOriginalSourceSlice Data) where
  phase := g.phase
  cutoff := g.cutoff
  normal := g.normal
  linearArgument := g.linearArgument
  eta := g.eta
  chart := g.chart
  inverse := g.inverse
  normal_mem := by
    intro nu beta z hz
    rw [fullIncrementNov_original_source_slice_eq Data z.1 (hTarget nu beta z hz)]
    exact g.normal_mem nu beta z hz

private theorem fullIncrementNov_native_family_eq_fields
    {Label : Type*} [Fintype Label]
    {F : Ep → M → Ey}
    (g g' : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := Sub) F)
    (hPhase : g.phase = g'.phase) (hCut : g.cutoff = g'.cutoff)
    (hNormal : g.normal = g'.normal) (hLinear : g.linearArgument = g'.linearArgument)
    (hEta : g.eta = g'.eta) (hChart : g.chart = g'.chart) (hInverse : g.inverse = g'.inverse) : g = g' := by
  cases g
  cases g'
  cases hPhase
  cases hCut
  cases hNormal
  cases hLinear
  cases hEta
  cases hChart
  cases hInverse
  rfl

theorem fullIncrementNov_prepared_open_family_native_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (G0 : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (prep : FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g G0 cT Tinv Forward Meta Rsub i) :
    actualOriginalPrimaryFamily Data hd hs hn i prep.host prep.native prep.slices prep.data
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta prep.active =
      round3ParameterNativePrimary (fullIncrementNovOriginalSourceSlice Data)
        (fullIncrementNovOriginalOpenFamily Data g hTarget) (Data.parameterChart i.2) := by
  obtain ⟨hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverse⟩ := prep.same_fields
  apply fullIncrementNov_native_family_eq_fields
  · exact hPhase
  · exact hCut
  · exact hNormal
  · exact hLinear
  · exact hEta
  · exact hChart
  · exact hInverse

theorem fullIncrementNov_original_metric_error_eq_open_source
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (U : P × M → Ey) (delta : ℝ) (p : P) (hp : p ∈ Data.parameterOpen) (x : M) :
    incrementsOriginalMetricError Data.F U Data.H delta p x =
      incrementsOriginalMetricError (fun z => fullIncrementNovOriginalSourceSlice Data z.1 z.2)
        U Data.H delta p x := by
  unfold incrementsOriginalMetricError
  dsimp only
  rw [fullIncrementNov_original_source_slice_eq Data p hp]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNovOriginalSourceSlice
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_source_slice_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_source_slice_smooth
#print axioms GlobalEmbedding.Continuation.fullIncrementNovOriginalOpenFamily
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_prepared_open_family_native_eq
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_metric_error_eq_open_source
