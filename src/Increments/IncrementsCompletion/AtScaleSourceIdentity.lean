import IncrementsCompletion.AtScaleMeanPreparation
import Repair.FullIncrementNovOpenSourceModel

/-! The seven unchanged actual fields identify the native family with the
existing open source-slice model. No all-scale refinement is consumed. -/

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

private theorem incrementsCompletion_at_scale_native_family_eq_fields
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

theorem incrementsCompletion_at_scale_open_family_native_eq
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Data.primaryCount) (Β := Sub)
      (fun p x => Data.F (p,x)))
    (hTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.1 ∈ Data.parameterOpen)
    (G0 : Set (P × M)) (cT : ℝ) (Tinv Forward Meta : ℕ → ℝ) (Rsub : ℕ)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (preparedScale : ℝ)
    (prep : IncrementsCompletionAtScaleMeanPreparation Data hd hs hn g G0 cT Tinv Forward Meta Rsub preparedScale i) :
    actualOriginalPrimaryFamily Data hd hs hn i prep.host prep.native prep.slices prep.data
      (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g (Data.parameterChart i.2)).eta prep.active =
      round3ParameterNativePrimary (fullIncrementNovOriginalSourceSlice Data)
        (fullIncrementNovOriginalOpenFamily Data g hTarget) (Data.parameterChart i.2) := by
  obtain ⟨hPhase,hCut,hNormal,hLinear,hEta,hChart,hInverse⟩ := prep.same_fields
  apply incrementsCompletion_at_scale_native_family_eq_fields
  · exact hPhase
  · exact hCut
  · exact hNormal
  · exact hLinear
  · exact hEta
  · exact hChart
  · exact hInverse

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_open_family_native_eq
