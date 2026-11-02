import NormalPolar.ActualProbeSecondaryParameterNaturality
import Probes.ActualSecondaryConstructedSum

/-!
# One physical secondary array and its native chart representatives

`ActualProbeSecondaryParameterSource` stores only the actual parameter-space
chart, inverse spatial map, two forcing inputs, and phase.  Its wave is the
full finite inhomogeneous reconstruction.  `ActualProbeSecondaryParameterBinding`
matches these primitive fields to an existing native piece; it has no wave,
jet, or output-budget field.  The complete ordered signed array is retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

structure ActualProbeSecondaryParameterSource (P M : Type*) [TopologicalSpace P]
    [TopologicalSpace M] (m : ℕ) where
  c : P → EuclideanSpace ℝ (Fin (m + 1)) → M
  chart : OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m + 1)))
  chart_preserves : Round3ParameterChartPreserves chart
  forcingR : P × EuclideanSpace ℝ (Fin (m + 1)) → Fin (m + 1) → Fin (m + 1) → ℝ
  forcingI : P × EuclideanSpace ℝ (Fin (m + 1)) → Fin (m + 1) → Fin (m + 1) → ℝ
  phase : P × M → ℝ

variable {m N : ℕ} {P M : Type*} [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def ActualProbeSecondaryParameterSource.wave
    (s : ActualProbeSecondaryParameterSource P M m)
    (F : P → M → V)
    (hF : ∀ p, ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, V) ∞ (F p))
    (tau : ℝ) (length : ℕ) : P × M → V :=
  round3ParameterSupportedWave F hF s.c s.forcingR s.forcingI s.chart s.phase tau length

def actualParameterSecondarySourceSum
    {Label Sub : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, V) ∞ (F p))
    (source : ActualSecondarySignedRecord Label → Sub → ActualProbeSecondaryParameterSource P M m)
    (tau : ℝ) (length : ℕ) : P × M → V :=
  actualSecondaryRefinedNonzeroSum (fun r a =>
    if h : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then
      (source ⟨r, h⟩ a).wave F hF tau length else 0)

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {n j : ℕ} {ell Mg CH delta : ℝ} {W : Set (Ep × M)}

/-- Only primitive field bindings on the genuine chart domain. -/
structure ActualProbeSecondaryParameterBinding
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, V) ∞ (F p))
    (B : OpenPartialHomeomorph P Ep) (s : ActualProbeSecondaryParameterSource P M m)
    (d : ActualSecondaryPieceData (m := m)
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) n j ell Mg CH delta W) : Prop where
  c_eq : d.c = fun t => s.c (B.symm t)
  chart_eq : d.chart = round3ParameterChartPullback B s.chart
  phase_eq : ∀ t ∈ B.target, ∀ x, d.phase (t, x) = s.phase (B.symm t, x)
  forcingR_eq : ∀ t ∈ B.target, ∀ x, (B.symm t, x) ∈ s.chart.target →
    d.hR (t, x) = s.forcingR (B.symm t, x)
  forcingI_eq : ∀ t ∈ B.target, ∀ x, (B.symm t, x) ∈ s.chart.target →
    d.hI (t, x) = s.forcingI (B.symm t, x)

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (B : OpenPartialHomeomorph P Ep)

theorem actual_secondary_parameter_native_piece
    (s : ActualProbeSecondaryParameterSource P M m)
    (d : ActualSecondaryPieceData (m := m)
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) n j ell Mg CH delta W)
    (h : ActualProbeSecondaryParameterBinding F hF B s d)
    (tau : ℝ) (length : ℕ) (t : Ep) (ht : t ∈ B.target) (x : M) :
    d.wave tau length (t, x) = s.wave F hF tau length (B.symm t, x) := by
  change round3ParameterSupportedWave
    (fun q => F (B.symm q)) (fun q => hF (B.symm q)) d.c d.hR d.hI d.chart d.phase
      tau length (t, x) = _
  rw [h.c_eq, h.chart_eq]
  have he := actual_secondary_parameter_supported_pullback F hF s.c s.chart B
    s.forcingR s.forcingI d.hR d.hI h.forcingR_eq h.forcingI_eq s.chart_preserves
    s.phase tau length t ht x
  simpa only [ActualProbeSecondaryParameterSource.wave, round3ParameterSupportedWave,
    h.phase_eq t ht x] using he

variable {Label Sub : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
  (source : ActualSecondarySignedRecord Label → Sub → ActualProbeSecondaryParameterSource P M m)
  (data : ActualSecondarySignedRecord Label → Sub →
    ActualSecondaryPieceData (m := m) (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      n j ell Mg CH delta W)
  (hdata : ∀ r a, ActualProbeSecondaryParameterBinding F hF B (source r a) (data r a))

include hdata

theorem actual_secondary_parameter_native_sum
    (tau : ℝ) (length : ℕ) (t : Ep) (ht : t ∈ B.target) (x : M) :
    actualConstructedSecondarySum (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      data tau length (t, x) =
    actualParameterSecondarySourceSum F hF source tau length (B.symm t, x) := by
  unfold actualConstructedSecondarySum actualParameterSecondarySourceSum
    actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [actualConstructedSecondaryFamily]
  split_ifs with h
  · exact actual_secondary_parameter_native_piece F hF B (source ⟨((ν, μ), q), h⟩ a)
      (data ⟨((ν, μ), q), h⟩ a) (hdata _ _) tau length t ht x
  · rfl

theorem actual_secondary_parameter_native_sum_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (tau : ℝ) (length : ℕ) (b : Y → Ep) (x : Y → M) (y : Y)
    (hb : ContinuousAt b y) (hy : b y ∈ B.target) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z => actualConstructedSecondarySum
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) data tau length (b z, x z)) y =
    iteratedFDeriv ℝ k (fun z => actualParameterSecondarySourceSum F hF source
      tau length (B.symm (b z), x z)) y := by
  have he : (fun z => actualConstructedSecondarySum
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) data tau length (b z, x z)) =ᶠ[𝓝 y]
      (fun z => actualParameterSecondarySourceSum F hF source tau length (B.symm (b z), x z)) := by
    filter_upwards [hb.preimage_mem_nhds (B.open_target.mem_nhds hy)] with z hz
    exact actual_secondary_parameter_native_sum F hF B source data hdata tau length (b z) hz (x z)
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_parameter_native_piece
#print axioms GlobalEmbedding.Continuation.actual_secondary_parameter_native_sum
#print axioms GlobalEmbedding.Continuation.actual_secondary_parameter_native_sum_jets
