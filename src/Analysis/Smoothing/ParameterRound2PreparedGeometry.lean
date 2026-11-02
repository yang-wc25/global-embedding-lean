import Smoothing.ParameterRound2PreparedAtlas
import Smoothing.TensorLocalPrepared

/-!
# The actual compact preparation feeds the local parameter smoothing interface

Forgetting the cover does not alter a chart, buffer, support, raw cutoff or
jet bound. The original maximum support degree controls the local provider
vertex degrees. Thus the genuinely constructed compact parameter geometry can
be passed directly to the already proved local full-joint map/tensor endpoint.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
noncomputable section

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- The same actual global raw preparation, viewed locally on any requested
set. No choice of new cutoffs, derivatives or support graph is made. -/
def parameterRound2_localPreparationOfGlobal
    (A : BufferedAtlas X E) {B₀ T : ℕ → ℝ} {D : ℕ}
    (R : TensorRawCutoffPreparation A B₀ T D) (Q : Set X) :
    TensorLocalRawPreparation (tensorChartFamilyOfAtlas A) Q B₀ T D where
  raw := R.raw
  smooth := R.smooth
  plateau_on := fun x _ => R.plateau_cover x
  inner_support := R.inner_support
  enlarged := A.support
  enlarged_support := R.enlarged_support
  degree := fun i => (tensorSupportDegree_le_original A i).trans R.degree
  own_jets := R.own_jets
  transition_jets := R.transition_jets

/-- The actual source and parameter sampling sets agree literally after
forgetting the global cover. -/
theorem parameterRound2_sampling_familyOfAtlas (A : BufferedAtlas X E)
    (i : Fin A.count) :
    tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas A) i = bufferedSamplingCoordinates A i := rfl

/-- Compact geometry constructs every datum needed by the local parameter
preparation. The profiles precede all fields, smoothing scales and budgets. -/
theorem parameterRound2_exists_compact_local_prepared_geometry
    [FiniteDimensional ℝ E] [CompactSpace X] [T2Space X] :
    ∃ A : BufferedAtlas X E, IsSmoothBufferedAtlas A ∧
      ∃ B₀ T : ℕ → ℝ, (∀ k, 0 ≤ B₀ k) ∧ (∀ k, 0 ≤ T k) ∧
        Nonempty (TensorLocalRawPreparation (tensorChartFamilyOfAtlas A) univ B₀ T A.supportDegree) ∧
        ∃ Omega : Fin A.count → Set E,
          ∀ i, IsCompact (Omega i) ∧ Omega i ⊆ (A.chart i).target ∧
            closure (tensorLocalSamplingCoordinates (tensorChartFamilyOfAtlas A) i) ⊆ Omega i := by
  obtain ⟨A, hA, B₀, T, hB₀, hT, ⟨R⟩, Omega, hOmega⟩ :=
    parameterRound2_exists_compact_prepared_bufferedAtlas (E := E) (X := X)
  exact ⟨A, hA, B₀, T, hB₀, hT, ⟨parameterRound2_localPreparationOfGlobal A R univ⟩,
    Omega, hOmega⟩

#print axioms parameterRound2_localPreparationOfGlobal
#print axioms parameterRound2_exists_compact_local_prepared_geometry
end
end GlobalEmbedding.Continuation
