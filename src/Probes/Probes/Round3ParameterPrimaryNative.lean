import Probes.Round3ParameterPrimaryConstruction

/-! The general-parameter definitions specialize definitionally to the existing
native formulas.  This is a binding to the original finite solver, not a second
wave selected using desired estimates. -/

noncomputable section
open GlobalEmbedding.Paper Manifold
open scoped ContDiff
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
  (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))

def Round3ParameterPrimaryFamily.toNative
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F) :
    IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F where
  phase := g.phase
  cutoff := g.cutoff
  normal := g.normal
  linearArgument := g.linearArgument
  eta := g.eta
  chart := g.chart
  inverse := g.inverse
  normal_mem := g.normal_mem

def Round3ParameterPrimaryFamily.ofNative
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F) :
    Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F where
  phase := g.phase
  cutoff := g.cutoff
  normal := g.normal
  linearArgument := g.linearArgument
  eta := g.eta
  chart := g.chart
  inverse := g.inverse
  normal_mem := g.normal_mem

variable (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ)

theorem round3ParameterPrimary_native_localZ :
    incrementsGlobalPrimaryLocalZ F hF (g.toNative F) input length tau =
      round3ParameterPrimaryLocalZ F hF g input length tau := rfl

theorem round3ParameterPrimary_native_extension :
    incrementsGlobalPrimaryExtension F hF (g.toNative F) input length tau =
      round3ParameterPrimaryExtension F hF g input length tau := rfl

theorem round3ParameterPrimary_native_wave :
    incrementsGlobalPrimaryWave F hF (g.toNative F) input length tau =
      round3ParameterPrimaryWave F hF g input length tau := rfl

theorem round3ParameterPrimary_native_mean :
    incrementsGlobalPrimaryMean F hF (g.toNative F) input length tau =
      round3ParameterPrimaryMean F hF g input length tau := rfl

theorem round3ParameterPrimary_native_meanError :
    incrementsGlobalPrimaryMeanError F hF (g.toNative F) input length tau =
      round3ParameterPrimaryMeanError F hF g input length tau := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimary_native_wave
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimary_native_mean
