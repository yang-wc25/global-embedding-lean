import NormalPolar.ParameterDisplacementBackgroundParameterNaturality

/-!
# Global parameter substitution before the actual background iteration

For a parameter input u(p), the finite spatial solver sees u(p) as fixed on
each source slice.  Its diagonal substitution therefore equals the actual
iteration driven by the single global tensor p ↦ Probe(u(p),p).  This identity
allows that one global tensor germ to receive original joint-norm estimates.
It does not infer mixed parameter estimates from fixed-u estimates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N p : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (length : ℕ) (tau delta : ℝ)
  (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (probe : (Fin p → ℝ) → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (u : P → Fin p → ℝ)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))

include hg

theorem actual_parameter_background_diagonal_iterate (j : ℕ) (b : P) (x : M) :
    actualParameterBackgroundMeanIterate F hF g length tau delta target
      (fun (_ : Fin 0 → ℝ) b => probe (u b) b) j 0 b x =
    actualParameterBackgroundMeanIterate F hF g length tau delta target probe j (u b) b x := by
  induction j generalizing b x with
  | zero => rfl
  | succ j ih =>
    let globalInput := actualParameterBackgroundMeanIterate F hF g length tau delta target
      (fun (_ : Fin 0 → ℝ) b => probe (u b) b) j 0
    let fixedInput := actualParameterBackgroundMeanIterate F hF g length tau delta target probe j (u b)
    have hs : globalInput b = fixedInput b := funext (fun y => ih b y)
    change target b x - (delta^2)⁻¹ • probe (u b) b x -
      round3ParameterPrimaryMeanError F hF g globalInput length tau b x =
        target b x - (delta^2)⁻¹ • probe (u b) b x -
          round3ParameterPrimaryMeanError F hF g fixedInput length tau b x
    rw [actualParameterPrimaryMeanError_input_slice_congr
      F hF g globalInput fixedInput length tau b hs hg x]

/-- The whole background wave, including its actual finite spatial
reconstruction, is unchanged by performing this global substitution first. -/
theorem actual_parameter_background_diagonal_wave (j : ℕ) :
    round3ParameterPrimaryWave F hF g
      (actualParameterBackgroundMeanIterate F hF g length tau delta target
        (fun (_ : Fin 0 → ℝ) b => probe (u b) b) j 0) length tau =
      fun z => round3ParameterPrimaryWave F hF g
        (actualParameterBackgroundMeanIterate F hF g length tau delta target probe j (u z.1))
        length tau z := by
  funext z
  exact actualParameterPrimaryWave_input_slice_congr F hF g _ _ length tau z.1
    (funext (fun x => actual_parameter_background_diagonal_iterate
      F hF g length tau delta target probe u hg j z.1 x)) hg z.2

/-- All observed joint derivatives are derivatives of the same globally
defined map.  No regularity of the diagonal parameter function is needed for
this identity; actual smoothness and budgets must be proved for that function. -/
theorem actual_parameter_background_diagonal_wave_jets
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (observer : Y → P × M) (j k : ℕ) (y : Y) :
    iteratedFDeriv ℝ k (round3ParameterPrimaryWave F hF g
      (actualParameterBackgroundMeanIterate F hF g length tau delta target
        (fun (_ : Fin 0 → ℝ) b => probe (u b) b) j 0) length tau ∘ observer) y =
    iteratedFDeriv ℝ k (fun z => round3ParameterPrimaryWave F hF g
      (actualParameterBackgroundMeanIterate F hF g length tau delta target probe j (u (observer z).1))
      length tau (observer z)) y := by
  rw [actual_parameter_background_diagonal_wave F hF g length tau delta target probe u hg j]
  rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_parameter_background_diagonal_iterate
#print axioms GlobalEmbedding.Continuation.actual_parameter_background_diagonal_wave
#print axioms GlobalEmbedding.Continuation.actual_parameter_background_diagonal_wave_jets
