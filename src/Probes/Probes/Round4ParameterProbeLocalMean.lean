import Probes.Round4ParameterProbeCombinedPrimary

/-! The physical combined mean identity only uses native differentiability
at the point being observed. This version retains the original working set;
it requires no regularity of chart extensions outside that set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Exact same-array residual on the actual working domain. The only amplitude
regularity input is at the current point, as furnished by a smooth germ on W. -/
theorem round4ParameterProbeCombinedMean_actual_iterate_residual_on
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hdelta : delta ≠ 0) (j : ℕ) (u : Fin p → ℝ) (W : Set (Ep × M))
    (hamp : ∀ b x, (b,x) ∈ W → ∀ nu ch, MDifferentiableAt I 𝓘(ℝ,V)
      (fun y => incrementsGlobalPrimaryAmplitude F hF g
        (round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target
          (round4PrescribedNativeMean label F hF c vf phase tau probeLength a) (j+1) u)
        backgroundLength tau ch nu (b,y)) x) :
    let probe := round4PrescribedNativeMean label F hF c vf phase tau probeLength a
    let A := round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target probe
    ∀ b x, (b,x) ∈ W →
      round4ParameterProbeCombinedMean F hF g label c vf phase tau delta
        backgroundLength probeLength a (A (j+1) u) u b x - delta^2 • target b x =
      delta^2 • (incrementsGlobalPrimaryMeanError F hF g (A (j+1) u) backgroundLength tau b x -
        incrementsGlobalPrimaryMeanError F hF g (A j u) backgroundLength tau b x) := by
  intro probe A b x hx
  rw [round4ParameterProbeCombinedMean_eq F hF g label c vf phase tau delta
    backgroundLength probeLength a (A (j+1) u) u b x (hamp b x hx)]
  exact congrFun (congrFun (round4ActualBackgroundMeanIterate_physical_residual
    F hF g backgroundLength tau delta hdelta target probe j u) b) x

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbeCombinedMean_actual_iterate_residual_on
