import NormalPolar.ParameterDisplacementPrimaryInputLocality
import NormalPolar.ParameterDisplacementPrescribedMeanNaturality
import Probes.Round4ActualProbeBackgroundIteration

/-!
# The actual finite background substitutions on the physical parameter space

The recurrence uses the genuine mean of the same finite primary solver and
the complete prescribed native mean. Its parameter-chart naturality is an
induction using actual parameter-slice locality. It requires no global
identity outside the chart target and no precomputed output iterate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def actualParameterBackgroundMeanIterate
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ)
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (probe : (Fin p → ℝ) → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) :
    ℕ → (Fin p → ℝ) → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)
  | 0 => fun _ => target
  | j+1 => fun u => target - (delta^2)⁻¹ • probe u -
      round3ParameterPrimaryMeanError F hF g
        (actualParameterBackgroundMeanIterate F hF g length tau delta target probe j u) length tau

theorem actualParameterBackgroundMeanIterate_pullback
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ)
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (probe : (Fin p → ℝ) → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (B : OpenPartialHomeomorph P Q)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (probeLocal : (Fin p → ℝ) → (b : Q) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hprobe : ∀ u b, b ∈ B.target → ∀ x, probeLocal u b x = probe u (B.symm b) x)
    (j : ℕ) (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterBackgroundMeanIterate (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) length tau delta
      (fun t => target (B.symm t)) probeLocal j u b x =
    actualParameterBackgroundMeanIterate F hF g length tau delta target probe j u (B.symm b) x := by
  induction j generalizing b x with
  | zero => rfl
  | succ j ih =>
    let localInput := actualParameterBackgroundMeanIterate (fun t => F (B.symm t))
      (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
      length tau delta (fun t => target (B.symm t)) probeLocal j u
    let input := actualParameterBackgroundMeanIterate F hF g length tau delta target probe j u
    have hs : localInput b = (fun t => input (B.symm t)) b := funext (fun y => ih b hb y)
    have hlocal := actualParameterPrimaryMeanError_input_slice_congr
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
      localInput (fun t => input (B.symm t)) length tau b hs
      (fun l k => round3ParameterChartPullback_preserves B (g.chart l k) (hg l k)) x
    have hphysical := round3ParameterPrimary_pullback_meanError F hF g B hg input length tau b hb x
    change target (B.symm b) x - (delta^2)⁻¹ • probeLocal u b x -
      round3ParameterPrimaryMeanError (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterPrimaryPullback F g B) localInput length tau b x =
      target (B.symm b) x - (delta^2)⁻¹ • probe u (B.symm b) x -
        round3ParameterPrimaryMeanError F hF g input length tau (B.symm b) x
    rw [hprobe u b hb x,hlocal,hphysical]

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

theorem actualParameterBackgroundMeanIterate_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (length : ℕ) (tau delta : ℝ)
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (probe : (Fin p → ℝ) → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)) :
    actualParameterBackgroundMeanIterate F hF g length tau delta target probe =
      round4ActualBackgroundMeanIterate F hF (g.toNative F) length tau delta target probe := by
  funext j
  induction j with
  | zero => rfl
  | succ j ih =>
    funext u
    simp only [actualParameterBackgroundMeanIterate,round4ActualBackgroundMeanIterate,
      round3ParameterPrimary_native_meanError,ih]

/-- The actual native recurrence driven by the actual complete prescribed
mean is the same finite physical recurrence through every admitted chart. -/
theorem actualParameterBackgroundMeanIterate_prescribed_native_pullback
    (F : P → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → P → D → M)
    (vf : (l : Fin r) → (b : P) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (P × M) (P × D))
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (j : ℕ) (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    round4ActualBackgroundMeanIterate (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t)))
      backgroundLength tau delta (fun t => target (B.symm t))
      (round4PrescribedNativeMean label (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
        (fun l z => phase l (B.symm z.1,z.2)) tau probeLength
        (fun l => round3ParameterChartPullback B (a l))) j u b x =
    actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
      (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) j u (B.symm b) x := by
  rw [← actualParameterBackgroundMeanIterate_native]
  exact actualParameterBackgroundMeanIterate_pullback F hF g backgroundLength tau delta target
    (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) B hg _
    (fun v t ht y => actualParameterPrescribedNativeMean_native_pullback label F hF c vf phase tau probeLength a ha B v t ht y)
    j u b hb x

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterBackgroundMeanIterate_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterBackgroundMeanIterate_native
#print axioms GlobalEmbedding.Continuation.actualParameterBackgroundMeanIterate_prescribed_native_pullback
