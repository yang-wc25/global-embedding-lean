import NormalPolar.ParameterDisplacementCombinedParameterNative
import NormalPolar.ParameterDisplacementBackgroundParameterNaturality

/-! The physical common primary whose background input is the literal j-th
forced mean iterate. The native realization uses its own same finite
recurrence, and equality is proved from the primitive chart data, not assumed
for either completed input or wave. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))

theorem actualParameterProbeCombinedPrimary_input_slice_congr
    (input₁ input₂ : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (b : P) (hinput : input₁ b = input₂ b) (u : Fin p → ℝ) (x : M) :
    actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input₁ u (b,x) =
      actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input₂ u (b,x) := by
  rw [actualParameterProbeCombinedPrimary_eq,actualParameterProbeCombinedPrimary_eq,
    actualParameterPrimaryWave_input_slice_congr F hF g input₁ input₂ backgroundLength tau b hinput hg x]

def actualParameterProbeIteratedPrimary
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (j : ℕ) (u : Fin p → ℝ) : P × M → V :=
  actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a
    (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
      (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) j u) u

theorem actualParameterProbeIteratedPrimary_pullback
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (B : OpenPartialHomeomorph P Q)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (j : ℕ) (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterProbeIteratedPrimary (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
      (fun l t => vf l (B.symm t)) (fun l z => phase l (B.symm z.1,z.2))
      tau delta backgroundLength probeLength (fun l => round3ParameterChartPullback B (a l))
      (fun t => target (B.symm t)) j u (b,x) =
    actualParameterProbeIteratedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a target j u (B.symm b,x) := by
  let probe := actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a
  let probeLocal := actualParameterPrescribedNativeMean label
    (fun t => F (B.symm t)) (fun t => hF (B.symm t))
    (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
    (fun l z => phase l (B.symm z.1,z.2)) tau probeLength
    (fun l => round3ParameterChartPullback B (a l))
  let input := actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target probe j u
  let localInput := actualParameterBackgroundMeanIterate (fun t => F (B.symm t))
    (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
    backgroundLength tau delta (fun t => target (B.symm t)) probeLocal j u
  have hinput : localInput b = (fun t => input (B.symm t)) b := by
    funext y
    exact actualParameterBackgroundMeanIterate_pullback F hF g backgroundLength tau delta target probe B hg probeLocal
      (fun v t ht z => actualParameterPrescribedNativeMean_pullback label F hF c vf phase tau probeLength a ha B v t ht z)
      j u b hb y
  have hlocal := actualParameterProbeCombinedPrimary_input_slice_congr
    (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
    label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
    (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
    (fun l => round3ParameterChartPullback B (a l)) localInput (fun t => input (B.symm t))
    (fun l k => round3ParameterChartPullback_preserves B (g.chart l k) (hg l k)) b hinput u x
  exact hlocal.trans (actualParameterProbeCombinedPrimary_pullback F hF g label c vf phase tau delta
    backgroundLength probeLength a B hg ha input u b hb x)

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

theorem actualParameterProbeIteratedPrimary_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (j : ℕ) (u : Fin p → ℝ) :
    actualParameterProbeIteratedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a target j u =
    round4ParameterProbeCombinedPrimary F hF (g.toNative F) label c vf phase tau delta backgroundLength probeLength a
      (round4ActualBackgroundMeanIterate F hF (g.toNative F) backgroundLength tau delta target
        (round4PrescribedNativeMean label F hF c vf phase tau probeLength a) j u) u := by
  unfold actualParameterProbeIteratedPrimary
  rw [actualParameterBackgroundMeanIterate_native]
  rfl

theorem actualParameterProbeIteratedPrimary_native_pullback
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (j : ℕ) (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    let Fbar := fun t => F (B.symm t)
    let hFbar := fun t => hF (B.symm t)
    let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
    let cbar := fun l t => c l (B.symm t)
    let vfbar := fun l t => vf l (B.symm t)
    let phasebar := fun l z => phase l (B.symm z.1,z.2)
    let abar := fun l => round3ParameterChartPullback B (a l)
    round4ParameterProbeCombinedPrimary Fbar hFbar gbar label cbar vfbar phasebar tau delta
      backgroundLength probeLength abar
      (round4ActualBackgroundMeanIterate Fbar hFbar gbar backgroundLength tau delta
        (fun t => target (B.symm t))
        (round4PrescribedNativeMean label Fbar hFbar cbar vfbar phasebar tau probeLength abar) j u) u (b,x) =
    actualParameterProbeIteratedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a target j u (B.symm b,x) := by
  intro Fbar hFbar gbar cbar vfbar phasebar abar
  rw [← actualParameterProbeIteratedPrimary_native]
  exact actualParameterProbeIteratedPrimary_pullback F hF g label c vf phase tau delta
    backgroundLength probeLength a target B hg ha j u b hb x

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterProbeIteratedPrimary_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeIteratedPrimary_native_pullback
