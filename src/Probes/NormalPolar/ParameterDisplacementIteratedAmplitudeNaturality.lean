import NormalPolar.ParameterDisplacementCombinedIterateNaturality
import NormalPolar.ParameterDisplacementCombinedAmplitudeLocality

/-! The actual complete amplitudes at the real finite background iterate.
Slice locality removes the distinction between the native recurrence and
the literal pullback of the physical recurrence before forming any of the
mixed-secondary forcing coefficients. -/

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

def actualParameterProbeIteratedAmplitude
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (j : ℕ) (u : Fin p → ℝ) (imag : Bool) : (Λ ⊕ Fin r) → P × M → V :=
  actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a
    (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
      (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) j u) u imag

theorem actualParameterProbeIteratedAmplitude_pullback
    (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (B : OpenPartialHomeomorph P Q)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (j : ℕ) (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterProbeIteratedAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
      (fun l t => vf l (B.symm t)) (fun l z => phase l (B.symm z.1,z.2))
      tau delta backgroundLength probeLength (fun l => round3ParameterChartPullback B (a l))
      (fun t => target (B.symm t)) j u imag l (b,x) =
    actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target j u imag l (B.symm b,x) := by
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
  have hlocal := actualParameterProbeCombinedAmplitude_input_slice_congr
    (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
    label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
    tau delta backgroundLength probeLength (fun l => round3ParameterChartPullback B (a l))
    localInput (fun t => input (B.symm t))
    (fun l k => round3ParameterChartPullback_preserves B (g.chart l k) (hg l k)) b hinput u imag l x
  exact hlocal.trans (actualParameterProbeCombinedAmplitude_pullback F hF g label c vf tau delta
    backgroundLength probeLength a B hg ha input u imag l b hb x)

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

theorem actualParameterProbeIteratedAmplitude_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (j : ℕ) (u : Fin p → ℝ) (imag : Bool) :
    actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target j u imag =
    round4ParameterProbeCombinedAmplitude F hF (g.toNative F) label c vf tau delta backgroundLength probeLength a
      (round4ActualBackgroundMeanIterate F hF (g.toNative F) backgroundLength tau delta target
        (round4PrescribedNativeMean label F hF c vf phase tau probeLength a) j u) u imag := by
  unfold actualParameterProbeIteratedAmplitude
  rw [actualParameterBackgroundMeanIterate_native]
  rfl

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterProbeIteratedAmplitude_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeIteratedAmplitude_native
