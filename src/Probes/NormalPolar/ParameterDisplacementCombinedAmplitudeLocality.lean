import NormalPolar.ParameterDisplacementPrimaryInputLocality
import NormalPolar.ParameterDisplacementCombinedParameterNaturality

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

theorem actualParameterProbeCombinedAmplitude_input_slice_congr
    (input₁ input₂ : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (b : P) (hinput : input₁ b = input₂ b) (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (x : M) :
    actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input₁ u imag l (b,x) =
      actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input₂ u imag l (b,x) := by
  cases l with
  | inl l =>
    simp only [actualParameterProbeCombinedAmplitude,Sum.elim_inl]
    rw [actualParameterPrimaryAmplitude_input_slice_congr F hF g input₁ input₂ backgroundLength tau b hinput hg (!imag) l x]
  | inr l =>
    simp only [actualParameterProbeCombinedAmplitude,Sum.elim_inr]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedAmplitude_input_slice_congr
