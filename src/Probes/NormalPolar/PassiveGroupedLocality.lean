import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude
import NormalPolar.ParameterDisplacementPrimaryInputLocality

/-! Spatial slice locality for the actual grouped physical first array.
The original labels and all pieces are fixed. Only equality of the input
tensor and the parameter value on the same physical slice is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : (l : Fin r) → Pieces l → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (k : Pieces l) → (b : P) →
    (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l k b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength : ℕ)
  (a : (l : Fin r) → Pieces l →
    OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (input₁ input₂ : (b : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (u₁ u₂ : P → Fin p → ℝ) (b : P)
  (hinput : input₁ b = input₂ b) (hu : u₁ b = u₂ b)

include hg hinput hu

theorem passiveGrouped_amplitude_slice_congr
    (imag : Bool) (l : Λ ⊕ Fin r) (x : M) :
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input₁ u₁ imag l (b,x) =
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input₂ u₂ imag l (b,x) := by
  cases l with
  | inl l =>
    exact congrArg (fun v : V => delta • v)
      (actualParameterPrimaryAmplitude_input_slice_congr F hF g input₁ input₂
        backgroundLength tau b hinput hg (!imag) l x)
  | inr l =>
    exact congrArg
      (fun v => jointGroupedParameterPrescribedAmplitude label F hF c vf
        tau probeLength a imag v l (b,x)) hu

theorem passiveGrouped_primary_slice_congr (x : M) :
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input₁ u₁ (b,x) =
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input₂ u₂ (b,x) := by
  unfold actualProbeInitialGroupedPrimary
  apply Finset.sum_congr rfl
  intro l _
  rw [passiveGrouped_amplitude_slice_congr F hF g label c vf tau delta
    backgroundLength probeLength a input₁ input₂ hg u₁ u₂ b hinput hu false l x,
    passiveGrouped_amplitude_slice_congr F hF g label c vf tau delta
      backgroundLength probeLength a input₁ input₂ hg u₁ u₂ b hinput hu true l x]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveGrouped_amplitude_slice_congr
#print axioms GlobalEmbedding.Continuation.passiveGrouped_primary_slice_congr
