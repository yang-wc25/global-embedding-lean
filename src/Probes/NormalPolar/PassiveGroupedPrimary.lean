import NormalPolar.PassiveGroupedPrescribed
import NormalPolar.PassiveParameterPrimary
import NormalPolar.ActualProbeInitialSupplyGroupedAmplitude

/-! The actual original-label grouped primary under the passive lift.
The background finite reconstruction and every subordinate prescribed
reconstruction use the same seed primitive fields and the same lengths. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M S P Λ Β : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable (s₀ : S) (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : (l : Fin r) → Pieces l → S → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (k : Pieces l) → (s : S) →
    (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F s) (c l k s x))
  (phase : Fin r → S × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength : ℕ)
  (a : (l : Fin r) → Pieces l →
    OpenPartialHomeomorph (S × M) (S × EuclideanSpace ℝ (Fin (m+1))))
  (input : (s : S) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))

theorem passiveGroupedPrimary_amplitude
    (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : P) (x : M) :
    actualProbeInitialGroupedAmplitude (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau delta
      backgroundLength probeLength (fun l k => passiveParameterChart s₀ (a l k))
      (fun _ => input s₀) (fun _ => u) imag l (b,x) =
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input (fun _ => u) imag l (s₀,x) := by
  cases l with
  | inl l =>
    exact congrArg (fun v : V => delta • v)
      (passiveParameterPrimary_amplitude s₀ F hF g input backgroundLength tau (!imag) l b x)
  | inr l =>
    exact passiveGroupedPrescribed_amplitude s₀ label F hF c vf tau probeLength a imag l u b x

theorem passiveGroupedPrimary_wave
    (u : Fin p → ℝ) (b : P) (x : M) :
    actualProbeInitialGroupedPrimary (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau delta backgroundLength probeLength
      (fun l k => passiveParameterChart s₀ (a l k))
      (fun _ => input s₀) (fun _ => u) (b,x) =
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a input (fun _ => u) (s₀,x) := by
  unfold actualProbeInitialGroupedPrimary
  apply Finset.sum_congr rfl
  intro l _
  rw [passiveGroupedPrimary_amplitude s₀ F hF g label c vf tau delta
      backgroundLength probeLength a input u false l b x,
    passiveGroupedPrimary_amplitude s₀ F hF g label c vf tau delta
      backgroundLength probeLength a input u true l b x]
  cases l <;> rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveGroupedPrimary_amplitude
#print axioms GlobalEmbedding.Continuation.passiveGroupedPrimary_wave
