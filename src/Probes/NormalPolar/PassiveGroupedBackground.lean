import NormalPolar.PassiveGroupedPrimary
import NormalPolar.PassiveParameterBackground

/-! The original grouped prescribed forcing commutes with the actual finite
background iteration. Every original label first sums all its pieces and
then enters the true opposite mean, including all cross-piece terms. -/

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
  (target : (s : S) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))

theorem passiveGroupedBackground_prescribed_iterate (j : ℕ) (u : Fin p → ℝ) :
    actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) backgroundLength tau delta (fun _ => target s₀)
      (jointGroupedParameterPrescribedMean label
        (fun _ : P => F s₀) (fun _ => hF s₀)
        (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
        (fun l z => phase l (s₀,z.2)) tau probeLength
        (fun l k => passiveParameterChart s₀ (a l k))) j u =
    fun _ : P => actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
      (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a) j u s₀ := by
  have hp : jointGroupedParameterPrescribedMean label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau probeLength
      (fun l k => passiveParameterChart s₀ (a l k)) =
      fun v (_ : P) => jointGroupedParameterPrescribedMean label F hF c vf
        phase tau probeLength a v s₀ := by
    funext v b x
    exact passiveGroupedPrescribed_mean s₀ label F hF c vf phase tau probeLength a v b x
  rw [hp]
  exact passiveParameterBackground_iterate s₀ F hF g backgroundLength tau delta target _ j u

theorem passiveGroupedBackground_amplitude
    (j : ℕ) (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : P) (x : M) :
    actualProbeInitialGroupedAmplitude (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau delta
      backgroundLength probeLength (fun l k => passiveParameterChart s₀ (a l k))
      (actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
        (passiveParameterPrimary s₀ F g) backgroundLength tau delta (fun _ => target s₀)
        (jointGroupedParameterPrescribedMean label
          (fun _ : P => F s₀) (fun _ => hF s₀)
          (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
          (fun l z => phase l (s₀,z.2)) tau probeLength
          (fun l k => passiveParameterChart s₀ (a l k))) j u)
      (fun _ => u) imag l (b,x) =
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a
      (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
        (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a) j u)
      (fun _ => u) imag l (s₀,x) := by
  rw [passiveGroupedBackground_prescribed_iterate s₀ F hF g label c vf phase tau delta
    backgroundLength probeLength a target j u]
  exact passiveGroupedPrimary_amplitude s₀ F hF g label c vf tau delta
    backgroundLength probeLength a _ u imag l b x

theorem passiveGroupedBackground_primary
    (j : ℕ) (u : Fin p → ℝ) (b : P) (x : M) :
    actualProbeInitialGroupedPrimary (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau delta backgroundLength probeLength
      (fun l k => passiveParameterChart s₀ (a l k))
      (actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
        (passiveParameterPrimary s₀ F g) backgroundLength tau delta (fun _ => target s₀)
        (jointGroupedParameterPrescribedMean label
          (fun _ : P => F s₀) (fun _ => hF s₀)
          (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
          (fun l z => phase l (s₀,z.2)) tau probeLength
          (fun l k => passiveParameterChart s₀ (a l k))) j u)
      (fun _ => u) (b,x) =
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a
      (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
        (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a) j u)
      (fun _ => u) (s₀,x) := by
  rw [passiveGroupedBackground_prescribed_iterate s₀ F hF g label c vf phase tau delta
    backgroundLength probeLength a target j u]
  exact passiveGroupedPrimary_wave s₀ F hF g label c vf phase tau delta
    backgroundLength probeLength a _ u b x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveGroupedBackground_prescribed_iterate
#print axioms GlobalEmbedding.Continuation.passiveGroupedBackground_amplitude
#print axioms GlobalEmbedding.Continuation.passiveGroupedBackground_primary
