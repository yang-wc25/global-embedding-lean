import NormalPolar.PassiveParameterPrimary
import NormalPolar.PassiveParameterPrescribed
import NormalPolar.ParameterDisplacementIteratedAmplitudeNaturality

/-! Passive-parameter identities for the same actual finite background
recurrence and the complete primary.  The recurrence is proved to commute
with the lift by induction, using the actual native mean from the solver. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M S P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable (s₀ : S) (F : S → M → (EuclideanSpace ℝ (Fin N)))
  (hF : ∀ s, ContMDiff I 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F s))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (length : ℕ) (tau delta : ℝ)
  (target : (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

theorem passiveParameterBackground_iterate
    (probe : (Fin p → ℝ) → (s : S) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (j : ℕ) (u : Fin p → ℝ) :
    actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
      (fun v _ => probe v s₀) j u =
    fun _ : P => actualParameterBackgroundMeanIterate F hF g length tau delta target probe j u s₀ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext b x
    change target s₀ x - (delta^2)⁻¹ • probe u s₀ x -
      round3ParameterPrimaryMeanError (fun _ : P => F s₀) (fun _ => hF s₀)
        (passiveParameterPrimary s₀ F g)
        (actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
          (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
          (fun v _ => probe v s₀) j u) length tau b x =
      target s₀ x - (delta^2)⁻¹ • probe u s₀ x -
        round3ParameterPrimaryMeanError F hF g
          (actualParameterBackgroundMeanIterate F hF g length tau delta target probe j u) length tau s₀ x
    rw [ih, passiveParameterPrimary_meanError s₀ F hF g]

variable (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → S → (EuclideanSpace ℝ (Fin (m+1))) → M)
  (vf : (l : Fin r) → (s : S) → (x : (EuclideanSpace ℝ (Fin (m+1)))) → normalSpace (I := I) (F s) (c l s x))
  (phase : Fin r → S × M → ℝ) (probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (S × M) (S × (EuclideanSpace ℝ (Fin (m+1)))))

theorem passiveParameterBackground_prescribed_iterate (j : ℕ) (u : Fin p → ℝ) :
    actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
      (actualParameterPrescribedNativeMean label
        (fun _ : P => F s₀) (fun _ => hF s₀)
        (fun l _ => c l s₀) (fun l _ => vf l s₀)
        (fun l z => phase l (s₀,z.2)) tau probeLength
        (fun l => passiveParameterChart s₀ (a l))) j u =
    fun _ : P => actualParameterBackgroundMeanIterate F hF g length tau delta target
      (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) j u s₀ := by
  have hp : actualParameterPrescribedNativeMean label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau probeLength
      (fun l => passiveParameterChart s₀ (a l)) =
      fun v (_ : P) => actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a v s₀ := by
    funext v b x
    exact passiveParameterPrescribed_mean s₀ label F hF c vf phase tau probeLength a v b x
  rw [hp]
  exact passiveParameterBackground_iterate s₀ F hF g length tau delta target _ j u

/-- The background term is the actual complete primary solver at the same
iterate on both sides, with the same finite reconstruction length. -/
theorem passiveParameterBackground_prescribed_wave (j : ℕ) (u : Fin p → ℝ) (b : P) (x : M) :
    round3ParameterPrimaryWave (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g)
      (actualParameterBackgroundMeanIterate (fun _ : P => F s₀) (fun _ => hF s₀)
        (passiveParameterPrimary s₀ F g) length tau delta (fun _ => target s₀)
        (actualParameterPrescribedNativeMean label
          (fun _ : P => F s₀) (fun _ => hF s₀)
          (fun l _ => c l s₀) (fun l _ => vf l s₀)
          (fun l z => phase l (s₀,z.2)) tau probeLength
          (fun l => passiveParameterChart s₀ (a l))) j u) length tau (b,x) =
    round3ParameterPrimaryWave F hF g
      (actualParameterBackgroundMeanIterate F hF g length tau delta target
        (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) j u)
      length tau (s₀,x) := by
  rw [passiveParameterBackground_prescribed_iterate s₀ F hF g length tau delta target
    label c vf phase probeLength a j u]
  exact passiveParameterPrimary_wave s₀ F hF g _ length tau b x

/-- Every original label and both complete reconstruction channels are
preserved, before the quadratic mixed forcing is assembled. -/
theorem passiveParameterBackground_complete_amplitude
    (j : ℕ) (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : P) (x : M) :
    actualParameterProbeIteratedAmplitude (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau delta length probeLength
      (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) j u imag l (b,x) =
    actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta
      length probeLength a target j u imag l (s₀,x) := by
  unfold actualParameterProbeIteratedAmplitude
  rw [passiveParameterBackground_prescribed_iterate s₀ F hF g length tau delta target
    label c vf phase probeLength a j u]
  cases l with
  | inl l =>
    exact congrArg (fun v : V => delta • v)
      (passiveParameterPrimary_amplitude s₀ F hF g _ length tau (!imag) l b x)
  | inr l =>
    exact passiveParameterPrescribed_amplitude s₀ label F hF c vf tau probeLength a imag l u b x

/-- Full common primary, including every prescribed channel, at the same
literal finite background iterate.  It is independent of the passive point
for every external probe parameter, not merely at the centre. -/
theorem passiveParameterBackground_complete_primary (j : ℕ) (u : Fin p → ℝ) (b : P) (x : M) :
    actualParameterProbeIteratedPrimary (fun _ : P => F s₀) (fun _ => hF s₀)
      (passiveParameterPrimary s₀ F g) label
      (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau delta length probeLength
      (fun l => passiveParameterChart s₀ (a l)) (fun _ => target s₀) j u (b,x) =
    actualParameterProbeIteratedPrimary F hF g label c vf phase tau delta length probeLength a target j u (s₀,x) := by
  unfold actualParameterProbeIteratedPrimary
  rw [actualParameterProbeCombinedPrimary_eq, actualParameterProbeCombinedPrimary_eq]
  rw [passiveParameterBackground_prescribed_wave s₀ F hF g length tau delta target
    label c vf phase probeLength a j u b x,
    passiveParameterPrescribed_wave s₀ label F hF c vf phase tau probeLength a u b x]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterBackground_iterate
#print axioms GlobalEmbedding.Continuation.passiveParameterBackground_complete_amplitude
#print axioms GlobalEmbedding.Continuation.passiveParameterBackground_complete_primary
