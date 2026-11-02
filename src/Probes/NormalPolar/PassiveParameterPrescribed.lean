import NormalPolar.PassiveParameterChart
import NormalPolar.ParameterDisplacementPrescribedMeanNaturality

/-! The entire prescribed wave and its native opposite mean for the actual
passive lift.  The finite solver and its original free normal data are kept
literally; no output response or family identity is supplied as a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M S P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace S] [Subsingleton S]
  [TopologicalSpace P] {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable (s₀ : S) (label : (Fin r × Bool) ↪ Fin p)
  (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (c : Fin r → S → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (s : S) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F s) (c l s x))
  (phase : Fin r → S × M → ℝ) (tau : ℝ) (length : ℕ)
  (a : Fin r → OpenPartialHomeomorph (S × M) (S × EuclideanSpace ℝ (Fin (m+1))))

theorem passiveParameterPrescribed_amplitude
    (imag : Bool) (l : Fin r) (u : Fin p → ℝ) (b : P) (x : M) :
    actualParameterPrescribedGlobalAmplitude imag label l
      (fun _ : P => F s₀) (fun _ => hF s₀) (fun _ => c l s₀) (fun _ => vf l s₀)
      tau length (passiveParameterChart s₀ (a l)) u (b,x) =
    actualParameterPrescribedGlobalAmplitude imag label l F hF (c l) (vf l)
      tau length (a l) u (s₀,x) := by
  classical
  have hp : (a l (s₀,x)).1 = s₀ := Subsingleton.elim _ _
  simp only [actualParameterPrescribedGlobalAmplitude,
    passiveParameterChart_source, passiveParameterChart_apply]
  split_ifs with hx
  · exact congrArg (fun s : S => round4PrescribedAmplitude imag label l (F s) (hF s)
      (c l s) (vf l s) tau length u (a l (s₀,x)).2) hp.symm
  · rfl

theorem passiveParameterPrescribed_wave
    (u : Fin p → ℝ) (b : P) (x : M) :
    actualParameterPrescribedGlobalWave label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau length
      (fun l => passiveParameterChart s₀ (a l)) u (b,x) =
    actualParameterPrescribedGlobalWave label F hF c vf phase tau length a u (s₀,x) := by
  unfold actualParameterPrescribedGlobalWave
  apply Finset.sum_congr rfl
  intro l _
  rw [passiveParameterPrescribed_amplitude s₀ label F hF c vf tau length a false l u b x,
    passiveParameterPrescribed_amplitude s₀ label F hF c vf tau length a true l u b x]

theorem passiveParameterPrescribed_coefficient
    (u : Fin p → ℝ) (imag : Bool) (l : Fin r) (b : P) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag (fun z => phase l (s₀,z.2)) tau
      (actualParameterPrescribedGlobalAmplitude false label l
        (fun _ : P => F s₀) (fun _ => hF s₀) (fun _ => c l s₀) (fun _ => vf l s₀)
        tau length (passiveParameterChart s₀ (a l)) u)
      (actualParameterPrescribedGlobalAmplitude true label l
        (fun _ : P => F s₀) (fun _ => hF s₀) (fun _ => c l s₀) (fun _ => vf l s₀)
        tau length (passiveParameterChart s₀ (a l)) u) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag (phase l) tau
      (actualParameterPrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u)
      (actualParameterPrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u)
      (s₀,x) := by
  have hR := funext (passiveParameterPrescribed_amplitude s₀ label F hF c vf tau length a false l u b)
  have hQ := funext (passiveParameterPrescribed_amplitude s₀ label F hF c vf tau length a true l u b)
  have hdR := congrArg (fun f : M → V => mvfderiv I f x) hR
  have hdQ := congrArg (fun f : M → V => mvfderiv I f x) hQ
  have hfR := congrArg
    (fun value : V => (incrementsGlobalScalarDerivative (I := I) (phase l) (s₀,x)).smulRight
      (tau⁻¹ • value)) (congrFun hR x)
  have hfQ := congrArg
    (fun value : V => (incrementsGlobalScalarDerivative (I := I) (phase l) (s₀,x)).smulRight
      (tau⁻¹ • value)) (congrFun hQ x)
  cases imag
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f-g) hdR hfQ
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f+g) hdQ hfR

theorem passiveParameterPrescribed_mean
    (u : Fin p → ℝ) (b : P) (x : M) :
    actualParameterPrescribedNativeMean label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l _ => c l s₀) (fun l _ => vf l s₀)
      (fun l z => phase l (s₀,z.2)) tau length
      (fun l => passiveParameterChart s₀ (a l)) u b x =
    actualParameterPrescribedNativeMean label F hF c vf phase tau length a u s₀ x := by
  simp only [actualParameterPrescribedNativeMean, round4NativeOppositeMean,
    passiveParameterPrescribed_coefficient s₀ label F hF c vf phase tau length a u false,
    passiveParameterPrescribed_coefficient s₀ label F hF c vf phase tau length a u true]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterPrescribed_wave
#print axioms GlobalEmbedding.Continuation.passiveParameterPrescribed_mean
