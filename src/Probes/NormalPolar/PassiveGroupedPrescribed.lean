import NormalPolar.PassiveParameterPrescribed
import NormalPolar.JointSecondaryGroupedParameter

/-! Passive parameter identities for the actual complete prescribed array.
Every original label keeps its dependent family of subordinate pieces. The
pieces are summed before the spatial derivative and the opposite quadratic
mean, so the identities include the cross terms between distinct pieces. -/

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
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable (s₀ : S) (label : (Fin r × Bool) ↪ Fin p)
  (F : S → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ s, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F s))
  (c : (l : Fin r) → Sub l → S → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (k : Sub l) → (s : S) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F s) (c l k s x))
  (phase : Fin r → S × M → ℝ) (tau : ℝ) (length : ℕ)
  (a : (l : Fin r) → Sub l →
    OpenPartialHomeomorph (S × M) (S × EuclideanSpace ℝ (Fin (m+1))))

theorem passiveGroupedPrescribed_amplitude
    (imag : Bool) (l : Fin r) (u : Fin p → ℝ) (b : P) (x : M) :
    jointGroupedParameterPrescribedAmplitude label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau length
      (fun l k => passiveParameterChart s₀ (a l k)) imag u l (b,x) =
    jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a imag u l (s₀,x) := by
  unfold jointGroupedParameterPrescribedAmplitude
  apply Finset.sum_congr rfl
  intro k _
  exact passiveParameterPrescribed_amplitude s₀ label F hF
    (fun _ => c l k) (fun _ => vf l k) tau length (fun _ => a l k) imag l u b x

theorem passiveGroupedPrescribed_coefficient
    (u : Fin p → ℝ) (imag : Bool) (l : Fin r) (b : P) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag (fun z => phase l (s₀,z.2)) tau
      (jointGroupedParameterPrescribedAmplitude label
        (fun _ : P => F s₀) (fun _ => hF s₀)
        (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau length
        (fun l k => passiveParameterChart s₀ (a l k)) false u l)
      (jointGroupedParameterPrescribedAmplitude label
        (fun _ : P => F s₀) (fun _ => hF s₀)
        (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau length
        (fun l k => passiveParameterChart s₀ (a l k)) true u l) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag (phase l) tau
      (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a false u l)
      (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a true u l) (s₀,x) := by
  have hR := funext (passiveGroupedPrescribed_amplitude s₀ label F hF c vf tau length a false l u b)
  have hQ := funext (passiveGroupedPrescribed_amplitude s₀ label F hF c vf tau length a true l u b)
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

theorem passiveGroupedPrescribed_mean
    (u : Fin p → ℝ) (b : P) (x : M) :
    jointGroupedParameterPrescribedMean label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀)
      (fun l z => phase l (s₀,z.2)) tau length
      (fun l k => passiveParameterChart s₀ (a l k)) u b x =
    jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u s₀ x := by
  simp only [jointGroupedParameterPrescribedMean, round4NativeOppositeMean,
    passiveGroupedPrescribed_coefficient s₀ label F hF c vf phase tau length a u false,
    passiveGroupedPrescribed_coefficient s₀ label F hF c vf phase tau length a u true]

/-- This is an identity of one whole spatial slice after the global probe
field has been inserted, not a choice of a reconstruction for each value. -/
theorem passiveGroupedPrescribed_joint_amplitude_slice
    (u : P → Fin p → ℝ) (imag : Bool) (l : Fin r) (b : P) :
    (fun x => jointGroupedParameterPrescribedAmplitude label
      (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun l k _ => c l k s₀) (fun l k _ => vf l k s₀) tau length
      (fun l k => passiveParameterChart s₀ (a l k)) imag (u (b,x).1) l (b,x)) =
    (fun x => jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a
      imag (u b) l (s₀,x)) := by
  funext x
  exact passiveGroupedPrescribed_amplitude s₀ label F hF c vf tau length a imag l (u b) b x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveGroupedPrescribed_amplitude
#print axioms GlobalEmbedding.Continuation.passiveGroupedPrescribed_coefficient
#print axioms GlobalEmbedding.Continuation.passiveGroupedPrescribed_mean
#print axioms GlobalEmbedding.Continuation.passiveGroupedPrescribed_joint_amplitude_slice
