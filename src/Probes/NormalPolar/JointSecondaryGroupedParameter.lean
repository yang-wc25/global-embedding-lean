import NormalPolar.ParameterDisplacementPrescribedParameterNaturality
import NormalPolar.JointSecondaryGroupedAmplitude

/-! The original-label grouped prescribed opposite mean on a physical parameter space,
with every complete subordinate reconstruction summed before the true native derivative. Both cross-piece quadratic terms and the original label embedding are retained.
This is the forcing used in the actual background iteration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N p r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable
  (label : (Fin r × Bool) ↪ Fin p)
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (c : (l : Fin r) → Sub l → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (s : Sub l) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F b) (c l s b x))
  (phase : Fin r → P × M → ℝ) (tau : ℝ) (length : ℕ)
  (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))

def jointGroupedParameterPrescribedAmplitude (imag : Bool) (u : Fin p → ℝ)
    (l : Fin r) (z : P × M) : V :=
  ∑ s, actualParameterPrescribedGlobalAmplitude imag label l F hF (c l s) (vf l s)
    tau length (a l s) u z

def jointGroupedParameterPrescribedMean (u : Fin p → ℝ) :
    (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x) :=
  round4NativeOppositeMean (I := I) phase tau
    (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a false u)
    (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a true u)

theorem jointGroupedParameterPrescribedMean_isSymm (u : Fin p → ℝ) (b : P) (x : M) :
    (jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u b x).IsSymm :=
  round4NativeOppositeMean_isSymm phase tau _ _ b x

variable (ha : ∀ l s, Round3ParameterChartPreserves (a l s)) (B : OpenPartialHomeomorph P Q)
include ha

theorem jointGroupedParameterPrescribedAmplitude_pullback
    (u : Fin p → ℝ) (imag : Bool) (l : Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    jointGroupedParameterPrescribedAmplitude label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t)) tau length
      (fun l s => round3ParameterChartPullback B (a l s)) imag u l (b,x) =
    jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a imag u l (B.symm b,x) := by
  unfold jointGroupedParameterPrescribedAmplitude
  exact Finset.sum_congr rfl (fun s _ => actualParameterPrescribedGlobalAmplitude_pullback
    imag label l F hF (c l s) (vf l s) tau length (a l s) (ha l s) B u b hb x)

theorem jointGroupedParameterPrescribedCoefficient_pullback
    (u : Fin p → ℝ) (imag : Bool) (l : Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag (fun z => phase l (B.symm z.1,z.2)) tau
      (jointGroupedParameterPrescribedAmplitude label
        (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t)) tau length
        (fun l s => round3ParameterChartPullback B (a l s)) false u l)
      (jointGroupedParameterPrescribedAmplitude label
        (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t)) tau length
        (fun l s => round3ParameterChartPullback B (a l s)) true u l) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag (phase l) tau
      (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a false u l)
      (jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a true u l) (B.symm b,x) := by
  have hR := funext (jointGroupedParameterPrescribedAmplitude_pullback label F hF c vf
    tau length a ha B u false l b hb)
  have hQ := funext (jointGroupedParameterPrescribedAmplitude_pullback label F hF c vf
    tau length a ha B u true l b hb)
  have hdR := congrArg (fun f : M → V => mvfderiv I f x) hR
  have hdQ := congrArg (fun f : M → V => mvfderiv I f x) hQ
  have hfastR := congrArg
    (fun value : V => (incrementsGlobalScalarDerivative (I := I) (phase l) (B.symm b,x)).smulRight (tau⁻¹ • value))
    (congrFun hR x)
  have hfastQ := congrArg
    (fun value : V => (incrementsGlobalScalarDerivative (I := I) (phase l) (B.symm b,x)).smulRight (tau⁻¹ • value))
    (congrFun hQ x)
  cases imag
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f-g) hdR hfastQ
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f+g) hdQ hfastR

theorem jointGroupedParameterPrescribedMean_pullback
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    jointGroupedParameterPrescribedMean label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau length
      (fun l s => round3ParameterChartPullback B (a l s)) u b x =
    jointGroupedParameterPrescribedMean label F hF c vf phase tau length a u (B.symm b) x := by
  simp only [jointGroupedParameterPrescribedMean,round4NativeOppositeMean,
    jointGroupedParameterPrescribedCoefficient_pullback label F hF c vf phase tau length a ha B u false _ b hb,
    jointGroupedParameterPrescribedCoefficient_pullback label F hF c vf phase tau length a ha B u true _ b hb]

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

omit ha in
theorem jointGroupedParameterPrescribedAmplitude_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : (l : Fin r) → Sub l → Ep → D → M)
    (vf : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (imag : Bool) (u : Fin p → ℝ) :
    jointGroupedParameterPrescribedAmplitude label F hF c vf tau length a imag u =
      jointGroupedPrescribedAmplitude imag label F hF c vf tau length a u := rfl

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointGroupedParameterPrescribedAmplitude_pullback
#print axioms GlobalEmbedding.Continuation.jointGroupedParameterPrescribedCoefficient_pullback
#print axioms GlobalEmbedding.Continuation.jointGroupedParameterPrescribedMean_pullback
#print axioms GlobalEmbedding.Continuation.jointGroupedParameterPrescribedAmplitude_native
