import NormalPolar.ParameterDisplacementPrescribedParameterNaturality

/-! The original prescribed opposite mean on a physical parameter space,
with its complete reconstructed amplitudes and true native derivatives.
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
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

variable
  (label : (Fin r × Bool) ↪ Fin p)
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (c : Fin r → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := I) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau : ℝ) (length : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))

def actualParameterPrescribedNativeMean (u : Fin p → ℝ) :
    (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x) :=
  round4NativeOppositeMean (I := I) phase tau
    (fun l => actualParameterPrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u)
    (fun l => actualParameterPrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u)

theorem actualParameterPrescribedNativeMean_isSymm (u : Fin p → ℝ) (b : P) (x : M) :
    (actualParameterPrescribedNativeMean label F hF c vf phase tau length a u b x).IsSymm :=
  round4NativeOppositeMean_isSymm phase tau _ _ b x

variable (ha : ∀ l, Round3ParameterChartPreserves (a l)) (B : OpenPartialHomeomorph P Q)
include ha

theorem actualParameterPrescribedCoefficient_pullback
    (u : Fin p → ℝ) (imag : Bool) (l : Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag (fun z => phase l (B.symm z.1,z.2)) tau
      (actualParameterPrescribedGlobalAmplitude false label l
        (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (fun t => c l (B.symm t)) (fun t => vf l (B.symm t)) tau length
        (round3ParameterChartPullback B (a l)) u)
      (actualParameterPrescribedGlobalAmplitude true label l
        (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (fun t => c l (B.symm t)) (fun t => vf l (B.symm t)) tau length
        (round3ParameterChartPullback B (a l)) u) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag (phase l) tau
      (actualParameterPrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u)
      (actualParameterPrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u) (B.symm b,x) := by
  have hR := funext (actualParameterPrescribedGlobalAmplitude_pullback false label l F hF
    (c l) (vf l) tau length (a l) (ha l) B u b hb)
  have hQ := funext (actualParameterPrescribedGlobalAmplitude_pullback true label l F hF
    (c l) (vf l) tau length (a l) (ha l) B u b hb)
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

theorem actualParameterPrescribedNativeMean_pullback
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterPrescribedNativeMean label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau length
      (fun l => round3ParameterChartPullback B (a l)) u b x =
    actualParameterPrescribedNativeMean label F hF c vf phase tau length a u (B.symm b) x := by
  simp only [actualParameterPrescribedNativeMean,round4NativeOppositeMean,
    actualParameterPrescribedCoefficient_pullback label F hF c vf phase tau length a ha B u false _ b hb,
    actualParameterPrescribedCoefficient_pullback label F hF c vf phase tau length a ha B u true _ b hb]

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

omit ha in
theorem actualParameterPrescribedNativeMean_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D)) :
    actualParameterPrescribedNativeMean label F hF c vf phase tau length a =
      round4PrescribedNativeMean label F hF c vf phase tau length a := rfl

theorem actualParameterPrescribedNativeMean_native_pullback
    (B : OpenPartialHomeomorph P Ep) (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    round4PrescribedNativeMean label
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau length
      (fun l => round3ParameterChartPullback B (a l)) u b x =
    actualParameterPrescribedNativeMean label F hF c vf phase tau length a u (B.symm b) x :=
  actualParameterPrescribedNativeMean_pullback label F hF c vf phase tau length a ha B u b hb x

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterPrescribedNativeMean_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterPrescribedNativeMean_native_pullback
