import NormalPolar.ParameterDisplacementPrescribedParameterNaturality
import Probes.Round4ParameterProbeCombinedPrimary

/-!
# One physical common primary array through every genuine parameter chart

The labels remain `Λ ⊕ Fin r`, including the complete background and both
prescribed reconstruction channels. The native coefficient and selected mean
are obtained from the actual spatial derivatives of these same amplitudes.
The physical parameter space requires no linear structure.
-/

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

def actualParameterProbeCombinedAmplitude
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (imag : Bool) : (Λ ⊕ Fin r) → P × M → V :=
  Sum.elim
    (fun l z => delta • round3ParameterPrimaryAmplitude F hF g input backgroundLength tau (!imag) l z)
    (fun l => actualParameterPrescribedGlobalAmplitude imag label l F hF (c l) (vf l) tau probeLength (a l) u)

def actualParameterProbeCombinedPrimary
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (z : P × M) : V :=
  let phi := Sum.elim g.phase phase
  let R := actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
  let Q := actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
  ∑ l, (Real.cos (phi l z/tau) • R l z - Real.sin (phi l z/tau) • Q l z)

def actualParameterProbeCombinedMean
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (b : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  let phi := Sum.elim g.phase phase
  let R := actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
  let Q := actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
  (1/2 : ℝ) • ∑ l,
    (LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap)

theorem actualParameterProbeCombinedPrimary_eq
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Fin p → ℝ) (z : P × M) :
    actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u z =
      delta • round3ParameterPrimaryWave F hF g input backgroundLength tau z +
        actualParameterPrescribedGlobalWave label F hF c vf phase tau probeLength a u z := by
  simp only [actualParameterProbeCombinedPrimary,Fintype.sum_sum_type,
    actualParameterProbeCombinedAmplitude,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    round3ParameterPrimaryWave,actualParameterPrescribedGlobalWave,Finset.smul_sum,smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_comm (Real.cos _),smul_comm (Real.sin _)]

variable (B : OpenPartialHomeomorph P Q)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (ha : ∀ l, Round3ParameterChartPreserves (a l))
  (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

include hg ha

theorem actualParameterProbeCombinedAmplitude_pullback
    (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterProbeCombinedAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
      (fun l t => vf l (B.symm t)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => input (B.symm t)) u imag l (b,x) =
    actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u imag l (B.symm b,x) := by
  cases l with
  | inl l =>
    exact congrArg (fun v : V => delta • v)
      (round3ParameterPrimary_pullback_amplitude F hF g B hg input backgroundLength tau (!imag) l b hb x)
  | inr l =>
    exact actualParameterPrescribedGlobalAmplitude_pullback imag label l F hF (c l) (vf l)
      tau probeLength (a l) (ha l) B u b hb x

theorem actualParameterProbeCombinedPrimary_pullback
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterProbeCombinedPrimary (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
      (fun l t => vf l (B.symm t)) (fun l z => phase l (B.symm z.1,z.2))
      tau delta backgroundLength probeLength (fun l => round3ParameterChartPullback B (a l))
      (fun t => input (B.symm t)) u (b,x) =
    actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u (B.symm b,x) := by
  rw [actualParameterProbeCombinedPrimary_eq,actualParameterProbeCombinedPrimary_eq,
    round3ParameterPrimary_pullback_wave F hF g B hg input backgroundLength tau b hb,
    actualParameterPrescribedGlobalWave_pullback label F hF c vf phase tau probeLength a ha B u b hb]

theorem actualParameterProbeCombinedCoefficient_pullback
    (u : Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : Q) (hb : b ∈ B.target) (x : M) :
    round4PrescribedNativeCoefficient (I := I) imag
      (Sum.elim (round3ParameterPrimaryPullback F g B).phase
        (fun l z => phase l (B.symm z.1,z.2)) l) tau
      (actualParameterProbeCombinedAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
        (fun l t => vf l (B.symm t)) tau delta backgroundLength probeLength
        (fun l => round3ParameterChartPullback B (a l)) (fun t => input (B.symm t)) u false l)
      (actualParameterProbeCombinedAmplitude (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
        (fun l t => vf l (B.symm t)) tau delta backgroundLength probeLength
        (fun l => round3ParameterChartPullback B (a l)) (fun t => input (B.symm t)) u true l) (b,x) =
    round4PrescribedNativeCoefficient (I := I) imag (Sum.elim g.phase phase l) tau
      (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false l)
      (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true l)
      (B.symm b,x) := by
  have hR := funext (actualParameterProbeCombinedAmplitude_pullback F hF g label c vf tau delta
    backgroundLength probeLength a B hg ha input u false l b hb)
  have hQ := funext (actualParameterProbeCombinedAmplitude_pullback F hF g label c vf tau delta
    backgroundLength probeLength a B hg ha input u true l b hb)
  have hp : (fun y => Sum.elim (round3ParameterPrimaryPullback F g B).phase
      (fun l z => phase l (B.symm z.1,z.2)) l (b,y)) =
      fun y => Sum.elim g.phase phase l (B.symm b,y) := by cases l <;> rfl
  have hdR := congrArg (fun f : M → V => mvfderiv I f x) hR
  have hdQ := congrArg (fun f : M → V => mvfderiv I f x) hQ
  have hdp := congrArg (fun f : M → ℝ => mvfderiv I f x) hp
  have hfastR := congrArg₂
    (fun (deriv : TangentSpace I x →L[ℝ] ℝ) (value : V) => deriv.smulRight (tau⁻¹ • value))
    hdp (congrFun hR x)
  have hfastQ := congrArg₂
    (fun (deriv : TangentSpace I x →L[ℝ] ℝ) (value : V) => deriv.smulRight (tau⁻¹ • value))
    hdp (congrFun hQ x)
  cases imag
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f-g) hdR hfastQ
  · exact congrArg₂ (fun f g : TangentSpace I x →L[ℝ] V => f+g) hdQ hfastR

theorem actualParameterProbeCombinedMean_pullback
    (u : Fin p → ℝ) (b : Q) (hb : b ∈ B.target) (x : M) :
    actualParameterProbeCombinedMean (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) label (fun l t => c l (B.symm t))
      (fun l t => vf l (B.symm t)) (fun l z => phase l (B.symm z.1,z.2))
      tau delta backgroundLength probeLength (fun l => round3ParameterChartPullback B (a l))
      (fun t => input (B.symm t)) u b x =
    actualParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength probeLength a input u (B.symm b) x := by
  simp only [actualParameterProbeCombinedMean,
    actualParameterProbeCombinedCoefficient_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a B hg ha input u false _ b hb,
    actualParameterProbeCombinedCoefficient_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a B hg ha input u true _ b hb]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedAmplitude_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedPrimary_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedCoefficient_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeCombinedMean_pullback
