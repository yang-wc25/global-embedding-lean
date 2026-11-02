import NormalPolar.JointSecondaryGroupedParameter
import NormalPolar.JointMixedGroupedPrimary
import NormalPolar.ParameterDisplacementCombinedParameterNaturality
import Probes.Round3ParameterNativeFamily

/-! The physical grouped first array on the original parameter manifold.
The labels remain exactly Λ ⊕ Fin r. Each original prescribed label first
sums its actual subordinate pieces, and the whole parameter field is inserted
before the physical wave or quadratic secondary forcing is formed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {M P Ep Λ Β : Type*}
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β] {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
variable
    (F : P → M → EuclideanSpace ℝ (Fin N))
    (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → EuclideanSpace ℝ (Fin (m+1)) → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
      normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
    (u : P → Fin p → ℝ)

def actualProbeInitialGroupedAmplitude (imag : Bool) : (Λ ⊕ Fin r) → P × M → V :=
  Sum.elim
    (fun (l : Λ) (z : P × M) => delta • round3ParameterPrimaryAmplitude (I := IM) (Λ := Λ) (Β := Β) F hF g input backgroundLength tau (!imag) l z)
    (fun (l : Fin r) (z : P × M) => jointGroupedParameterPrescribedAmplitude (Sub := Pieces) label F hF c vf tau probeLength a
      imag (u z.1) l z)

def actualProbeInitialGroupedPrimary (z : P × M) : V :=
  ∑ l, (Real.cos (Sum.elim g.phase phase l z/tau) •
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false l z -
    Real.sin (Sum.elim g.phase phase l z/tau) •
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true l z)

def actualProbeInitialGroupedMean (b : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace IM x) :=
  let phi := Sum.elim g.phase phase
  let R := actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
  let Q := actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
  (1/2 : ℝ) • ∑ l,
    (LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := IM) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := IM) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := IM) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := IM) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap)


variable (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ (l : Λ) (k : Β), Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ (l : Fin r) (s : Pieces l), Round3ParameterChartPreserves (a l s))
include hg ha

theorem actualProbeInitialSupply_grouped_amplitude_pullback
    (imag : Bool) (l : Λ ⊕ Fin r) (b : Ep) (hb : b ∈ B.target) (x : M) :
    jointGroupedCombinedAmplitude
      (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      ((round3ParameterPrimaryPullback F g B).toNative (fun t => F (B.symm t))) label
      (fun l s t => c l s (B.symm t)) (fun l s t => vf l s (B.symm t))
      tau delta backgroundLength probeLength
      (fun l s => round3ParameterChartPullback B (a l s))
      (fun t => input (B.symm t)) (fun t => u (B.symm t)) imag l (b,x) =
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta backgroundLength probeLength
      a input u imag l (B.symm b,x) := by
  cases l with
  | inl l =>
    exact congrArg (fun v : V => delta • v)
      (round3ParameterPrimary_pullback_amplitude F hF g B hg input backgroundLength tau
        (!imag) l b hb x)
  | inr l =>
    exact jointGroupedParameterPrescribedAmplitude_pullback label F hF c vf tau probeLength
      a ha B (u (B.symm b)) imag l b hb x


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_amplitude_pullback
