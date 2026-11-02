import NormalPolar.PassiveParameterComplete
import NormalPolar.ActualProbeBackgroundDiagonal
import NormalPolar.JointSecondaryDiagonal

/-!
# The actual first map formed jointly on the physical parameter manifold

The global parameter is substituted before the background recurrence and
before the negative quadratic secondary forcing is formed.  Slice locality
of the actual spatial solver identifies that one global construction with
the fixed-external-parameter formula.  For passive primitive geometry the
latter is the one-point seed formula on the entire original parameter ball.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Λ Β SubSecondary : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))

variable (F : P → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I:=𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m:=m) (Λ:=Λ) (Β:=Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → P → (EuclideanSpace ℝ (Fin (m+1))) → M)
  (vf : (l : Fin r) → (b : P) → (x : (EuclideanSpace ℝ (Fin (m+1)))) → normalSpace (I:=𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength secondaryLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × (EuclideanSpace ℝ (Fin (m+1)))))
  (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)
  (choice : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Round3ParameterSecondaryChoice P M m)
  (hc : ∀ rec k, Round3ParameterChartPreserves (choice rec k).chart)

/-- One global actual background tensor, with the physical parameter already
inserted in the complete prescribed native mean. -/
def passiveFamilyJointBackground (u : P → Fin p → ℝ) :
    (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
  actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
    (fun (_ : Fin 0 → ℝ) b => actualParameterPrescribedNativeMean label F hF c vf phase
      tau probeLength a (u b) b) iteration 0

/-- The complete joint primary amplitudes using that one global tensor. -/
def passiveFamilyJointAmplitude (u : P → Fin p → ℝ) (imag : Bool) :
    (Λ ⊕ Fin r) → P × M → V :=
  fun l z => actualParameterProbeCombinedAmplitude F hF g label c vf tau delta
    backgroundLength probeLength a
    (passiveFamilyJointBackground F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u) (u z.1) imag l z

/-- Actual complete first increment, with all physical parameter dependence
inserted before the signed quadratic source is formed. -/
def passiveFamilyJointFirstIncrement (u : P → Fin p → ℝ) (z : P × M) : V :=
  actualParameterProbeCombinedPrimary F hF g label c vf phase tau delta
    backgroundLength probeLength a
    (passiveFamilyJointBackground F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u) (u z.1) z +
  actualParameterSecondarySourceSum F hF
    (fun rec k => actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
      (passiveFamilyJointAmplitude F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration u false)
      (passiveFamilyJointAmplitude F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration u true)
      tau rec.val (choice rec k) (hc rec k)) tau secondaryLength z

variable (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))

include hg

theorem passiveFamilyJointAmplitude_eq_diagonal
    (u : P → Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : P) (x : M) :
    passiveFamilyJointAmplitude F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u imag l (b,x) =
    actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration (u b) imag l (b,x) := by
  apply actualParameterProbeCombinedAmplitude_input_slice_congr F hF g label c vf tau delta
    backgroundLength probeLength a _ _ hg b _ (u b) imag l x
  funext y
  exact actual_parameter_background_diagonal_iterate F hF g backgroundLength tau delta target
    (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) u hg iteration b y

/-- Full equality of the one global construction with the actual fixed-u
slice; no secondary witness is chosen pointwise. -/
theorem passiveFamilyJointFirstIncrement_eq_fixed (u : P → Fin p → ℝ) (b : P) (x : M) :
    passiveFamilyJointFirstIncrement F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration choice hc u (b,x) =
    actualParameterCompleteFirstIncrementFromChoices F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration choice hc (u b) (b,x) := by
  have hA (imag : Bool) : passiveFamilyJointAmplitude F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u imag =
      fun l z => actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration (u z.1) imag l z := by
    funext l z
    exact passiveFamilyJointAmplitude_eq_diagonal F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration hg u imag l z.1 z.2
  unfold passiveFamilyJointFirstIncrement actualParameterCompleteFirstIncrementFromChoices
    actualParameterCompleteFirstIncrement
  apply congrArg₂ (fun v w : V => v+w)
  · apply actualParameterProbeCombinedPrimary_input_slice_congr F hF g label c vf phase tau delta
      backgroundLength probeLength a _ _ hg b _ (u b) x
    funext y
    exact actual_parameter_background_diagonal_iterate F hF g backgroundLength tau delta target
      (actualParameterPrescribedNativeMean label F hF c vf phase tau probeLength a) u hg iteration b y
  · rw [hA false,hA true]
    exact jointSecondary_diagonal_complete_sum F hF (Sum.elim g.phase phase)
      (fun v => actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration v false)
      (fun v => actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration v true)
      u tau choice hc tau secondaryLength b x

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveFamilyJointFirstIncrement
#print axioms GlobalEmbedding.Continuation.passiveFamilyJointFirstIncrement_eq_fixed
