import NormalPolar.PassiveGroupedLocality
import NormalPolar.ActualProbeBackgroundDiagonal

/-! One actual grouped family on the whole physical parameter space.
The parameter field is substituted before the true prescribed mean and
background recurrence. Spatial slice locality identifies the resulting
complete primary with the fixed external parameter formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : (l : Fin r) → Pieces l → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (k : Pieces l) → (b : P) →
    (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l k b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength : ℕ)
  (a : (l : Fin r) → Pieces l →
    OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (target : (b : P) → (x : M) →
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

/-- The parameter is inserted in the actual complete grouped mean before
the background recurrence, as in the genuine q = 440 producer. -/
def passiveGroupedFamilyJointBackground (u : P → Fin p → ℝ) :
    (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x) :=
  actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
    (fun (_ : Fin 0 → ℝ) b => jointGroupedParameterPrescribedMean label F hF c vf
      phase tau probeLength a (u b) b) iteration 0

variable (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
include hg

theorem passiveGroupedFamilyJointBackground_eq_fixed
    (u : P → Fin p → ℝ) (b : P) (x : M) :
    passiveGroupedFamilyJointBackground F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u b x =
    actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
      (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a)
      iteration (u b) b x :=
  actual_parameter_background_diagonal_iterate F hF g backgroundLength tau delta target
    (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a)
    u hg iteration b x

theorem passiveGroupedFamilyJointAmplitude_eq_fixed
    (u : P → Fin p → ℝ) (imag : Bool) (l : Λ ⊕ Fin r) (b : P) (x : M) :
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a
      (passiveGroupedFamilyJointBackground F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration u) u imag l (b,x) =
    actualProbeInitialGroupedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a
      (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
        (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a)
        iteration (u b)) (fun _ => u b) imag l (b,x) := by
  apply passiveGrouped_amplitude_slice_congr F hF g label c vf tau delta
    backgroundLength probeLength a _ _ hg u (fun _ => u b) b _ rfl imag l x
  funext y
  exact passiveGroupedFamilyJointBackground_eq_fixed F hF g label c vf phase tau delta
    backgroundLength probeLength a target iteration hg u b y

theorem passiveGroupedFamilyJointPrimary_eq_fixed
    (u : P → Fin p → ℝ) (b : P) (x : M) :
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a
      (passiveGroupedFamilyJointBackground F hF g label c vf phase tau delta
        backgroundLength probeLength a target iteration u) u (b,x) =
    actualProbeInitialGroupedPrimary F hF g label c vf phase tau delta
      backgroundLength probeLength a
      (actualParameterBackgroundMeanIterate F hF g backgroundLength tau delta target
        (jointGroupedParameterPrescribedMean label F hF c vf phase tau probeLength a)
        iteration (u b)) (fun _ => u b) (b,x) := by
  apply passiveGrouped_primary_slice_congr F hF g label c vf phase tau delta
    backgroundLength probeLength a _ _ hg u (fun _ => u b) b _ rfl x
  funext y
  exact passiveGroupedFamilyJointBackground_eq_fixed F hF g label c vf phase tau delta
    backgroundLength probeLength a target iteration hg u b y

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveGroupedFamilyJointBackground
#print axioms GlobalEmbedding.Continuation.passiveGroupedFamilyJointBackground_eq_fixed
#print axioms GlobalEmbedding.Continuation.passiveGroupedFamilyJointAmplitude_eq_fixed
#print axioms GlobalEmbedding.Continuation.passiveGroupedFamilyJointPrimary_eq_fixed
