import Smoothing.Round3OuterPositiveFiber
import Smoothing.ParameterRound2OriginalReserveC0

/-! A genuine positive decomposition neighborhood for a computed repair target.
The neighborhood is constructed from the unchanged linear functionals and
actual relative supports. The square-root reconstruction identity is derived
from the old open decomposition, by its already proved linear extension.
No membership of the computed target in an arbitrary old neighborhood is
assumed. Original data definitions and the original decomposition are unchanged.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace P]
local notation "Dsource" => EuclideanSpace ℝ (Fin n)
local notation "IT" => 𝓘(ℝ,Dsource)

def round3OriginalRetargetPositiveConeData
    (D : IncrementsOriginalNativeData n d N M P)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (reserve : ℝ) : IncrementsOriginalNativeData n d N M P :=
  { D with H := T, tensorNeighborhood := round3OriginalPositiveCone D reserve }

/-- The actual positive cone supplies every qualitative decomposition field
and a fixed reserve for the same cutoff/phase/linear-functional packet. -/
theorem round3_original_retarget_positive_cone
    (D : IncrementsOriginalNativeData n d N M P)
    (hD : IncrementsOriginalQualitativeDecompositionInputs D)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (hT : ∀ p ∈ D.parameterOpen, ∀ x, (T p x).IsSymm)
    (reserve : ℝ) (hr : 0 < reserve)
    (hTpos : ∀ ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      reserve < D.linearArgument ν z.1 z.2 (T z.1 z.2))
    (hRpos : ∀ ν z, z ∈ incrementsOriginalRelativeCutoffSupport D ν →
      reserve < D.linearArgument ν z.1 z.2 (D.reference z.1 z.2)) :
    IncrementsOriginalQualitativeDecompositionInputs
      (round3OriginalRetargetPositiveConeData D T reserve) ∧
    IncrementsOriginalDecompositionReserveInputs
      (round3OriginalRetargetPositiveConeData D T reserve) reserve := by
  constructor
  · refine { fiber_open := fun p _ x => round3_original_positive_cone_open D reserve p x
             H_symmetric := hT
             reference_symmetric := hD.reference_symmetric
             H_mem := ?_
             reference_mem := ?_
             decomposition := ?_
             argument_positive := ?_ }
    · intro p hp x ν hν
      exact hTpos ν (p,x) hν
    · intro p hp x ν hν
      exact hRpos ν (p,x) hν
    · intro p hp x A hA
      apply (incrementsOriginal_decomposition_extension D hD p hp x).2 A
      intro ν hν
      have hrel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν :=
        ⟨⟨(p,x),hp,Set.mem_univ _⟩,subset_tsupport _ hν,rfl⟩
      exact (hr.trans (hA ν hrel)).le
    · intro p hp x ν hν A hA
      have hrel : (p,x) ∈ incrementsOriginalRelativeCutoffSupport D ν :=
        ⟨⟨(p,x),hp,Set.mem_univ _⟩,subset_tsupport _ hν,rfl⟩
      exact hr.trans (hA ν hrel)
  · refine ⟨hr,?_⟩
    intro ν z hz hp A hA
    exact (hA ν hz).le

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- Over a global parameter evaluation set, original C0 control produces the
computed target's cone membership and a uniform reserve. In repair, T is
literally SH-(deltaNext/delta)^2 gamma(F0). No target-cone premise remains. -/
theorem round3_original_retarget_positive_cone_of_C0
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D)
    (hD : IncrementsOriginalQualitativeDecompositionInputs D)
    (hK : D.parameterSet = univ)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs D rho)
    (T : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
    (hT : ∀ p ∈ D.parameterOpen, ∀ x, (T p x).IsSymm)
    (ell ML R : ℝ)
    (hProfile : incrementsOriginalInputProfileWithLinear D 0 ell ≠ ⊤)
    (hML : (incrementsOriginalInputProfileWithLinear D 0 ell).toReal ≤ ML)
    (hFinite : paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => T p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤)
    (hR : (paperAtlasCj 0
      (incrementsOriginalTensorCoordinates D.atlas D.parameterChart (fun p x => T p x-D.H p x))
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet)).toReal ≤ R)
    (hSmall : ‖actualOriginalCoefficientFunctional n‖ * ML * R ≤ rho/2) :
    IncrementsOriginalQualitativeDecompositionInputs
      (round3OriginalRetargetPositiveConeData D T (rho/4)) ∧
    IncrementsOriginalDecompositionReserveInputs
      (round3OriginalRetargetPositiveConeData D T (rho/4)) (rho/4) := by
  have hSample := parameterRound2_original_reserve_of_C0
    D hd hD rho hReserve T hT ell ML R hProfile hML hFinite hR hSmall
  apply round3_original_retarget_positive_cone D hD T hT (rho/4) (by linarith [hReserve.reserve_pos])
  · intro ν z hz
    have hp : z.1 ∈ D.parameterSet := by rw [hK]; exact mem_univ _
    exact lt_of_lt_of_le (by linarith [hReserve.reserve_pos]) (hSample ν z hz hp)
  · intro ν z hz
    have hp : z.1 ∈ D.parameterSet := by rw [hK]; exact mem_univ _
    have hR := hReserve.lower ν z hz hp _
      (hD.reference_mem z.1 (hd.parameter_subset hp) z.2)
    exact lt_of_lt_of_le (by linarith [hReserve.reserve_pos]) hR

#print axioms round3_original_retarget_positive_cone
#print axioms round3_original_retarget_positive_cone_of_C0
end GlobalEmbedding.Continuation
