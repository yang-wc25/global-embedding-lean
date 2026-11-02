import OriginalIntegration.FinitePositiveIncrementsStatement
import GlobalEmbedding.Paper.IncrementsOriginalLinearArgumentCoordinates

/-!
# Original finite input prefix and literal increment entrance

This statement layer depends only on original native-data, coordinate and
norm definitions. It imports no solver, actual constructed packet, output
predicate, mean estimate or implementation threshold. The phase and chart
transition derivatives below are literal coordinate views of the given
functions. All norm bounds are extended-real inequalities against finite
real bounds; infinity cannot satisfy them through `toReal`.

The entrance predicate is about a displayed real threshold, not an
existential function of a budget. Its companion proof identifies that
threshold with the explicit finite numerical construction and proves its
actual prefix invariance.
-/

noncomputable section
open Set Function Manifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Paper

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The actual total phase differential in source-first original joint
coordinates. No phase-value bound or produced inverse is included. -/
def finitePositiveTotalPhaseCoordinates
    (Data : IncrementsOriginalNativeData n d N M P) (nu : Fin Data.primaryCount)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (n+d) → ℝ) : Fin (n+d) → ℝ :=
  fun r => fderiv ℝ
    (Data.phase nu ∘ incrementsOriginalJointPoint Data.atlas Data.parameterChart i)
    y (Pi.single r 1)

/-- The given chart change, written directly in the original source-first
coordinate order. This is not an adapted chart produced by the solver. -/
def finitePositiveOriginalTransition
    (Data : IncrementsOriginalNativeData n d N M P)
    (i k : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (n+d) → ℝ) : Fin (n+d) → ℝ :=
  Fin.append
    (fun r => Data.atlas.chart k.1 (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).2 r)
    (fun r => Data.parameterChart k.2 (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).1 r)

def finitePositiveOriginalTransitionDomain
    (Data : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) ×
      (Fin Data.atlas.count × Fin Data.parameterCount)) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalDifferentiation Data.atlas Data.parameterChart ik.1 ∩
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart ik.1) ⁻¹'
      ((Data.parameterChart ik.2.2).source ×ˢ (Data.atlas.chart ik.2.1).source)

def finitePositiveOriginalTransitionSample
    (Data : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) ×
      (Fin Data.atlas.count × Fin Data.parameterCount)) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
    Data.parameterNormDomain Data.parameterSet ik.1 ∩ finitePositiveOriginalTransitionDomain Data ik

def finitePositiveOriginalTransitionDifferentialCoordinates
    (Data : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin Data.atlas.count × Fin Data.parameterCount) ×
      (Fin Data.atlas.count × Fin Data.parameterCount))
    (y : Fin (n+d) → ℝ) : Fin ((n+d)*(n+d)) → ℝ :=
  fun a => fderiv ℝ (finitePositiveOriginalTransition Data ik.1 ik.2) y
    (Pi.single (finProdFinEquiv.symm a).2 1) (finProdFinEquiv.symm a).1

/-- Complete original input norms: base-two F, H, cutoff, given normal,
spatial phase covector, genuine linear functional, total phase
differential, and total differential of the given coordinate transition. -/
def finitePositiveGivenInputProfile
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  max (incrementsOriginalInputProfileWithLinear Data j ell)
    (max (⨆ nu : Fin Data.primaryCount,
      paperAtlasWeighted 0 j ell (finitePositiveTotalPhaseCoordinates Data nu)
        (incrementsOriginalPrimaryDifferentiation Data nu) (incrementsOriginalPrimaryEvaluation Data nu))
      (paperAtlasWeighted 0 j ell (finitePositiveOriginalTransitionDifferentialCoordinates Data)
        (finitePositiveOriginalTransitionDomain Data) (finitePositiveOriginalTransitionSample Data)))

/-- Only the displayed finite list of actual weighted original norms is
an entrance condition. No inactive extension or constructed output occurs. -/
def FinitePositiveGivenPrefix
    (Data : IncrementsOriginalNativeData n d N M P)
    (J : ℕ) (allowed : ℕ → ℝ) (ell : ℝ) : Prop :=
  ∀ j, j ≤ J → finitePositiveGivenInputProfile Data j ell ≤ ENNReal.ofReal (allowed j)

variable [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]

/-- Literal original estimates at a displayed finite entrance. C precedes
all scales, and the common U inside AtScale precedes every observation j. -/
def FinitePositiveIncrementFiniteEntrance
    (Data : IncrementsOriginalNativeData n d N M P)
    (q J : ℕ) (allowed : ℕ → ℝ) (Theta : ℝ) : Prop :=
  0 < Theta ∧ Theta ≤ 1 ∧
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ell, 0 < ell → ell ≤ 1 → FinitePositiveGivenPrefix Data J allowed ell →
      ∀ tau delta, 0 < delta → delta ≤ tau → tau ≤ ell → tau/ell < Theta →
        FinitePositiveIncrementAtScale Data q C ell tau delta

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.finitePositiveGivenInputProfile
#print axioms GlobalEmbedding.Paper.FinitePositiveIncrementFiniteEntrance
