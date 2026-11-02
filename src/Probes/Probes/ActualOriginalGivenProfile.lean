import Probes.ActualIncrementOriginalOpenCore
import GlobalEmbedding.Paper.IncrementsOriginalLinearArgumentCoordinates

/-! Explicit GIVEN data for quantitative full-parameter estimates.

The frozen Core is retained verbatim. The source fixes the phase packet and
original coordinate transitions; their total differentials are displayed
here as actual coordinate functions. In particular spatial d(phi) alone does
not bound parameter derivatives of exp(i phi/tau). No phase VALUE bound is
inserted. No produced adapted chart, inverse, geometry, mean, iteration or
output error is an entry of this profile.

This makes the fixed-packet dependence explicit. It is not a claim that the
old Core implies these extra given-data bounds or that a full original target
has passed source review. Both differentiation and sample domains are literal
original chart overlaps, with no compactness assumption on M.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

def actualOriginalJointPhase
    (D : IncrementsOriginalNativeData n d N M P) (nu : Fin D.primaryCount)
    (i : Fin D.atlas.count × Fin D.parameterCount) : (Fin (n+d) → ℝ) → ℝ :=
  D.phase nu ∘ incrementsOriginalJointPoint D.atlas D.parameterChart i

def actualOriginalTotalPhaseCoordinates
    (D : IncrementsOriginalNativeData n d N M P) (nu : Fin D.primaryCount)
    (i : Fin D.atlas.count × Fin D.parameterCount)
    (y : Fin (n+d) → ℝ) : Fin (n+d) → ℝ :=
  fun r => fderiv ℝ (actualOriginalJointPhase D nu i) y (Pi.single r 1)

def actualOriginalGivenTransition
    (D : IncrementsOriginalNativeData n d N M P)
    (i k : Fin D.atlas.count × Fin D.parameterCount) : (Fin (n+d) → ℝ) → Fin (n+d) → ℝ :=
  fun y => parameterTensorModelEquiv n d
    (D.parameterChart k.2 (incrementsOriginalJointPoint D.atlas D.parameterChart i y).1,
      D.atlas.chart k.1 (incrementsOriginalJointPoint D.atlas D.parameterChart i y).2)

def actualOriginalGivenTransitionDomain
    (D : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalDifferentiation D.atlas D.parameterChart ik.1 ∩
    (incrementsOriginalJointPoint D.atlas D.parameterChart ik.1) ⁻¹'
      ((D.parameterChart ik.2.2).source ×ˢ (D.atlas.chart ik.2.1).source)

def actualOriginalGivenTransitionSample
    (D : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) : Set (Fin (n+d) → ℝ) :=
  incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
    D.parameterNormDomain D.parameterSet ik.1 ∩ actualOriginalGivenTransitionDomain D ik

def actualOriginalGivenTransitionDifferentialCoordinates
    (D : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount))
    (y : Fin (n+d) → ℝ) : Fin ((n+d)*(n+d)) → ℝ :=
  fun a => fderiv ℝ (actualOriginalGivenTransition D ik.1 ik.2) y
    (Pi.single (finProdFinEquiv.symm a).2 1) (finProdFinEquiv.symm a).1

def actualOriginalGivenInputProfile
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) : ℝ≥0∞ :=
  max (incrementsOriginalInputProfileWithLinear D j ell)
    (max (⨆ nu : Fin D.primaryCount,
      paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates D nu)
        (incrementsOriginalPrimaryDifferentiation D nu) (incrementsOriginalPrimaryEvaluation D nu))
      (paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates D)
        (actualOriginalGivenTransitionDomain D) (actualOriginalGivenTransitionSample D)))

theorem actualOriginalGivenInputProfile_core_le
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) :
    incrementsOriginalCoreInputProfile D j ell ≤ actualOriginalGivenInputProfile D j ell :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem actualOriginalGivenInputProfile_linear_le
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) :
    incrementsOriginalInputProfileWithLinear D j ell ≤ actualOriginalGivenInputProfile D j ell :=
  le_max_left _ _

theorem actualOriginalGivenInputProfile_phase_le
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) (nu : Fin D.primaryCount) :
    paperAtlasWeighted 0 j ell (actualOriginalTotalPhaseCoordinates D nu)
      (incrementsOriginalPrimaryDifferentiation D nu) (incrementsOriginalPrimaryEvaluation D nu) ≤
        actualOriginalGivenInputProfile D j ell :=
  (le_iSup (fun nu : Fin D.primaryCount => paperAtlasWeighted 0 j ell
    (actualOriginalTotalPhaseCoordinates D nu) (incrementsOriginalPrimaryDifferentiation D nu)
      (incrementsOriginalPrimaryEvaluation D nu)) nu).trans
        ((le_max_left _ _).trans (le_max_right _ _))

theorem actualOriginalGivenInputProfile_transition_le
    (D : IncrementsOriginalNativeData n d N M P) (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (actualOriginalGivenTransitionDifferentialCoordinates D)
      (actualOriginalGivenTransitionDomain D) (actualOriginalGivenTransitionSample D) ≤
        actualOriginalGivenInputProfile D j ell :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem actualOriginalGivenTransitionDomain_open
    (D : IncrementsOriginalNativeData n d N M P)
    (ik : (Fin D.atlas.count × Fin D.parameterCount) ×
      (Fin D.atlas.count × Fin D.parameterCount)) : IsOpen (actualOriginalGivenTransitionDomain D ik) :=
  (actual_original_jointPoint_continuousOn D ik.1).isOpen_inter_preimage
    (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart ik.1)
    ((D.parameterChart ik.2.2).open_source.prod (D.atlas.chart ik.2.1).open_source)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualOriginalGivenInputProfile_phase_le
#print axioms GlobalEmbedding.Continuation.actualOriginalGivenTransitionDomain_open
