import OriginalIntegration.FinitePositiveIncrementsStatement
import OriginalIntegration.OriginalFixedDataIncrement

/-!
# Candidate source target for the fixed-decomposition existence assertion

The statement module is independent of the implementation output predicate.
This binding returns the same G, U, and C, preserving every original norm
and support. It makes no stronger class-uniformity claim. No Challenge,
comparator configuration, source acceptance count, or locked target is
modified by this candidate.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Paper
open GlobalEmbedding.Continuation GlobalEmbedding.Continuation.OriginalIntegration
open GlobalEmbedding.Continuation.FaithfulCollars

variable {m d N : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P] [T2Space M] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The implementation's genuine same-U output gives the independently
spelled original conclusion; finite extended norms are preserved. -/
theorem original_increment_output_to_paper
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (q : ℕ) (C : ℕ → ℝ) (ell tau delta : ℝ)
    (out : OriginalIncrementOutput Data q C ell tau delta) :
    FinitePositiveIncrementAtScale Data q C ell tau delta := by
  obtain ⟨G,U,hG,hKG,hRegion,hSmooth,hSupport,hJets⟩ := out
  refine ⟨G,U,hG,hKG,hRegion,hSmooth,hSupport,?_⟩
  intro j
  have hj := hJets j
  exact ⟨(ENNReal.ofReal_toReal hj.1).symm.le.trans (ENNReal.ofReal_le_ofReal hj.2.1),
    (ENNReal.ofReal_toReal hj.2.2.1).symm.le.trans (ENNReal.ofReal_le_ofReal hj.2.2.2)⟩

/-- Candidate canonical binding of the fixed-data existence part of
lem:increments. Every assumption is an original input condition, and no
finite input bound, inverse supplier, prepared packet, or output is given. -/
theorem finite_positive_increments_fixed_data
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data)
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data)
    (rho : ℝ) (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho)
    (c : ℝ) (hEll : IncrementsOriginalCoordinateEllipticityInputs Data c)
    (RSrc bSrc RPar bPar : ℝ)
    (gS : OriginalSourceNormBuffer Data.atlas Data.sourceNormDomain RSrc bSrc)
    (WParam : Fin Data.parameterCount → Set P)
    (gP : OriginalParameterNormBuffer Data.parameterChart Data.parameterNormDomain
      WParam Data.parameterSet RPar bPar)
    (TS TP Parameter Spatial : ℕ → ℝ)
    (hTS : ∀ j, 0 ≤ TS j) (hTP : ∀ j, 0 ≤ TP j)
    (hParameter : ∀ j, 0 ≤ Parameter j) (hSpatial : ∀ j, 0 ≤ Spatial j)
    (Ds Dp : ℕ) (hDs : Data.atlas.supportDegree ≤ Ds)
    (hDp : ∀ i, tensorEnlargedSupportDegree WParam i ≤ Dp)
    (hSTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.atlas.chart p).target,
      (Data.atlas.chart p).symm y ∈ Data.atlas.support i →
      ‖iteratedFDeriv ℝ j (Data.atlas.chart i ∘ (Data.atlas.chart p).symm) y‖ ≤ TS j)
    (hPTrans : ∀ p i j, 1 ≤ j → ∀ y ∈ (Data.parameterChart p).target,
      (Data.parameterChart p).symm y ∈ WParam i →
      (Data.parameterChart p).symm y ∈ (Data.parameterChart i).source →
      ‖iteratedFDeriv ℝ j (Data.parameterChart i ∘ (Data.parameterChart p).symm) y‖ ≤ TP j)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    : FinitePositiveIncrementsFixedData Data := by
  have hRun := original_buffered_fixed_data_increment Data hd hs hp hn hImm hLinear hDecomp
    rho hReserve c hEll RSrc bSrc RPar bPar gS WParam gP TS TP Parameter Spatial
    hTS hTP hParameter hSpatial Ds Dp hDs hDp hSTrans hPTrans transition
  intro q hq
  obtain ⟨Theta,hTheta,hThetaOne,C,hC,hOutput⟩ := hRun q hq
  refine ⟨Theta,hTheta,hThetaOne,C,hC,?_⟩
  intro ell hell hellOne tau delta hdelta hdeltaTau htauEll hRatio
  exact original_increment_output_to_paper Data q C ell tau delta
    (hOutput ell hell hellOne tau delta hdelta hdeltaTau htauEll hRatio)

end GlobalEmbedding.Paper
#print axioms GlobalEmbedding.Paper.original_increment_output_to_paper
#print axioms GlobalEmbedding.Paper.finite_positive_increments_fixed_data
