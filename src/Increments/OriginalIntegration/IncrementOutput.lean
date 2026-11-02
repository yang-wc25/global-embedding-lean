import FaithfulIntegration.LocalizedDataTransport
import FaithfulIncrements.BufferedInputFiniteness
import OriginalIntegration.RefinedDataTransport
import Repair.FullIncrementNovOriginalSupportedConstruction

/-!
# The literal original output and its internal-domain transport

This definition spells out both original estimates, finiteness of the actual
ENNReal seminorms, one common real U, smooth parameter dependence, and the
original support/pair-intersection conclusion. Internal solver domains never
replace the original norm domains or original physical maps.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.OriginalIntegration
open FaithfulIncrements FaithfulIntegration FaithfulCollars

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

/-- The full same-U conclusion of (6.1), including every original norm domain. -/
def OriginalIncrementOutput (Data : IncrementsOriginalNativeData n d N M P)
    (q : ℕ) (C : ℕ → ℝ) (ell tau delta : ℝ) : Prop :=
  ∃ (G : Set (P × M)) (U : P × M → Ey), IsOpen G ∧
    Data.parameterSet ×ˢ (univ : Set M) ⊆ G ∧
    G ⊆ incrementsOriginalParameterRegion Data ∧
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓘(ℝ,Es)) 𝓘(ℝ,Ey) ∞ U G ∧
    FullIncrementNovOriginalSupportConclusion Data.cutoff G U ∧
    ∀ j, paperAtlasWeighted 0 j tau
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
      (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
        Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau
        (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart U)
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet)).toReal ≤ C j*delta*tau ∧
      paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
          (incrementsOriginalMetricError Data.F U Data.H delta))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j tau
        (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart
          (incrementsOriginalMetricError Data.F U Data.H delta))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet)).toReal ≤
        C j*(delta*(tau/ell)^q+delta^3/tau)

/-- A finite numerical bound contains finiteness, so `toReal ⊤ = 0` cannot
silently admit an infinite original input norm. No higher order is read. -/
def OriginalFinitePrefixBudget (Data : IncrementsOriginalNativeData n d N M P)
    (J : ℕ) (allowed : ℕ → ℝ) (ell : ℝ) : Prop :=
  ∀ j, j ≤ J → actualOriginalGivenInputProfile Data j ell ≠ ⊤ ∧
    (actualOriginalGivenInputProfile Data j ell).toReal ≤ allowed j

/-- Internal source collars do not change a single term of the output. -/
theorem refinedWorkingData_output
    (Data : IncrementsOriginalNativeData n d N M P)
    (R b : ℝ) (hb : 0 < b) (hbuffer : b ≤ Data.atlas.buffer)
    (s : SourceCollarNovFamily Data.atlas Data.sourceNormDomain R b hb)
    (q : ℕ) (C : ℕ → ℝ) (ell tau delta : ℝ) :
    OriginalIncrementOutput (refinedWorkingData Data R b hb hbuffer s) q C ell tau delta ↔
      OriginalIncrementOutput Data q C ell tau delta := Iff.rfl

variable [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]

/-- One output produced on internal solver neighborhoods is an output for
the literal original datum; the very same G, U and C are returned. -/
theorem localPrimaryData_original_output
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hV : V ⊆ Data.parameterOpen) (q : ℕ) (C : ℕ → ℝ) (ell tau delta : ℝ)
    (h : OriginalIncrementOutput (localPrimaryData Data V domain) q C ell tau delta) :
    OriginalIncrementOutput Data q C ell tau delta := by
  obtain ⟨G,U,hG,hKG,hGU,hSmooth,hSupport,hEstimates⟩ := h
  exact ⟨G,U,hG,hKG,localPrimaryData_output_region Data V domain hV G hGU,
    hSmooth,hSupport,hEstimates⟩

/-- Localizing the solver can only decrease the actual original input
profile, at the same scale and with the same prescribed finite budget. -/
theorem localPrimaryData_original_budget
    (Data : IncrementsOriginalNativeData n d N M P)
    (V : Set P) (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ nu, IsOpen (Data.primaryDomain nu)) (hNew : ∀ nu, IsOpen (domain nu))
    (hSub : ∀ nu, domain nu ⊆ Data.primaryDomain nu)
    (J : ℕ) (allowed : ℕ → ℝ) (ell : ℝ)
    (h : OriginalFinitePrefixBudget Data J allowed ell) :
    OriginalFinitePrefixBudget (localPrimaryData Data V domain) J allowed ell :=
  localPrimaryData_given_prefix Data V domain hOld hNew hSub J ell allowed
    (fun j hj => (h j hj).1) (fun j hj => (h j hj).2)

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.localPrimaryData_original_output
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.localPrimaryData_original_budget
