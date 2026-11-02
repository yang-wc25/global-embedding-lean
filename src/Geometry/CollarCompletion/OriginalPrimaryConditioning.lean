import CollarCompletion.OriginalParentSampling
import Repair.FullIncrementNovOpenReferenceProfiles

/-!
# Actual reference conditioning from the literal localized parent

The native support of each actual primary piece is pulled back to the same
physical localized parent. Its original source-inner inclusion is proved,
then the existing conditioning theorem constructs real first/transverse
reserves and all native profiles on the original open parameter region.
No compactness of Q/Omega, global smoothness of F, or K = univ is assumed.
The qualitative compact choices still require the separate original
finite-budget uniformity proof; this theorem does not rename that obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.CollarCompletion

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem original_localized_primary_reference_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      Nonempty (Round3ParameterWholeReferenceProfiles Data hd hs theta packet) := by
  intro theta packet
  apply fullIncrementNov_original_open_reference_profiles Data hd hs hp hImm theta packet
  intro nu i a y hy
  have hyT := (packet.piece nu i a).source_domain ((packet.piece nu i a).support hy)
  have hPhysical := (round3ParameterSupportedPullback_tsupport_iff
    (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).symm
    (theta i) y hyT).mp (packet.native_parent nu i a hy)
  rw [packet.host nu i a]
  exact (original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
    BS TS BP TP Ds Dp RS RP psi i hPhysical).2

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_localized_primary_reference_profiles
