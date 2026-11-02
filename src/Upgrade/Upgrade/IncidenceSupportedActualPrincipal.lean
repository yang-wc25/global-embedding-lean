import Upgrade.IncidenceSupportedPrincipal
import Upgrade.SupportedProbePackets

/-!
# Actual supported-wave packets give the full joint principal frame

Every equation, tensor, normal, and tangent below is the literal object of the
original smooth immersion. The two independent normal families are obtained
by constructing `SupportedJointWavePacket` from the accepted supported-rank
and saturation theorems. No incidence-rank assumption is introduced.
-/

noncomputable section
open Function Manifold Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual source derivative whose orthogonal complement defines the
original normal space. -/
def incidenceActualTangent (F : M → V) (x : M) : E →L[ℝ] V :=
  (tangentSpaceCastModel 𝓘(ℝ, V) (F x)).toContinuousLinearMap.comp
    (mfderiv IM 𝓘(ℝ, V) F x)

theorem incidenceActualTangent_injective (F : M → V) (x : M)
    (himm : Injective (mfderiv IM 𝓘(ℝ, V) F x)) :
    Injective (incidenceActualTangent (n := n) F x) :=
  (tangentSpaceCastModel 𝓘(ℝ, V) (F x)).injective.comp himm

namespace SupportedJointWavePacket

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F} {x y : M}

/-- The actual support-normal columns of the SAME supported defining chart. -/
def equationColumns (p : SupportedJointWavePacket (n := n) (N := N) F hF x y) :
    Fin (n * (n - 1) / 2 + n) → Fin p.chart.codim → ℝ :=
  fun i ↦ fderiv ℝ p.chart.equation
    (LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x))
    ((normalSpace (I := IM) F x).orthogonalProjectionOnto.comp ((p.waves i).tensor x))

/-- Actual old-normal values of those same waves. -/
def valueNormals (p : SupportedJointWavePacket (n := n) (N := N) F hF x y) :
    Fin (n * (n - 1) / 2 + n) → (incidenceActualTangent (n := n) F x).rangeᗮ :=
  fun i ↦ (normalSpace (I := IM) F x).orthogonalProjectionOnto ((p.waves i).value x)

/-- The actual principal map in the independent incidence/value target. -/
def principalMap (p : SupportedJointWavePacket (n := n) (N := N) F hF x y)
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ) :
    (((Fin (n * (n - 1) / 2 + n) × Fin 2) → ℝ) × E) →L[ℝ]
      (Fin p.chart.codim → ℝ) × V :=
  supportedJointPrincipalMap (incidenceActualTangent (n := n) F x)
    p.equationColumns p.valueNormals lambda

/-- This rank is proved from the two actual packet constructions and the
original immersion derivative; it is not a packet premise. -/
theorem principalMap_rank (p : SupportedJointWavePacket (n := n) (N := N) F hF x y)
    (himm : Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    n * (n - 1) / 2 + 2 * n ≤ finrank ℝ (p.principalMap lambda).range := by
  have hA : LinearIndependent ℝ (p.equationColumns ∘ Fin.castAdd n) := p.normal_columns
  have hv : LinearIndependent ℝ
      (p.valueNormals ∘ Fin.natAdd (n * (n - 1) / 2)) := p.value_columns
  have h := supportedJointPrincipalMap_rank (incidenceActualTangent (n := n) F x)
    (incidenceActualTangent_injective F x himm) p.equationColumns p.valueNormals
    lambda hlambda hne (Fin.castAdd n) (Fin.natAdd (n * (n - 1) / 2)) hA hv
  simpa [principalMap, finrank_euclideanSpace_fin, two_mul, add_comm, add_left_comm,
    add_assoc] using! h

/-- Fix actual preimages of a full principal frame before small parameters,
small scale, or fast-angle radial vectors are selected. -/
theorem principalMap_finite_frame (p : SupportedJointWavePacket (n := n) (N := N) F hF x y)
    (himm : Injective (mfderiv IM 𝓘(ℝ, V) F x))
    (lambda : Fin (n * (n - 1) / 2 + n) → Fin 2 → ℝ)
    (hlambda : ∀ i j, 0 < lambda i j) (hne : ∀ i, lambda i 0 ≠ lambda i 1) :
    ∃ d : Fin (n * (n - 1) / 2 + 2 * n) →
        (((Fin (n * (n - 1) / 2 + n) × Fin 2) → ℝ) × E),
      LinearIndependent ℝ (fun i ↦ p.principalMap lambda (d i)) ∧
      ∃ m : ℝ, 0 < m ∧ ∀ c : Fin (n * (n - 1) / 2 + 2 * n) → ℝ,
        m * ‖c‖ ≤ ‖∑ i, c i • p.principalMap lambda (d i)‖ := by
  exact incidenceFiniteFrame_of_rank (p.principalMap lambda) _
    (p.principalMap_rank himm lambda hlambda hne)

end SupportedJointWavePacket

end GlobalEmbedding.Upgrade
