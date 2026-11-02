import Smoothing.Round3RepairNormalRebind

/-! Actual normal replacement is consumed by the literal smoothing stage.
Only the new normal's produced full-coordinate estimates are added.  The
phase/cutoff/linear/transition entries are inherited on smaller genuine open
domains, with no multiplicity loss and no smoothed output budget premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)

/-- The fixed packet bound after actual normal rebinding.  The normal estimate
is the producer's original full differentiation norm on the new primary
samples; the existing primary-norm bridge supplies the exact local norm. -/
theorem round3_repair_rebind_fixed_packet_bound
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ ν, IsOpen (Data.primaryDomain ν)) (hNew : ∀ ν, IsOpen (domain ν))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (j : ℕ) (ell Cold Cnormal : ℝ) (hCnormal : 0 ≤ Cnormal)
    (hFinite : parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤)
    (hBound : (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ Cold)
    (hProduced : ∀ ν,
      paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν)).toReal ≤ Cnormal) :
    parameterRound2_originalFixedPacketProfile (round3RepairRebindNormalData Data normal domain) j ell ≠ ⊤ ∧
      (parameterRound2_originalFixedPacketProfile (round3RepairRebindNormalData Data normal domain) j ell).toReal ≤
        max Cold Cnormal := by
  let E := round3RepairRebindNormalData Data normal domain
  have hNormal := parameterRound2_original_primary_normal_packet_bound E hNew normal j ell Cnormal hCnormal hProduced
  have hN (ν : Fin Data.primaryCount) : paperAtlasWeighted 0 j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
      (incrementsOriginalPrimaryDifferentiation E ν) (incrementsOriginalPrimaryEvaluation E ν) ≤ ENNReal.ofReal Cnormal := by
    have hSup := (le_iSup (fun μ : Fin Data.primaryCount => paperAtlasWeighted 0 j ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal μ))
      (incrementsOriginalPrimaryDifferentiation E μ) (incrementsOriginalPrimaryEvaluation E μ)) ν)
    have hFin := ne_top_of_le_ne_top hNormal.1 hSup
    apply (ENNReal.toReal_le_toReal hFin ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hCnormal] using
      (ENNReal.toReal_mono hNormal.1 hSup).trans hNormal.2
  have hLe := round3_repair_rebind_fixed_packet_le Data normal domain hOld hNew hSub j ell _ hN
  have hMaxFinite : max (parameterRound2_originalFixedPacketProfile Data j ell)
      (ENNReal.ofReal Cnormal) ≠ ⊤ :=
    (max_lt (lt_top_iff_ne_top.mpr hFinite) (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)).ne
  refine ⟨ne_top_of_le_ne_top hMaxFinite hLe,?_⟩
  refine (ENNReal.toReal_mono hMaxFinite hLe).trans ?_
  rw [ENNReal.toReal_max hFinite ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hCnormal]
  exact max_le_max hBound le_rfl

namespace Round3RepairOriginalSmoothingStage
variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {r : ℕ} {budget : ℝ} {reference givenPacket : ℕ → ℝ}

/-- Literal SF/SH and the old-state budget are preserved.  The new normal
packet is accounted for explicitly by max with its produced profile. -/
def rebindNormal
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hOld : ∀ ν, IsOpen (Data.primaryDomain ν)) (hNew : ∀ ν, IsOpen (domain ν))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (normalProfile : ℕ → ℝ) (hNormalProfile : ∀ j, 0 ≤ normalProfile j)
    (hProduced : ∀ j ν,
      paperAtlasWeighted 0 j stage.ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν) ≠ ⊤ ∧
      (paperAtlasWeighted 0 j stage.ell (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart (normal ν))
        (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
        (incrementsOriginalPrimaryEvaluation (round3RepairRebindNormalData Data normal domain) ν)).toReal ≤ normalProfile j) :
    Round3RepairOriginalSmoothingStage (round3RepairRebindNormalData Data normal domain)
      BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference (fun j => max (givenPacket j) (normalProfile j)) :=
  { stage with
    given_finite := fun j => (round3_repair_rebind_fixed_packet_bound Data normal domain hOld hNew hSub
      j stage.ell (givenPacket j) (normalProfile j) (hNormalProfile j)
      (stage.given_finite j) (stage.given_bound j) (hProduced j)).1
    given_bound := fun j => (round3_repair_rebind_fixed_packet_bound Data normal domain hOld hNew hSub
      j stage.ell (givenPacket j) (normalProfile j) (hNormalProfile j)
      (stage.given_finite j) (stage.given_bound j) (hProduced j)).2 }

end Round3RepairOriginalSmoothingStage

/-- Linear-functional regularity restricts to the new genuine primary domains. -/
theorem round3_repair_rebind_linear
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hSub : ∀ ν, domain ν ⊆ Data.primaryDomain ν)
    (hLinear : IncrementsOriginalLinearSmoothInputs Data) :
    IncrementsOriginalLinearSmoothInputs (round3RepairRebindNormalData Data normal domain) := by
  refine ⟨fun ν i => (hLinear.linear_coordinates ν i).mono ?_⟩
  intro y hy
  exact ⟨⟨hy.1.1,hSub ν hy.1.2⟩,hy.2⟩

/-- The tensor cone and its reserve use the same phase/cutoff/linear data. -/
theorem round3_repair_rebind_decomposition
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M))
    (hDecomp : IncrementsOriginalQualitativeDecompositionInputs Data) :
    IncrementsOriginalQualitativeDecompositionInputs (round3RepairRebindNormalData Data normal domain) :=
  { hDecomp with }

theorem round3_repair_rebind_reserve
    (Data : IncrementsOriginalNativeData n d N M P)
    (normal : Fin Data.primaryCount → P × M → Ey)
    (domain : Fin Data.primaryCount → Set (P × M)) (rho : ℝ)
    (hReserve : IncrementsOriginalDecompositionReserveInputs Data rho) :
    IncrementsOriginalDecompositionReserveInputs (round3RepairRebindNormalData Data normal domain) rho :=
  ⟨hReserve.reserve_pos,hReserve.lower⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairOriginalSmoothingStage.rebindNormal
#print axioms GlobalEmbedding.Continuation.round3_repair_rebind_decomposition
