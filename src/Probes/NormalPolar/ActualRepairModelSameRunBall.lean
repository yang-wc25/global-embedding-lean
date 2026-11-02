import NormalPolar.ActualRepairModelSameRunGlobal
import NormalPolar.ActualRepairModelCentered
import NormalPolar.ActualRepairModelDirections
import NormalPolar.ActualRepairCenteredFamily

/-!
# The same actual repair tails on a genuine centered parameter ball

All source and parameter sampling inclusions follow from the fixed packet.
The centered map is the same literal repair limit in its actual chart.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance actualRepairModelSameRunBallChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelSameRunBallIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

namespace Round3RepairInfiniteBlocks
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial)


open GlobalEmbedding.NormalPolar GlobalEmbedding.Upgrade

/-- Whole-source spatial tails on every parameter in the centered original
ball, for the same actual sum and its actual initial state. -/
theorem actualRepairModelCentered_spatial_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := actualRepairCenteredFamily packet.parameterFamily b p₀ Fstar u -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map u
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 3 tail ≤ ENNReal.ofReal (2*C*s^(228/25 : ℝ)) ∧
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (2*C*s^(264/25 : ℝ)) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (2*C*s^(12 : ℝ)) := by
  intro A Fstar tail C
  let actualTail := fun z => Fstar z-initial.map z
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hcmp (j : ℕ) : probeAtlasCj A j tail ≤
      paperAtlasCj j (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart actualTail)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples :=
    actualRepairModel_centered_spatial_le_total Data.atlas packet.domain.atlas_smooth
      packet.parameterFamily hB packet.Omega packet.Q packet.source_target packet.parameter_target
      packet.parameter_sampling actualTail hSmooth b p₀ hp₀ u hu j
  have hbound := run.probe_original_tail_84 packet hK heps hSmall hDisp hTheta hCap s hs hstart
  exact ⟨(hcmp 3).trans hbound.1,(hcmp 2).trans hbound.2.1,(hcmp 1).trans hbound.2.2⟩

/-- The Hessian/value correction fields, including lower source derivatives,
hold throughout the true centered parameter ball. -/
theorem actualRepairModelCentered_response_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily) (a : Fin d) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := fun x => fderiv ℝ (fun v => actualRepairCenteredFamily packet.parameterFamily b p₀ Fstar v x -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map v x) u (Pi.single a 1)
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal (s^(44/5 : ℝ)*actualRepairModelHessianModulus C s) ∧
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal (s^(10 : ℝ)*actualRepairModelCOneModulus C s) ∧
    probeAtlasCj A 0 tail ≤ ENNReal.ofReal (s^(56/5 : ℝ)*actualRepairModelValueModulus C s) := by
  intro A Fstar tail C
  let actualTail := fun z => Fstar z-initial.map z
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hcmp (j : ℕ) : probeAtlasCj A j tail ≤
      ⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) j 1
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart actualTail i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i) :=
    actualRepairModel_centered_response_le_mixed Data.atlas packet.domain.atlas_smooth
      packet.parameterFamily hB packet.Omega packet.Q packet.source_target packet.parameter_target
      packet.source_sampling packet.parameter_sampling actualTail hSmooth b p₀ hp₀ u hu a j
  have hbound := run.probe_mixed_tail_response_moduli packet hK heps hSmall hDisp hTheta hCap s hs hstart
  rcases actualRepairModel_moduli_eq_original (C := C) hs.le with ⟨hH,hC,hV⟩
  rw [hH,hC,hV]
  exact ⟨(hcmp 2).trans hbound.1,(hcmp 1).trans hbound.2.1,(hcmp 0).trans hbound.2.2⟩

/-- The actual C1/C2 response bounds in every parameter direction. The fixed
finite factor d is exposed; the original Pi norm and ball remain unchanged. -/
theorem actualRepairModelCentered_direction_tails
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (p₀ : P) (hp₀ : p₀ ∈ packet.parameterFamily.inner b)
    (u : Fin d → ℝ) (hu : ‖u‖ < actualRepairParameterRadius packet.parameterFamily)
    (direction : Fin d → ℝ) :
    let A := actualRepairSamplingAtlas Data.atlas packet.Omega
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := fun x => fderiv ℝ (fun v => actualRepairCenteredFamily packet.parameterFamily b p₀ Fstar v x -
      actualRepairCenteredFamily packet.parameterFamily b p₀ initial.map v x) u direction
    let C := round4ParameterProbeTailConstant cost
    probeAtlasCj A 1 tail ≤ ENNReal.ofReal ((d : ℝ)*(s^(10 : ℝ)*actualRepairModelCOneModulus C s)*‖direction‖) ∧
    probeAtlasCj A 2 tail ≤ ENNReal.ofReal ((d : ℝ)*(s^(44/5 : ℝ)*actualRepairModelHessianModulus C s)*‖direction‖) := by
  intro A Fstar tail C
  let actualTail := fun z => Fstar z-initial.map z
  let F := actualRepairCenteredFamily packet.parameterFamily b p₀ actualTail
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ actualTail := hFull.2.1.sub initial.smooth
  have hB : ∀ b, packet.parameterFamily.chart b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hF := actualRepairCenteredFamily_smooth packet.parameterFamily hB b p₀ hp₀ actualTail hSmooth
  have hmod := actualRepairModel_moduli_nonneg (round4ParameterProbeTailConstant_pos cost).le s
  have hcolumns := run.actualRepairModelCentered_response_tails packet hK heps hSmall hDisp hTheta hCap
    s hs hstart b p₀ hp₀ u hu
  have huB : u ∈ Metric.ball 0 (actualRepairParameterRadius packet.parameterFamily) := by
    simpa only [Metric.mem_ball,dist_zero_right] using hu
  exact ⟨actualRepairModel_parameter_direction_of_columns A
    (actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target)
    Metric.isOpen_ball F hF u huB 1 (mul_nonneg (Real.rpow_nonneg hs.le _) hmod.2.1)
    (fun a => (hcolumns a).2.1) direction,
    actualRepairModel_parameter_direction_of_columns A
    (actualRepairSamplingAtlas_smooth Data.atlas packet.domain.atlas_smooth packet.Omega packet.source_target)
    Metric.isOpen_ball F hF u huB 2 (mul_nonneg (Real.rpow_nonneg hs.le _) hmod.1)
    (fun a => (hcolumns a).1) direction⟩

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelCentered_spatial_tails
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelCentered_response_tails
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelCentered_direction_tails

