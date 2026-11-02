import NormalPolar.ActualRepairModelTail
import Probes.Round4ActualRepairResponseModuli

/-!
# Actual same-run repair tail as native parameter-column norms

The true mixed bounds of the existing stay/advance trajectory are converted
to cumulative spatial norms of native parameter columns, with constant one.
The domains are the exact slices of the existing original differentiation
and sampling sets; no whole chart or probe ball coverage is inferred.
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
local instance actualRepairModelSameRunChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelSameRunIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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


open GlobalEmbedding.NormalPolar

/-- Native column of the same literal correction, in a fixed actual parameter
chart. This definition does not replace the final map by a separate field. -/
def actualRepairModelSameRunResponse
    (b : Fin Data.parameterCount) (u : Fin d → ℝ) (a : Fin d)
    (i : Fin Data.atlas.count) (x : Fin (m+1) → ℝ) : Fin N → ℝ :=
  fderiv ℝ (fun v => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => (initial.map z + ∑' j, run.increment packet j z) - initial.map z)
    (i,b) (sourceFirstCoordinates (m+1) d (v,x))) u (Pi.single a 1)

/-- The same open source domain after fixing the actual parameter coordinate. -/
def actualRepairModelSameRunDomain (b : Fin Data.parameterCount) (u : Fin d → ℝ)
    (i : Fin Data.atlas.count) : Set (Fin (m+1) → ℝ) :=
  actualRepairModelSlice u (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart (i,b))

/-- The same original sample set after fixing that parameter coordinate. -/
def actualRepairModelSameRunSamples (b : Fin Data.parameterCount) (u : Fin d → ℝ)
    (i : Fin Data.atlas.count) : Set (Fin (m+1) → ℝ) :=
  actualRepairModelSlice u (packet.closedSamples (i,b))

/-- The actual native column tail on the same original sampled source slice.
This derives the response estimates from the proved run, not from a supplied
response bound. In particular it retains the same initial map and full tail. -/
theorem actualRepairModelSameRun_response_moduli
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ))
    (b : Fin Data.parameterCount) (u : Fin d → ℝ) (a : Fin d) :
    let f := run.actualRepairModelSameRunResponse packet b u a
    let O := actualRepairModelSameRunDomain packet b u
    let S := actualRepairModelSameRunSamples packet b u
    let C := round4ParameterProbeTailConstant cost
    paperAtlasCj 2 f O S ≤ ENNReal.ofReal (s^(44/5 : ℝ)*round4RepairHessianTailModulus C s) ∧
    paperAtlasCj 1 f O S ≤ ENNReal.ofReal (s^(10 : ℝ)*round4RepairCOneTailModulus C s) ∧
    paperAtlasCj 0 f O S ≤ ENNReal.ofReal (s^(56/5 : ℝ)*round4RepairValueTailModulus C s) := by
  intro f O S C
  let tail := fun z => (initial.map z+∑' j, run.increment packet j z)-initial.map z
  let coords := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail
  let fullO := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ tail := hFull.2.1.sub initial.smooth
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hcoords (i) : ContDiffOn ℝ ∞ (coords i) (fullO i) :=
    parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB tail hSmooth i
  have hcmp (j : ℕ) : paperAtlasCj j f O S ≤
      ⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) j 1
        (coords i) (fullO i) (packet.closedSamples i) := by
    have h := actualRepairModel_parameter_atlasCj_le_mixed j
      (fun i => coords (i,b)) (fun i => fullO (i,b)) (fun i => packet.closedSamples (i,b))
      (fun i => parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart (i,b))
      (fun i => hcoords (i,b)) u O S
      (fun i => actualRepairModelSlice_open u
        (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart (i,b)))
      (fun _ => Subset.rfl) (fun _ _ hx => hx.1) (fun _ _ hx => hx) a
    apply h.trans
    apply iSup_le
    intro i
    exact le_iSup (fun k => paperMixedCoordinateCj (nx := m+1) (np := d) j 1
      (coords k) (fullO k) (packet.closedSamples k)) (i,b)
  have hbound := run.probe_mixed_tail_response_moduli packet hK heps hSmall hDisp hTheta hCap s hs hstart
  exact ⟨(hcmp 2).trans hbound.1,(hcmp 1).trans hbound.2.1,(hcmp 0).trans hbound.2.2⟩

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actualRepairModelSameRun_response_moduli
