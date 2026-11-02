import Probes.Round3ParameterPrimaryPhysicalPoint
import Probes.Round3ParameterNativeFamily
import Probes.Round3ParameterWholePrimaryFactory

/-! The SAME all-chart physical primary family supplies genuine physical
geometry in EVERY original parameter chart. Immersion, transverse Gram,
normal kernel and phase adaptation come from the original hypotheses and
actual constructed slice charts; no PhysicalGeometry premise is left. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_original_primary_native_physical_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hPhase : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    {Β : Type*} [Fintype Β]
    (ip : Fin Data.primaryCount → Β → Fin Data.parameterCount)
    (W : Fin Data.primaryCount → Β → Set (Ep × M))
    (piece : ∀ nu beta, Round3PreparedPrimaryPiece Data (ip nu beta) nu (W nu beta))
    (B : OpenPartialHomeomorph P Ep) :
    let g := round3ParameterOriginalPrimaryFamily Data hd hs hn ip W piece
    Nonempty (ActualOriginalPrimaryPhysicalGeometry (fun p x => Data.F (B.symm p,x))
      (fun p => hF (B.symm p)) (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g B)) := by
  intro g
  let gN := round3ParameterNativePrimary (fun p x => Data.F (p,x)) g B
  let e := fun nu beta p => (piece nu beta).slices ((Data.parameterChart (ip nu beta)) (B.symm p))
  have hTarget (nu : Fin Data.primaryCount) (beta : Β) (z : Ep × D)
      (hz : z ∈ (gN.chart nu beta).target) :
      (B.symm z.1,z.2) ∈ (g.chart nu beta).target :=
    ((round3ParameterChartPullback_target B (g.chart nu beta) z).mp hz).2.1
  have hSource (nu : Fin Data.primaryCount) (beta : Β) (z : Ep × M)
      (hz : z ∈ (gN.chart nu beta).source) :
      (B.symm z.1,z.2) ∈ (g.chart nu beta).source :=
    ((round3ParameterChartPullback_source B (g.chart nu beta) z).mp hz).2.1
  exact ⟨{
    slices := e
    maximal := fun nu beta p => (piece nu beta).data.2.2.2.2.1 _
    inverse := fun _ _ => rfl
    target := fun nu beta z hz => round3ParameterLiftedPrimaryChart_slice_target Data (ip nu beta) nu
      (W nu beta) (piece nu beta) (B.symm z.1,z.2) (hTarget nu beta z hz)
    immersion := by
      intro nu beta z hz
      have ha := round3ParameterLiftedPrimaryChart_active Data (ip nu beta) nu (W nu beta)
        (piece nu beta) (B.symm z.1,z.2) (hTarget nu beta z hz)
      exact hImm.immersion (B.symm z.1) ha.2.1 (gN.inverse nu beta z.1 z.2)
    gram := fun nu beta z hz => round3ParameterLiftedPrimaryChart_gram Data hd hs hPhase hF
      (ip nu beta) nu (W nu beta) (piece nu beta) (B.symm z.1,z.2) (hTarget nu beta z hz)
    normalKernel := fun nu beta z hz => round3ParameterLiftedPrimaryChart_normal_kernel Data hd hs hn hF
      (ip nu beta) nu (W nu beta) (piece nu beta) (B.symm z.1,z.2) (hTarget nu beta z hz)
    adaptation := by
      intro nu beta z hz
      change Data.phase nu (B.symm z.1,z.2) = (round3ParameterChartPullback B (g.chart nu beta) z).2 0
      rw [round3ParameterChartPullback_apply]
      exact round3ParameterLiftedPrimaryChart_forward_phase Data (ip nu beta) nu (W nu beta)
        (piece nu beta) (B.symm z.1,z.2) (hSource nu beta z hz) }⟩

theorem round3Parameter_whole_primary_native_physical_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hPhase : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (fun x => Data.F (p,x)))
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta) (B : OpenPartialHomeomorph P Ep) :
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta packet
    Nonempty (ActualOriginalPrimaryPhysicalGeometry (fun p x => Data.F (B.symm p,x))
      (fun p => hF (B.symm p)) (round3ParameterNativePrimary (fun p x => Data.F (p,x)) g B)) := by
  exact round3Parameter_original_primary_native_physical_geometry
    (Β := Round3ParameterWholePrimaryIndex Data theta packet) Data hd hs hPhase hn hImm hF
    (fun _ a => a.1.2) (fun _ a => (Data.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (round3ParameterWholePrimaryPiece Data hd theta packet) B

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_primary_native_physical_geometry
#print axioms GlobalEmbedding.Continuation.round3Parameter_whole_primary_native_physical_geometry
