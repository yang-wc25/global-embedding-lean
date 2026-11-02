import NormalPolar.ActualProbeSecondaryParameterForcing
import NormalPolar.ParameterDisplacementCombinedParameterNative

/-!
# Same combined background/prescribed source in every parameter chart

The physical source below contains every ordered label in `Λ ⊕ Fin r` and
each of the four signed modes.  Its two forcing channels are constructed
from that actual common primary array.  Their parameter-chart identities
are derived from the actual finite amplitudes, not supplied as assumptions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {P Q M Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, D)

variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → P → EuclideanSpace ℝ (Fin (m + 1)) → M)
  (vf : (l : Fin r) → (b : P) → (x : EuclideanSpace ℝ (Fin (m + 1))) →
    normalSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m + 1))))

def actualParameterProbeCombinedSecondarySource
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart) : ActualProbeSecondaryParameterSource P M m :=
  actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
    (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u false)
    (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u true)
    tau rec choice hc

variable (B : OpenPartialHomeomorph P Q)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (ha : ∀ l, Round3ParameterChartPreserves (a l))

include hg ha

theorem actual_parameter_probe_combined_secondary_forcing_pullback
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t, x) ∈ choice.chart.target) :
    let s := actualParameterProbeCombinedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a input u rec choice hc
    let sq := actualParameterProbeCombinedSecondarySource
      (fun b => F (B.symm b)) (fun b => hF (B.symm b)) (round3ParameterPrimaryPullback F g B)
      label (fun l b => c l (B.symm b)) (fun l b => vf l (B.symm b))
      (fun l z => phase l (B.symm z.1, z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun b => input (B.symm b)) u rec
      (choice.pullback B) (round3ParameterChartPullback_preserves B choice.chart hc)
    sq.forcingR (t, x) = s.forcingR (B.symm t, x) ∧
      sq.forcingI (t, x) = s.forcingI (B.symm t, x) := by
  apply actual_parameter_primary_forcing_pullback B (Sum.elim g.phase phase)
    (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u false)
    (actualParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a input u true)
    (Sum.elim (round3ParameterPrimaryPullback F g B).phase
      (fun l z => phase l (B.symm z.1, z.2))) _ _
    ?_ ?_ ?_ tau rec choice hc t ht x hx
  · intro l b hb y
    cases l <;> rfl
  · intro l b hb y
    exact actualParameterProbeCombinedAmplitude_pullback F hF g label c vf tau delta
      backgroundLength probeLength a B hg ha input u false l b hb y
  · intro l b hb y
    exact actualParameterProbeCombinedAmplitude_pullback F hF g label c vf tau delta
      backgroundLength probeLength a B hg ha input u true l b hb y

section NativeBinding
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- The native piece is bound by its original chart, phase and two constructed
forcing fields.  Its identity with the physical full wave is then a theorem;
no wave, response, or derivative equality is required here. -/
theorem actual_parameter_probe_combined_secondary_native_binding
    (C : OpenPartialHomeomorph P Ep)
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    {n j : ℕ} {ell Mg CH : ℝ} {W : Set (Ep × M)}
    (d : ActualSecondaryPieceData (m := m)
      (fun b => F (C.symm b)) (fun b => hF (C.symm b)) n j ell Mg CH delta W) :
    let s := actualParameterProbeCombinedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a input u rec choice hc
    let sq := actualParameterProbeCombinedSecondarySource
      (fun b => F (C.symm b)) (fun b => hF (C.symm b)) (round3ParameterPrimaryPullback F g C)
      label (fun l b => c l (C.symm b)) (fun l b => vf l (C.symm b))
      (fun l z => phase l (C.symm z.1, z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback C (a l)) (fun b => input (C.symm b)) u rec
      (choice.pullback C) (round3ParameterChartPullback_preserves C choice.chart hc)
    d.c = sq.c → d.chart = sq.chart → d.phase = sq.phase →
      d.hR = sq.forcingR → d.hI = sq.forcingI →
      ActualProbeSecondaryParameterBinding F hF C s d := by
  intro s sq hdc hdchart hdphase hdR hdI
  refine ⟨hdc, hdchart, ?_, ?_, ?_⟩
  · intro t ht x
    rw [hdphase]
    rcases rec with ⟨⟨l, k⟩, q⟩
    cases l <;> cases k <;> rfl
  · intro t ht x hx
    rw [hdR]
    exact (actual_parameter_probe_combined_secondary_forcing_pullback
      F hF g label c vf phase tau delta backgroundLength probeLength a C hg ha
      input u rec choice hc t ht x hx).1
  · intro t ht x hx
    rw [hdI]
    exact (actual_parameter_probe_combined_secondary_forcing_pullback
      F hF g label c vf phase tau delta backgroundLength probeLength a C hg ha
      input u rec choice hc t ht x hx).2

end NativeBinding

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_parameter_probe_combined_secondary_forcing_pullback
#print axioms GlobalEmbedding.Continuation.actual_parameter_probe_combined_secondary_native_binding
