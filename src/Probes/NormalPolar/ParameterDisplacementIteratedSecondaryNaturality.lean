import NormalPolar.ParameterDisplacementIteratedAmplitudeNaturality
import NormalPolar.ActualProbeSecondaryCombinedForcing

/-! The secondary forcing is formed from the actual j-th background iterate
in each native chart. Naturality of that iterate and of both full amplitudes
is proved first, so no equality between independently supplied completed
forcing tensors or iterates is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {P Q M Λ Β : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Λ) (Β := Β) F)
  (label : (Fin r × Bool) ↪ Fin p)
  (c : Fin r → P → EuclideanSpace ℝ (Fin (m+1)) → M)
  (vf : (l : Fin r) → (b : P) → (x : EuclideanSpace ℝ (Fin (m+1))) →
    normalSpace (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (F b) (c l b x))
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

def actualParameterProbeIteratedSecondarySource
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart) : ActualProbeSecondaryParameterSource P M m :=
  actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
    (actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target iteration u false)
    (actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target iteration u true)
    tau rec choice hc

theorem actual_parameter_probe_iterated_secondary_forcing_pullback
    (B : OpenPartialHomeomorph P Q)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (b : Q) (hb : b ∈ B.target) (x : D) (hx : (B.symm b,x) ∈ choice.chart.target) :
    let s := actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u rec choice hc
    let sq := actualParameterProbeIteratedSecondarySource
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => target (B.symm t)) iteration u rec
      (choice.pullback B) (round3ParameterChartPullback_preserves B choice.chart hc)
    sq.forcingR (b,x) = s.forcingR (B.symm b,x) ∧ sq.forcingI (b,x) = s.forcingI (B.symm b,x) := by
  apply actual_parameter_primary_forcing_pullback B (Sum.elim g.phase phase)
    (actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target iteration u false)
    (actualParameterProbeIteratedAmplitude F hF g label c vf phase tau delta backgroundLength probeLength a target iteration u true)
    (Sum.elim (round3ParameterPrimaryPullback F g B).phase (fun l z => phase l (B.symm z.1,z.2))) _ _
    ?_ ?_ ?_ tau rec choice hc b hb x hx
  · intro l t ht y
    cases l <;> rfl
  · intro l t ht y
    exact actualParameterProbeIteratedAmplitude_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a target B hg ha iteration u false l t ht y
  · intro l t ht y
    exact actualParameterProbeIteratedAmplitude_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a target B hg ha iteration u true l t ht y

section Native
variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

/-- In native coordinates this source uses the actual existing native finite
background recurrence, including the full prescribed mean as its forcing. -/
theorem actualParameterProbeIteratedSecondarySource_native
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice Ep M m)
    (hc : Round3ParameterChartPreserves choice.chart) :
    actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u rec choice hc =
    actualParameterProbeCombinedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a
      (round4ActualBackgroundMeanIterate F hF (g.toNative F) backgroundLength tau delta target
        (round4PrescribedNativeMean label F hF c vf phase tau probeLength a) iteration u) u rec choice hc := by
  unfold actualParameterProbeIteratedSecondarySource actualParameterProbeIteratedAmplitude
  rw [actualParameterBackgroundMeanIterate_native]
  rfl

theorem actual_parameter_probe_iterated_secondary_native_binding
    (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
    (ha : ∀ l, Round3ParameterChartPreserves (a l))
    (u : Fin p → ℝ) (rec : ((Λ ⊕ Fin r) × (Λ ⊕ Fin r)) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    {n j : ℕ} {ell Mg CH : ℝ} {W : Set (Ep × M)}
    (d : ActualSecondaryPieceData (m := m)
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) n j ell Mg CH delta W) :
    let s := actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u rec choice hc
    let sq := actualParameterProbeIteratedSecondarySource
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
      label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
      (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
      (fun l => round3ParameterChartPullback B (a l)) (fun t => target (B.symm t)) iteration u rec
      (choice.pullback B) (round3ParameterChartPullback_preserves B choice.chart hc)
    d.c = sq.c → d.chart = sq.chart → d.phase = sq.phase → d.hR = sq.forcingR → d.hI = sq.forcingI →
      ActualProbeSecondaryParameterBinding F hF B s d := by
  intro s sq hdc hdchart hdphase hdR hdI
  refine ⟨hdc,hdchart,?_,?_,?_⟩
  · intro t ht x
    rw [hdphase]
    rcases rec with ⟨⟨l,k⟩,q⟩
    cases l <;> cases k <;> rfl
  · intro t ht x hx
    rw [hdR]
    exact (actual_parameter_probe_iterated_secondary_forcing_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration B hg ha u rec choice hc t ht x hx).1
  · intro t ht x hx
    rw [hdI]
    exact (actual_parameter_probe_iterated_secondary_forcing_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration B hg ha u rec choice hc t ht x hx).2

end Native
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_parameter_probe_iterated_secondary_forcing_pullback
#print axioms GlobalEmbedding.Continuation.actualParameterProbeIteratedSecondarySource_native
#print axioms GlobalEmbedding.Continuation.actual_parameter_probe_iterated_secondary_native_binding
