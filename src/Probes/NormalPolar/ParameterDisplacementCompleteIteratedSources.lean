import NormalPolar.ParameterDisplacementCompleteParameterNaturality
import NormalPolar.ParameterDisplacementIteratedSecondaryNaturality

/-!
# The complete physical increment from the actual iterated mixed sources

The secondary sources are constructed from the same complete common
amplitudes at the actual finite background iterate. The only native-data
identities requested are the original five primitive fields. No output wave,
parameter-chart forcing identity, derivative or norm bound is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Ep Λ Β SubSecondary : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)

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
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength secondaryLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

def actualParameterCompleteFirstIncrementFromChoices
    (choice : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec k, Round3ParameterChartPreserves (choice rec k).chart)
    (u : Fin p → ℝ) : P × M → V :=
  actualParameterCompleteFirstIncrement F hF g label c vf phase tau delta
    backgroundLength probeLength secondaryLength a target iteration
    (fun rec k => actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration u rec.val (choice rec k) (hc rec k)) u

variable (B : OpenPartialHomeomorph P Ep)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (ha : ∀ l, Round3ParameterChartPreserves (a l))
  {n order : ℕ} {ell Mg CH : ℝ} {W : Set (Ep × M)}
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (choice : Y → ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → Round3ParameterSecondaryChoice P M m)
  (hc : ∀ y rec k, Round3ParameterChartPreserves (choice y rec k).chart)
  (data : Y → ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
    ActualSecondaryPhysicalPieceData (m := m) (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      n order ell Mg CH delta W)
  (u : Y → Fin p → ℝ)

include hg ha

theorem actual_complete_first_increment_from_iterated_primitives_jets
    (hprimitive : ∀ y rec k,
      let sq := actualParameterProbeIteratedSecondarySource
        (fun t => F (B.symm t)) (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
        label (fun l t => c l (B.symm t)) (fun l t => vf l (B.symm t))
        (fun l z => phase l (B.symm z.1,z.2)) tau delta backgroundLength probeLength
        (fun l => round3ParameterChartPullback B (a l)) (fun t => target (B.symm t)) iteration (u y) rec.val
        ((choice y rec k).pullback B) (round3ParameterChartPullback_preserves B (choice y rec k).chart (hc y rec k))
      (data y rec k).base.c = sq.c ∧ (data y rec k).base.chart = sq.chart ∧
        (data y rec k).base.phase = sq.phase ∧ (data y rec k).base.hR = sq.forcingR ∧
        (data y rec k).base.hI = sq.forcingI)
    (b : Y → Ep) (x : Y → M) (y : Y) (hb : ContinuousAt b y) (hy : b y ∈ B.target) (j : ℕ) :
    let Fbar := fun t => F (B.symm t)
    let hFbar := fun t => hF (B.symm t)
    let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
    let cbar := fun l t => c l (B.symm t)
    let vfbar := fun l t => vf l (B.symm t)
    let phasebar := fun l z => phase l (B.symm z.1,z.2)
    let abar := fun l => round3ParameterChartPullback B (a l)
    let input := fun z => round4ActualBackgroundMeanIterate Fbar hFbar gbar backgroundLength tau delta
      (fun t => target (B.symm t))
      (round4PrescribedNativeMean label Fbar hFbar cbar vfbar phasebar tau probeLength abar) iteration (u z)
    iteratedFDeriv ℝ j (fun z => actualProbeCompleteFirstIncrement Fbar hFbar gbar label cbar vfbar phasebar
      backgroundLength probeLength abar (input z) (u z) (data z) tau secondaryLength (b z,x z)) y =
    iteratedFDeriv ℝ j (fun z => actualParameterCompleteFirstIncrementFromChoices F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration (choice z) (hc z) (u z) (B.symm (b z),x z)) y := by
  intro Fbar hFbar gbar cbar vfbar phasebar abar input
  let source := fun z rec k => actualParameterProbeIteratedSecondarySource F hF g label c vf phase tau delta
    backgroundLength probeLength a target iteration (u z) rec.val (choice z rec k) (hc z rec k)
  have hbind : ∀ z rec k, ActualProbeSecondaryParameterBinding F hF B (source z rec k) (data z rec k).base := by
    intro z rec k
    obtain ⟨hc0,hchart,hphase,hR,hI⟩ := hprimitive z rec k
    exact actual_parameter_probe_iterated_secondary_native_binding F hF g label c vf phase tau delta
      backgroundLength probeLength a target iteration B hg ha (u z) rec.val (choice z rec k) (hc z rec k)
      (data z rec k).base hc0 hchart hphase hR hI
  exact actual_complete_first_increment_native_parameter_jets F hF g label c vf phase tau delta
    backgroundLength probeLength secondaryLength a target iteration B hg ha source data hbind u b x y hb hy j

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_complete_first_increment_from_iterated_primitives_jets
