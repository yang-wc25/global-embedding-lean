import NormalPolar.ParameterDisplacementCombinedIterateNaturality
import NormalPolar.ParameterDisplacementFirstIncrementJets
import NormalPolar.ActualProbeSecondaryParameterSource

/-!
# The complete physical U0 and its actual native parameter-chart realization

U0 is the common primary at the actual finite background iterate plus every
ordered signed mixed-secondary reconstruction. Both chart representatives
come from the same primitive sources. For joint derivatives, the source and
native-data families are supplied on the entire observation variable space;
the proof neither chooses data pointwise nor differentiates a choice.
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
  (phase : Fin r → P × M → ℝ) (tau delta : ℝ)
  (backgroundLength probeLength secondaryLength : ℕ)
  (a : Fin r → OpenPartialHomeomorph (P × M) (P × EuclideanSpace ℝ (Fin (m+1))))
  (target : (b : P) → (x : M) → LinearMap.BilinForm ℝ
    (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (iteration : ℕ)

/-- One literal complete increment on the physical parameter space. The
secondary input is the full actual signed source array for this parameter. -/
def actualParameterCompleteFirstIncrement
    (source : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → ActualProbeSecondaryParameterSource P M m)
    (u : Fin p → ℝ) (z : P × M) : V :=
  actualParameterProbeIteratedPrimary F hF g label c vf phase tau delta
    backgroundLength probeLength a target iteration u z +
  actualParameterSecondarySourceSum F hF source tau secondaryLength z

variable (B : OpenPartialHomeomorph P Ep)
  (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
  (ha : ∀ l, Round3ParameterChartPreserves (a l))
  {n order : ℕ} {ell Mg CH : ℝ} {W : Set (Ep × M)}

include hg ha

theorem actual_complete_first_increment_native_parameter
    (source : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → ActualProbeSecondaryParameterSource P M m)
    (data : ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
      ActualSecondaryPhysicalPieceData (m := m) (fun t => F (B.symm t)) (fun t => hF (B.symm t))
        n order ell Mg CH delta W)
    (hdata : ∀ rec k, ActualProbeSecondaryParameterBinding F hF B (source rec k) (data rec k).base)
    (u : Fin p → ℝ) (b : Ep) (hb : b ∈ B.target) (x : M) :
    let Fbar := fun t => F (B.symm t)
    let hFbar := fun t => hF (B.symm t)
    let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
    let cbar := fun l t => c l (B.symm t)
    let vfbar := fun l t => vf l (B.symm t)
    let phasebar := fun l z => phase l (B.symm z.1,z.2)
    let abar := fun l => round3ParameterChartPullback B (a l)
    let input := round4ActualBackgroundMeanIterate Fbar hFbar gbar backgroundLength tau delta
      (fun t => target (B.symm t))
      (round4PrescribedNativeMean label Fbar hFbar cbar vfbar phasebar tau probeLength abar) iteration u
    actualProbeCompleteFirstIncrement Fbar hFbar gbar label cbar vfbar phasebar
      backgroundLength probeLength abar input u data tau secondaryLength (b,x) =
    actualParameterCompleteFirstIncrement F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration source u (B.symm b,x) := by
  intro Fbar hFbar gbar cbar vfbar phasebar abar input
  exact congrArg₂ (fun v w : V => v+w)
    (actualParameterProbeIteratedPrimary_native_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a target B hg ha iteration u b hb x)
    (actual_secondary_parameter_native_sum F hF B source (fun rec k => (data rec k).base)
      hdata tau secondaryLength b hb x)

section JointFamily
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (source : Y → ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary → ActualProbeSecondaryParameterSource P M m)
  (data : Y → ActualSecondarySignedRecord (Λ ⊕ Fin r) → SubSecondary →
    ActualSecondaryPhysicalPieceData (m := m) (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      n order ell Mg CH delta W)
  (hdata : ∀ y rec k, ActualProbeSecondaryParameterBinding F hF B (source y rec k) (data y rec k).base)
  (u : Y → Fin p → ℝ) (b : Y → Ep) (x : Y → M) (y : Y)
  (hb : ContinuousAt b y) (hy : b y ∈ B.target)

include hdata hb hy

theorem actual_complete_first_increment_native_parameter_germ :
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
    (fun z => actualProbeCompleteFirstIncrement Fbar hFbar gbar label cbar vfbar phasebar
      backgroundLength probeLength abar (input z) (u z) (data z) tau secondaryLength (b z,x z)) =ᶠ[𝓝 y]
    (fun z => actualParameterCompleteFirstIncrement F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration (source z) (u z) (B.symm (b z),x z)) := by
  intro Fbar hFbar gbar cbar vfbar phasebar abar input
  filter_upwards [hb.preimage_mem_nhds (B.open_target.mem_nhds hy)] with z hz
  exact actual_complete_first_increment_native_parameter F hF g label c vf phase tau delta
    backgroundLength probeLength secondaryLength a target iteration B hg ha (source z) (data z)
    (hdata z) (u z) (b z) hz (x z)

/-- Every joint jet of the complete physical increment is exactly the native
jet of the same common primary and full signed secondary construction. This
does not assert smoothness of an arbitrary source family: it transports
actual derivatives once supplied, on the unchanged genuine chart domain. -/
theorem actual_complete_first_increment_native_parameter_jets (j : ℕ) :
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
    iteratedFDeriv ℝ j (fun z => actualParameterCompleteFirstIncrement F hF g label c vf phase tau delta
      backgroundLength probeLength secondaryLength a target iteration (source z) (u z) (B.symm (b z),x z)) y := by
  intro Fbar hFbar gbar cbar vfbar phasebar abar input
  exact ((actual_complete_first_increment_native_parameter_germ F hF g label c vf phase tau delta
    backgroundLength probeLength secondaryLength a target iteration B hg ha source data hdata u b x y hb hy).iteratedFDeriv ℝ j).eq_of_nhds

end JointFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_complete_first_increment_native_parameter
#print axioms GlobalEmbedding.Continuation.actual_complete_first_increment_native_parameter_jets
