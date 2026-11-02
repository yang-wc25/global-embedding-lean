import NormalPolar.ActualProbeSecondaryParameterSource
import Probes.Round3ParameterSecondaryForcingNaturality

/-!
# The actual common-primary forcing on a physical parameter space

These definitions use the literal negative symmetric quadratic coefficient
of the complete primary amplitudes, including the cutoff and fast spatial
derivatives already in those amplitudes.  Both inverse-coordinate Jacobians
are retained.  Naturality of the two forcing channels follows from equality
of the primary spatial slices, rather than being assumed as an output field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {P Q M Label : Type*} [TopologicalSpace P]
  [TopologicalSpace Q] [TopologicalSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)

def actualParameterPrimaryQuadratic
    (phase : Label → P × M → ℝ) (R J : Label → P × M → V)
    (tau : ℝ) (e : OpenPartialHomeomorph M D) (r : (Label × Label) × Fin 4) :=
  incrementsSecondaryQuadraticForcing
    (fun l p x => phase l (p, e.symm x)) tau
    (fun (_ : Label) (_ : P) (_ : Unit) (_ : D) => (1 : ℝ))
    (fun l p (_ : Unit) x => R l (p, e.symm x))
    (fun l p (_ : Unit) x => J l (p, e.symm x))
    (fun i _ => EuclideanSpace.single i 1) r.1.1 r.1.2 r.2

def actualParameterSecondarySourceOfPrimary
    (phase : Label → P × M → ℝ) (R J : Label → P × M → V)
    (tau : ℝ) (r : (Label × Label) × Fin 4)
    (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart) : ActualProbeSecondaryParameterSource P M m where
  c := c.c
  chart := c.chart
  chart_preserves := hc
  forcingR := round3ParameterInverseForcing (round3ParameterSecondaryTransition c)
    (c.cutoff ∘ ((OpenPartialHomeomorph.refl P).prod c.host).symm)
    (fun z => actualRealTensorAssembly (actualParameterPrimaryQuadratic phase R J tau c.host r z))
  forcingI := round3ParameterInverseForcing (round3ParameterSecondaryTransition c)
    (c.cutoff ∘ ((OpenPartialHomeomorph.refl P).prod c.host).symm)
    (fun z => actualImaginaryTensorAssembly (actualParameterPrimaryQuadratic phase R J tau c.host r z))
  phase := fun z => ![phase r.1.1 z + phase r.1.2 z,
    phase r.1.1 z - phase r.1.2 z, -phase r.1.1 z + phase r.1.2 z,
    -phase r.1.1 z - phase r.1.2 z] r.2

variable (B : OpenPartialHomeomorph P Q)
  (phase : Label → P × M → ℝ)
  (R J : Label → P × M → EuclideanSpace ℝ (Fin N))
  (phaseQ : Label → Q × M → ℝ)
  (RQ IQ : Label → Q × M → EuclideanSpace ℝ (Fin N))
  (hphase : ∀ l t, t ∈ B.target → ∀ x, phaseQ l (t, x) = phase l (B.symm t, x))
  (hR : ∀ l t, t ∈ B.target → ∀ x, RQ l (t, x) = R l (B.symm t, x))
  (hI : ∀ l t, t ∈ B.target → ∀ x, IQ l (t, x) = J l (B.symm t, x))

include hphase hR hI

theorem actual_parameter_primary_quadratic_pullback
    (tau : ℝ) (e : OpenPartialHomeomorph M D) (r : (Label × Label) × Fin 4)
    (t : Q) (ht : t ∈ B.target) (x : D) :
    actualParameterPrimaryQuadratic phaseQ RQ IQ tau e r (t, x) =
      actualParameterPrimaryQuadratic phase R J tau e r (B.symm t, x) := by
  have hp (l : Label) : (fun y => phaseQ l (t, e.symm y)) =
      (fun y => phase l (B.symm t, e.symm y)) := funext fun y => hphase l t ht (e.symm y)
  have hr (l : Label) : (fun (_ : Unit) y => RQ l (t, e.symm y)) =
      (fun (_ : Unit) y => R l (B.symm t, e.symm y)) :=
    funext fun _ => funext fun y => hR l t ht (e.symm y)
  have hi (l : Label) : (fun (_ : Unit) y => IQ l (t, e.symm y)) =
      (fun (_ : Unit) y => J l (B.symm t, e.symm y)) :=
    funext fun _ => funext fun y => hI l t ht (e.symm y)
  unfold actualParameterPrimaryQuadratic incrementsSecondaryQuadraticForcing
    incrementsSecondaryPhysicalCoefficient
  dsimp only
  simp only [hp, hr, hi]

theorem actual_parameter_primary_forcing_pullback
    (tau : ℝ) (r : (Label × Label) × Fin 4)
    (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart)
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t, x) ∈ c.chart.target) :
    let s := actualParameterSecondarySourceOfPrimary phase R J tau r c hc
    let sq := actualParameterSecondarySourceOfPrimary phaseQ RQ IQ tau r (c.pullback B)
      (round3ParameterChartPullback_preserves B c.chart hc)
    sq.forcingR (t, x) = s.forcingR (B.symm t, x) ∧
      sq.forcingI (t, x) = s.forcingI (B.symm t, x) := by
  intro s sq
  constructor
  · apply round3ParameterInverseForcing_pullback c B hc _ _ _ t ht x hx
    intro b hb y
    apply congrArg actualRealTensorAssembly
    exact actual_parameter_primary_quadratic_pullback B phase R J phaseQ RQ IQ
      hphase hR hI tau c.host r b hb y
  · apply round3ParameterInverseForcing_pullback c B hc _ _ _ t ht x hx
    intro b hb y
    apply congrArg actualImaginaryTensorAssembly
    exact actual_parameter_primary_quadratic_pullback B phase R J phaseQ RQ IQ
      hphase hR hI tau c.host r b hb y

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_parameter_primary_quadratic_pullback
#print axioms GlobalEmbedding.Continuation.actual_parameter_primary_forcing_pullback
