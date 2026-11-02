import NormalPolar.PassiveParameterChart
import NormalPolar.ActualProbeSecondaryParameterForcing

/-!
# Passive parameters preserve the actual full signed secondary solver

The host chart, adapted chart, cutoff and spatial inverse are lifted from
their original single-point-parameter data.  Both inverse-coordinate
Jacobians are retained.  The transformed forcing and reconstructed wave
identities are derived from these fields, not assumed for solver outputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {S P M Label : Type*}
  [TopologicalSpace S] [Subsingleton S] [TopologicalSpace P] [TopologicalSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def passiveParameterSecondaryChoice (s₀ : S) (choice : Round3ParameterSecondaryChoice S M m) :
    Round3ParameterSecondaryChoice P M m where
  host := choice.host
  chart := passiveParameterChart s₀ choice.chart
  c := fun _ => choice.c s₀
  cutoff := fun z => choice.cutoff (s₀,z.2)

theorem passiveParameterSecondaryChoice_preserves (s₀ : S)
    (choice : Round3ParameterSecondaryChoice S M m) :
    Round3ParameterChartPreserves (passiveParameterSecondaryChoice (P:=P) s₀ choice).chart :=
  passiveParameterChart_preserves s₀ choice.chart

theorem passiveParameterSecondary_spatialJacobian (s₀ : S)
    (choice : Round3ParameterSecondaryChoice S M m) (b : P) (x : D) :
    actualJointSpatialJacobian
      (round3ParameterSecondaryTransition (passiveParameterSecondaryChoice s₀ choice)).symm (b,x) =
    actualJointSpatialJacobian (round3ParameterSecondaryTransition choice).symm (s₀,x) := rfl

theorem passiveParameterSecondary_inverseForcing (s₀ : S)
    (choice : Round3ParameterSecondaryChoice S M m) (A : S × D → Tensor) (b : P) (x : D) :
    round3ParameterInverseForcing
      (round3ParameterSecondaryTransition (passiveParameterSecondaryChoice s₀ choice))
      ((passiveParameterSecondaryChoice s₀ choice).cutoff ∘
        ((OpenPartialHomeomorph.refl P).prod choice.host).symm)
      (fun z => A (s₀,z.2)) (b,x) =
    round3ParameterInverseForcing (round3ParameterSecondaryTransition choice)
      (choice.cutoff ∘ ((OpenPartialHomeomorph.refl S).prod choice.host).symm) A (s₀,x) := by
  have hp : (choice.chart.symm (s₀,x)).1 = s₀ := Subsingleton.elim _ _
  unfold round3ParameterInverseForcing round3ParameterInverseForcingTensor
  rw [passiveParameterSecondary_spatialJacobian]
  apply congrArg actualTensorBasisCoefficients
  change choice.cutoff (s₀,choice.host.symm (choice.host (choice.chart.symm (s₀,x)).2)) •
      (A (s₀,choice.host (choice.chart.symm (s₀,x)).2)).bilinearComp _ _ =
    choice.cutoff ((choice.chart.symm (s₀,x)).1,
      choice.host.symm (choice.host (choice.chart.symm (s₀,x)).2)) •
      (A ((choice.chart.symm (s₀,x)).1,choice.host (choice.chart.symm (s₀,x)).2)).bilinearComp _ _
  rw [hp]

theorem passiveParameterSecondary_quadratic (s₀ : S)
    (phase : Label → S × M → ℝ) (R J : Label → S × M → V)
    (tau : ℝ) (e : OpenPartialHomeomorph M D) (rec : (Label × Label) × Fin 4)
    (b : P) (x : D) :
    actualParameterPrimaryQuadratic
      (fun l (z : P × M) => phase l (s₀,z.2))
      (fun l (z : P × M) => R l (s₀,z.2))
      (fun l (z : P × M) => J l (s₀,z.2)) tau e rec (b,x) =
    actualParameterPrimaryQuadratic phase R J tau e rec (s₀,x) := rfl

theorem passiveParameterSecondary_forcing (s₀ : S)
    (phase : Label → S × M → ℝ) (R J : Label → S × M → V)
    (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice S M m)
    (hc : Round3ParameterChartPreserves choice.chart) (b : P) (x : D) :
    let source := actualParameterSecondarySourceOfPrimary phase R J tau rec choice hc
    let lifted := actualParameterSecondarySourceOfPrimary
      (fun l (z : P × M) => phase l (s₀,z.2))
      (fun l (z : P × M) => R l (s₀,z.2))
      (fun l (z : P × M) => J l (s₀,z.2)) tau rec
      (passiveParameterSecondaryChoice s₀ choice) (passiveParameterSecondaryChoice_preserves s₀ choice)
    lifted.forcingR (b,x) = source.forcingR (s₀,x) ∧
      lifted.forcingI (b,x) = source.forcingI (s₀,x) := by
  intro source lifted
  constructor
  · exact passiveParameterSecondary_inverseForcing s₀ choice
      (fun z => actualRealTensorAssembly (actualParameterPrimaryQuadratic phase R J tau choice.host rec z)) b x
  · exact passiveParameterSecondary_inverseForcing s₀ choice
      (fun z => actualImaginaryTensorAssembly (actualParameterPrimaryQuadratic phase R J tau choice.host rec z)) b x

section Waves
variable [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem passiveParameterSecondary_supported_wave (s₀ : S)
    (F : S → M → V) (hF : ∀ s, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F s))
    (c : S → D → M)
    (R J : S × D → Fin (m+1) → Fin (m+1) → ℝ)
    (a : OpenPartialHomeomorph (S × M) (S × D)) (phase : S × M → ℝ)
    (tau : ℝ) (length : ℕ) (b : P) (x : M) :
    round3ParameterSupportedWave (fun _ : P => F s₀) (fun _ => hF s₀)
      (fun _ => c s₀) (fun z => R (s₀,z.2)) (fun z => J (s₀,z.2))
      (passiveParameterChart s₀ a) (fun z => phase (s₀,z.2)) tau length (b,x) =
    round3ParameterSupportedWave F hF c R J a phase tau length (s₀,x) := by
  classical
  have ha : a (s₀,x) = (s₀,(a (s₀,x)).2) := Prod.ext (Subsingleton.elim _ _) rfl
  unfold round3ParameterSupportedWave
  simp only [passiveParameterChart_source, passiveParameterChart_apply]
  rw [ha]
  rfl

/-- This is the original negative quadratic source of the given full
amplitudes, transformed through the same two spatial Jacobians. -/
theorem passiveParameterSecondary_primary_wave (s₀ : S)
    (F : S → M → V) (hF : ∀ s, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F s))
    (phase : Label → S × M → ℝ) (R J : Label → S × M → V)
    (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice S M m)
    (hc : Round3ParameterChartPreserves choice.chart)
    (length : ℕ) (b : P) (x : M) :
    (actualParameterSecondarySourceOfPrimary
      (fun l (z : P × M) => phase l (s₀,z.2))
      (fun l (z : P × M) => R l (s₀,z.2))
      (fun l (z : P × M) => J l (s₀,z.2)) tau rec
      (passiveParameterSecondaryChoice s₀ choice)
      (passiveParameterSecondaryChoice_preserves s₀ choice)).wave
      (fun _ : P => F s₀) (fun _ => hF s₀) tau length (b,x) =
    (actualParameterSecondarySourceOfPrimary phase R J tau rec choice hc).wave F hF tau length (s₀,x) := by
  let source := actualParameterSecondarySourceOfPrimary phase R J tau rec choice hc
  let lifted := actualParameterSecondarySourceOfPrimary
    (fun l (z : P × M) => phase l (s₀,z.2))
    (fun l (z : P × M) => R l (s₀,z.2))
    (fun l (z : P × M) => J l (s₀,z.2)) tau rec
    (passiveParameterSecondaryChoice s₀ choice) (passiveParameterSecondaryChoice_preserves s₀ choice)
  have hr : lifted.forcingR = fun z => source.forcingR (s₀,z.2) := by
    funext z
    exact (passiveParameterSecondary_forcing s₀ phase R J tau rec choice hc z.1 z.2).1
  have hi : lifted.forcingI = fun z => source.forcingI (s₀,z.2) := by
    funext z
    exact (passiveParameterSecondary_forcing s₀ phase R J tau rec choice hc z.1 z.2).2
  change round3ParameterSupportedWave (fun _ : P => F s₀) (fun _ => hF s₀)
    (fun _ => source.c s₀) lifted.forcingR lifted.forcingI
    (passiveParameterChart s₀ source.chart) (fun z => source.phase (s₀,z.2)) tau length (b,x) = _
  rw [hr,hi]
  exact passiveParameterSecondary_supported_wave s₀ F hF source.c source.forcingR source.forcingI
    source.chart source.phase tau length b x

end Waves
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveParameterSecondary_forcing
#print axioms GlobalEmbedding.Continuation.passiveParameterSecondary_primary_wave
