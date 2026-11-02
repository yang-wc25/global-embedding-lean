import NormalPolar.ActualProbeSecondaryParameterForcing

/-!
# The same physical secondary source in each original parameter chart

Pull back the primitive source fields, before solving the finite system.
The existing supported-wave naturality theorem identifies the full sum on
the original chart target, including its zero extension. This construction
does not introduce a chosen solver output or a derivative estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {P Q M : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

/-- Primitive identities only on the domains used by the actual spatial
solver. No equality of extensions outside the chart target is required. -/
structure ActualProbeInitialSourcePullbackBinding
    (B : OpenPartialHomeomorph P Q)
    (source : ActualProbeSecondaryParameterSource P M m)
    (native : ActualProbeSecondaryParameterSource Q M m) : Prop where
  c_eq : native.c = fun t => source.c (B.symm t)
  chart_eq : native.chart = round3ParameterChartPullback B source.chart
  phase_eq : ∀ t ∈ B.target, ∀ x, native.phase (t,x) = source.phase (B.symm t,x)
  forcingR_eq : ∀ t ∈ B.target, ∀ x, (B.symm t,x) ∈ source.chart.target →
    native.forcingR (t,x) = source.forcingR (B.symm t,x)
  forcingI_eq : ∀ t ∈ B.target, ∀ x, (B.symm t,x) ∈ source.chart.target →
    native.forcingI (t,x) = source.forcingI (B.symm t,x)

theorem actualProbeInitialSupply_source_wave_pullback
    (B : OpenPartialHomeomorph P Q)
    (source : ActualProbeSecondaryParameterSource P M m)
    (native : ActualProbeSecondaryParameterSource Q M m)
    (binding : ActualProbeInitialSourcePullbackBinding B source native)
    (F : P → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (tau : ℝ) (length : ℕ) (t : Q) (ht : t ∈ B.target) (x : M) :
    native.wave (fun t => F (B.symm t)) (fun t => hF (B.symm t)) tau length (t,x) =
      source.wave F hF tau length (B.symm t,x) := by
  change round3ParameterSupportedWave (fun t => F (B.symm t)) (fun t => hF (B.symm t))
    native.c native.forcingR native.forcingI native.chart native.phase tau length (t,x) = _
  rw [binding.c_eq,binding.chart_eq]
  have h := actual_secondary_parameter_supported_pullback F hF source.c source.chart B
    source.forcingR source.forcingI native.forcingR native.forcingI
    binding.forcingR_eq binding.forcingI_eq source.chart_preserves source.phase tau length t ht x
  simpa only [ActualProbeSecondaryParameterSource.wave,round3ParameterSupportedWave,
    binding.phase_eq t ht x] using h

theorem actualProbeInitialSupply_secondary_sum_pullback_of_binding
    {Label Sub : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
    (F : P → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (source : ActualSecondarySignedRecord Label → Sub → ActualProbeSecondaryParameterSource P M m)
    (native : ActualSecondarySignedRecord Label → Sub → ActualProbeSecondaryParameterSource Q M m)
    (B : OpenPartialHomeomorph P Q)
    (binding : ∀ rec b, ActualProbeInitialSourcePullbackBinding B (source rec b) (native rec b))
    (tau : ℝ) (length : ℕ) (t : Q) (ht : t ∈ B.target) (x : M) :
    actualParameterSecondarySourceSum (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      native tau length (t,x) =
    actualParameterSecondarySourceSum F hF source tau length (B.symm t,x) := by
  unfold actualParameterSecondarySourceSum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro nu _
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  split_ifs with h
  · exact actualProbeInitialSupply_source_wave_pullback B (source ⟨((nu,mu),q),h⟩ b)
      (native ⟨((nu,mu),q),h⟩ b) (binding _ _) F hF tau length t ht x
  · rfl

theorem actualProbeInitialSupply_primary_source_binding
    {Label : Type*}
    (B : OpenPartialHomeomorph P Q)
    (phase : Label → P × M → ℝ) (R J : Label → P × M → V)
    (phaseQ : Label → Q × M → ℝ) (RQ IQ : Label → Q × M → V)
    (hphase : ∀ l t, t ∈ B.target → ∀ x, phaseQ l (t,x) = phase l (B.symm t,x))
    (hR : ∀ l t, t ∈ B.target → ∀ x, RQ l (t,x) = R l (B.symm t,x))
    (hI : ∀ l t, t ∈ B.target → ∀ x, IQ l (t,x) = J l (B.symm t,x))
    (tau : ℝ) (rec : (Label × Label) × Fin 4)
    (choice : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves choice.chart) :
    ActualProbeInitialSourcePullbackBinding B
      (actualParameterSecondarySourceOfPrimary phase R J tau rec choice hc)
      (actualParameterSecondarySourceOfPrimary phaseQ RQ IQ tau rec (choice.pullback B)
        (round3ParameterChartPullback_preserves B choice.chart hc)) := by
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · intro t ht x
    simp only [actualParameterSecondarySourceOfPrimary,hphase _ t ht x]
  · intro t ht x hx
    exact (actual_parameter_primary_forcing_pullback B phase R J phaseQ RQ IQ
      hphase hR hI tau rec choice hc t ht x hx).1
  · intro t ht x hx
    exact (actual_parameter_primary_forcing_pullback B phase R J phaseQ RQ IQ
      hphase hR hI tau rec choice hc t ht x hx).2

def ActualProbeSecondaryParameterSource.pullback
    (source : ActualProbeSecondaryParameterSource P M m)
    (B : OpenPartialHomeomorph P Q) : ActualProbeSecondaryParameterSource Q M m where
  c := fun t => source.c (B.symm t)
  chart := round3ParameterChartPullback B source.chart
  chart_preserves := round3ParameterChartPullback_preserves B source.chart source.chart_preserves
  forcingR := fun z => source.forcingR (B.symm z.1,z.2)
  forcingI := fun z => source.forcingI (B.symm z.1,z.2)
  phase := fun z => source.phase (B.symm z.1,z.2)

theorem ActualProbeSecondaryParameterSource.pullback_wave
    (source : ActualProbeSecondaryParameterSource P M m)
    (B : OpenPartialHomeomorph P Q)
    (F : P → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (tau : ℝ) (length : ℕ) (t : Q) (ht : t ∈ B.target) (x : M) :
    (source.pullback B).wave (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      tau length (t,x) = source.wave F hF tau length (B.symm t,x) := by
  exact actual_secondary_parameter_supported_pullback F hF source.c source.chart B
    source.forcingR source.forcingI
    (fun z => source.forcingR (B.symm z.1,z.2))
    (fun z => source.forcingI (B.symm z.1,z.2))
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    source.chart_preserves source.phase tau length t ht x

theorem actualProbeInitialSupply_secondary_sum_pullback
    {Label Sub : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
    (F : P → M → V) (hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p))
    (source : ActualSecondarySignedRecord Label → Sub → ActualProbeSecondaryParameterSource P M m)
    (B : OpenPartialHomeomorph P Q) (tau : ℝ) (length : ℕ)
    (t : Q) (ht : t ∈ B.target) (x : M) :
    actualParameterSecondarySourceSum (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (fun rec a => (source rec a).pullback B) tau length (t,x) =
    actualParameterSecondarySourceSum F hF source tau length (B.symm t,x) := by
  unfold actualParameterSecondarySourceSum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
  apply Finset.sum_congr rfl
  intro nu _
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  split_ifs with h
  · exact (source ⟨((nu,mu),q),h⟩ a).pullback_wave B F hF tau length t ht x
  · rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.ActualProbeSecondaryParameterSource.pullback_wave
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_source_wave_pullback
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_primary_source_binding
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_secondary_sum_pullback_of_binding
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_secondary_sum_pullback
