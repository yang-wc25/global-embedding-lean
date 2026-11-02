import Probes.ActualSecondaryQuadraticConstruction
import Smoothing.ParameterRound2IdentityRefinementSamples

/-! Restrict the same actual secondary geometry to the final positive open
germ. No phase, inverse function, coefficient, cutoff or numerical constant
is changed. Supports and sample sets are restricted to their genuine domains.
The relative support fields are exactly those of the existing RawGeometry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

namespace ActualSecondaryRawGeometry
variable {n j : ℕ} {ell Mg : ℝ} {W : Set (Ep × M)}

def restrictOpen {N : ℕ} {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    (d : ActualSecondaryRawGeometry (m := m) (N := N) F hF n j ell Mg W)
    (G : Set (Ep × M)) (hG : IsOpen G) (hGW : G ⊆ W) :
    ActualSecondaryRawGeometry (m := m) (N := N) F hF n j ell Mg G where
  c := d.c
  chart := d.chart.restrOpen G hG
  sample := d.sample ∩ (d.chart.restrOpen G hG).target
  sample_subset := fun _ hz => hz.2
  support := G ∩ d.support
  support_closed := by
    let inclusion : G → W := fun y => ⟨y.val,hGW y.property⟩
    have hc : Continuous inclusion := continuous_subtype_val.subtype_mk _
    have hh := d.support_closed.preimage hc
    convert hh using 1
    ext y
    exact and_iff_right y.property
  support_source := fun _ hz => ⟨d.support_source hz.2,hz.1⟩
  source_domain := fun _ hz => hz.2
  chart_smooth := d.chart_smooth.mono (fun _ hz => hz.1)
  inverse := fun z hz => d.inverse z hz.1
  phase := d.phase
  phase_smooth := d.phase_smooth.mono (fun _ hz => hz.1)
  adaptation := fun y hy => d.adaptation y hy.1
  brows_smooth := d.brows_smooth.mono (fun _ hz => hz.1)
  inverse_smooth := d.inverse_smooth.mono (fun _ hz => hz.1)
  transverse_smooth := d.transverse_smooth.mono (fun _ hz => hz.1)
  value_smooth := d.value_smooth.mono (fun _ hz => hz.1)
  coefficientA_smooth := d.coefficientA_smooth.mono (fun _ hz => hz.1)
  coefficientB_smooth := d.coefficientB_smooth.mono (fun _ hz => hz.1)
  brows_bound := fun k hk z hz => d.brows_bound k hk z hz.1
  transverse_bound := fun k hk z hz => d.transverse_bound k hk z hz.1
  inverse_bound := fun k hk z hz => d.inverse_bound k hk z hz.1
  value_bound := fun k hk z hz => d.value_bound k hk z hz.1
  coefficientA_bound := fun k hk z hz => d.coefficientA_bound k hk z hz.1
  coefficientB_bound := fun k hk z hz => d.coefficientB_bound k hk z hz.1
  spatialChart := d.spatialChart
  coordinate := d.coordinate
  maximal := d.maximal
  target := fun z hz => d.target z hz.1
  immersion := fun z hz => d.immersion z hz.1
  gram := fun z hz => d.gram z hz.1

theorem restrictOpen_functions {N : ℕ} {F : Ep → M → EuclideanSpace ℝ (Fin N)}
    {hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
      𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
    (d : ActualSecondaryRawGeometry (m := m) (N := N) F hF n j ell Mg W)
    (G : Set (Ep × M)) (hG : IsOpen G) (hGW : G ⊆ W) :
    (d.restrictOpen G hG hGW).c = d.c ∧
    ((d.restrictOpen G hG hGW).chart : Ep × M → X) = d.chart ∧
    ((d.restrictOpen G hG hGW).chart.symm : X → Ep × M) = d.chart.symm ∧
    (d.restrictOpen G hG hGW).phase = d.phase ∧
    (d.restrictOpen G hG hGW).spatialChart = d.spatialChart :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

end ActualSecondaryRawGeometry

theorem actual_secondary_relative_cutoff_restrict
    (cutoff : Ep × M → ℝ) (W G K : Set (Ep × M))
    (hW : IsOpen W) (hG : IsOpen G) (hGW : G ⊆ W)
    (hsupport : tsupport (fun y : W => cutoff y.val) ⊆ Subtype.val ⁻¹' K) :
    tsupport (fun y : G => cutoff y.val) ⊆ Subtype.val ⁻¹' (G ∩ K) := by
  intro y hy
  refine ⟨y.property,?_⟩
  have hsmall : y.val ∈ incrementsGlobalRelativeSupport G cutoff := ⟨y,hy,rfl⟩
  rw [parameterRound2_global_relativeSupport_eq G hG] at hsmall
  have hrel : y.val ∈ incrementsGlobalRelativeSupport W cutoff := by
    rw [parameterRound2_global_relativeSupport_eq W hW]
    exact ⟨hGW y.property,hsmall.2⟩
  obtain ⟨z,hz,he⟩ := hrel
  have hh := hsupport hz
  change z.val ∈ K at hh
  simpa only [he] using hh

/-- Restriction preserves the genuine intersection of a subordinate cutoff
and the two primary supports, even when they meet the boundary of the germ. -/
theorem actual_secondary_relative_pair_cutoff_restrict
    (cutoff chi psi : Ep × M → ℝ) (W G K : Set (Ep × M))
    (hW : IsOpen W) (hG : IsOpen G) (hGW : G ⊆ W)
    (hsupport : tsupport (fun y : W => cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W chi ∩ incrementsGlobalRelativeSupport W psi) ⊆
        Subtype.val ⁻¹' K) :
    tsupport (fun y : G => cutoff y.val) ∩
      Subtype.val ⁻¹' (incrementsGlobalRelativeSupport G chi ∩ incrementsGlobalRelativeSupport G psi) ⊆
        Subtype.val ⁻¹' (G ∩ K) := by
  rintro y ⟨hy,hpair⟩
  refine ⟨y.property,?_⟩
  have hmono (f : Ep × M → ℝ) : incrementsGlobalRelativeSupport G f ⊆
      incrementsGlobalRelativeSupport W f := by
    rw [parameterRound2_global_relativeSupport_eq G hG,
      parameterRound2_global_relativeSupport_eq W hW]
    exact fun _ hz => ⟨hGW hz.1,hz.2⟩
  have hrel : y.val ∈ incrementsGlobalRelativeSupport W cutoff := hmono cutoff ⟨y,hy,rfl⟩
  obtain ⟨z,hz,hzy⟩ := hrel
  have heq : z = (⟨y.val,hGW y.property⟩ : W) := Subtype.ext hzy
  apply hsupport (a := (⟨y.val,hGW y.property⟩ : W))
  exact ⟨by simpa only [heq] using hz,hmono chi hpair.1,hmono psi hpair.2⟩

theorem actual_secondary_relative_pair_support_restrict
    (chi psi : Ep × M → ℝ) (W G K : Set (Ep × M))
    (hW : IsOpen W) (hG : IsOpen G)
    (hpair : K ⊆ incrementsGlobalRelativeSupport W chi ∩ incrementsGlobalRelativeSupport W psi) :
    G ∩ K ⊆ incrementsGlobalRelativeSupport G chi ∩ incrementsGlobalRelativeSupport G psi := by
  intro y hy
  have hh := hpair hy.2
  rw [parameterRound2_global_relativeSupport_eq W hW,
    parameterRound2_global_relativeSupport_eq W hW] at hh
  rw [parameterRound2_global_relativeSupport_eq G hG,
    parameterRound2_global_relativeSupport_eq G hG]
  exact ⟨⟨hy.1,hh.1.2⟩,⟨hy.1,hh.2.2⟩⟩

#print axioms actual_secondary_relative_pair_cutoff_restrict
#print axioms actual_secondary_relative_pair_support_restrict
#print axioms ActualSecondaryRawGeometry.restrictOpen
#print axioms ActualSecondaryRawGeometry.restrictOpen_functions
#print axioms actual_secondary_relative_cutoff_restrict
end GlobalEmbedding.Continuation
