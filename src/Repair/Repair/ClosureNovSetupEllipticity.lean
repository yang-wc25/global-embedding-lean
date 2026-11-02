import Repair.SourceCollarNovSetup
import Probes.ActualOriginalChartImmersion

/-!
# Original source ellipticity gives global slice immersion without collars

The original source inner sets cover the manifold and their coordinates lie
in the original norm domains. Positive differential ellipticity therefore
supplies actual global native immersion; no metric-positivity output or
independent immersion certificate is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology
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
local notation "X" => Ep × D

theorem closureNov_reference_slice_immersion
    (g : SourceCollarNovSetup (m+1) d M P)
    (F0 : P × M → V)
    (hF : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (lower : ℝ) (hLower : 0 < lower)
    (hEll : ∀ p i y, y ∈ g.Omega i → ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.source.chart i).symm x)) y v‖^2) :
    ∀ p x, Function.Injective
      (mfderiv 𝓘(ℝ,D) 𝓘(ℝ,V) (fun y => F0 (p,y)) x) := by
  intro p x
  obtain ⟨i,hi⟩ := g.source.cover x
  have hs := g.source.inner_subset i hi
  have hy := g.source_sampling i
    (bufferedInner_subset_sampling g.source i (bufferedInnerCoordinates_mem g.source i hi))
  have h := actual_increment_immersion_of_chart_reserve (fun y => F0 (p,y)) (hF p)
    (g.source.chart i) (g.source_smooth.chart_mem i) (g.source.chart i x)
    ((g.source.chart i).map_source hs) lower hLower (hEll p i _ hy)
  exact (congrArg (fun q : M => Function.Injective
    (mfderiv 𝓘(ℝ,D) 𝓘(ℝ,V) (fun y => F0 (p,y)) q))
      ((g.source.chart i).left_inv hs)).mp h

/-- Phase reweighting and the positive reference-neighborhood construction
retain the map. This literal equality transports the proved immersion. -/
theorem closureNov_reference_slice_immersion_inputs
    (g : SourceCollarNovSetup (m+1) d M P)
    (F0 : P × M → V)
    (hF : ∀ p, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (fun x => F0 (p,x)))
    (lower : ℝ) (hLower : 0 < lower)
    (hEll : ∀ p i y, y ∈ g.Omega i → ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.source.chart i).symm x)) y v‖^2)
    (Data : IncrementsOriginalNativeData (m+1) d N M P) (hMap : Data.F=F0) :
    IncrementsOriginalSliceImmersionInputs Data := by
  constructor
  intro p _ x
  rw [hMap]
  exact closureNov_reference_slice_immersion g F0 hF lower hLower hEll p x

/-- The same original spatial inequality at the physical parameter gives
the joint-coordinate input consumed by the actual local reference factory. -/
theorem closureNov_reference_joint_ellipticity
    (g : SourceCollarNovSetup (m+1) d M P)
    (F0 : P × M → V) (lower : ℝ)
    (hEll : ∀ p i y, y ∈ g.Omega i → ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ (fun x => F0 (p,(g.source.chart i).symm x)) y v‖^2) :
    ∀ i z, parameterTensorModelEquiv (m+1) d z ∈ g.samples i → ∀ v : D,
      lower*‖v‖^2 ≤ ‖fderiv ℝ ((fun x => F0 ((g.parameter.chart i.2).symm z.1,x)) ∘
        (g.source.chart i.1).symm) z.2 v‖^2 := by
  intro i z hz v
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z)=z.2 at hx
  have hs : z.2 ∈ g.Omega i.1 := by simpa only [hx] using hz.2.1
  exact hEll ((g.parameter.chart i.2).symm z.1) i.1 z.2 hs v

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.closureNov_reference_slice_immersion
#print axioms GlobalEmbedding.Continuation.closureNov_reference_slice_immersion_inputs
#print axioms GlobalEmbedding.Continuation.closureNov_reference_joint_ellipticity
