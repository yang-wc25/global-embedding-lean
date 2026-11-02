import Probes.ActualSecondaryQuadraticConstruction

/-! Actual quadratic forcing cost chosen before the source manifold. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
universe uCanonicalM
variable {m N : ℕ} {Ep M : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 theorem repairEntranceCanonical_quadratic_piece
    (n : ℕ) (MD Kcut : ℝ) (hMD : 0 ≤ MD) (hKcut : 0 ≤ Kcut)
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) :
    ∃ CH : ℝ, 0 ≤ CH ∧
      ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace D M]
        [IsManifold 𝓙 ∞ M] [BoundarylessManifold 𝓙 M],
      ∀ {Label Sub : Type*} [Fintype Sub]
        (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
        (j : ℕ) (ell Mg delta : ℝ) (W : Set (Ep × M))
        (d : ActualSecondaryRawGeometry F hF n j ell Mg W)
        (b : OpenPartialHomeomorph (Ep × M) X) (hhost : d.chart.source ⊆ b.source)
        (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
        (P Q : Label → Ep → Sub → D → V) (nu mu : Label) (q : Fin 4)
        (cutoff : X → ℝ)
        (hc : ContDiffOn ℝ ∞ cutoff (b.symm.trans d.chart).source)
        (he : ContDiffOn ℝ ∞ (b.symm.trans d.chart).symm (b.symm.trans d.chart).target)
        (hcutSupport : ∀ y ∈ b.target, b.symm y ∈ W →
          y ∈ tsupport cutoff →
          y ∈ tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) z nu) ∩
            tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
              (fun i _ => EuclideanSpace.single i 1) z mu) → b.symm y ∈ d.support)
        (hell : 0 < ell)
        (hnu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z nu) (b.symm.trans d.chart).source)
        (hmu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z mu) (b.symm.trans d.chart).source)
        (hnub : ∀ r ≤ n, ∀ z ∈ d.sample, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y nu) ((b.symm.trans d.chart).symm z)‖ ≤ MD*|delta|)
        (hmub : ∀ r ≤ n, ∀ z ∈ d.sample, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y mu) ((b.symm.trans d.chart).symm z)‖ ≤ MD*|delta|)
        (hcut : ∀ r ≤ n, ∀ z ∈ d.sample,
          ell^r*‖iteratedFDeriv ℝ r cutoff ((b.symm.trans d.chart).symm z)‖ ≤ Kcut)
        (hinv : ∀ r, 1 ≤ r → r ≤ n+1 → ∀ z ∈ d.sample,
          ell^(r-1)*‖iteratedFDeriv ℝ r (b.symm.trans d.chart).symm z‖ ≤ T r),
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) nu mu q
      let HR := fun z => actualRealTensorAssembly (H z)
      let HI := fun z => actualImaginaryTensorAssembly (H z)
      let hR := actualSecondaryInverseForcing (b.symm.trans d.chart) cutoff HR
      let hI := actualSecondaryInverseForcing (b.symm.trans d.chart) cutoff HI
      ∃ out : ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W,
        out.base.c = d.c ∧ out.base.chart = d.chart ∧ out.base.phase = d.phase ∧
        out.base.support = d.support ∧ out.base.sample = d.sample ∧
        out.base.hR = hR ∧ out.base.hI = hI ∧
        ∀ tau' length, out.base.wave tau' length =
          actualSecondarySupportedWave F hF d.c hR hI d.chart d.phase tau' length := by
  obtain ⟨CH,hCH,hlocal⟩ := actual_secondary_quadratic_localization_profiles (m := m) n N MD Kcut hMD hKcut T hT
  refine ⟨CH,hCH,?_⟩
  intro M _ _ _ _ Label Sub _ F hF j ell Mg delta W d b hhost phi tau chi P Q nu mu q cutoff hc he hcutSupport
    hell hnu hmu hnub hmub hcut hinv H HR HI hR hI
  have htarget := actual_secondary_host_transition_target d.chart b hhost
  have hsample : d.sample ⊆ (b.symm.trans d.chart).target := by
    rw [htarget]
    exact d.sample_subset
  obtain ⟨hr,hi,hsr,hsi,hsupport,hrb,hib⟩ := hlocal phi tau chi P Q nu mu q
    (b.symm.trans d.chart) cutoff hc he d.sample hsample ell delta hell hnu hmu hnub hmub hcut hinv
  have hr' : ContDiffOn ℝ ∞ hR d.chart.target := by simpa only [htarget] using hr
  have hi' : ContDiffOn ℝ ∞ hI d.chart.target := by simpa only [htarget] using hi
  have hsup : ∀ z ∈ d.chart.target, z ∈ tsupport hR ∪ tsupport hI → d.chart.symm z ∈ d.support := by
    intro z hz hzs
    have hz' : z ∈ (b.symm.trans d.chart).target := by rwa [htarget]
    have hy : (b.symm.trans d.chart).symm z ∈ b.target :=
      ((b.symm.trans d.chart).map_target hz').1
    have hyW : b.symm ((b.symm.trans d.chart).symm z) ∈ W := by
      change b.symm (b (d.chart.symm z)) ∈ W
      rw [b.left_inv (hhost (d.chart.map_target hz))]
      exact d.source_domain (d.chart.map_target hz)
    have hh := hcutSupport _ hy hyW (hsupport z hz' hzs).1 (hsupport z hz' hzs).2
    change b.symm (b (d.chart.symm z)) ∈ d.support at hh
    rwa [b.left_inv (hhost (d.chart.map_target hz))] at hh
  let base : ActualSecondaryPieceData F hF n j ell Mg CH delta W := {
    c := d.c
    chart := d.chart
    sample := d.sample
    sample_subset := d.sample_subset
    support := d.support
    support_closed := d.support_closed
    support_source := d.support_source
    source_domain := d.source_domain
    chart_smooth := d.chart_smooth
    inverse := d.inverse
    phase := d.phase
    phase_smooth := d.phase_smooth
    adaptation := d.adaptation
    brows_smooth := d.brows_smooth
    inverse_smooth := d.inverse_smooth
    transverse_smooth := d.transverse_smooth
    value_smooth := d.value_smooth
    coefficientA_smooth := d.coefficientA_smooth
    coefficientB_smooth := d.coefficientB_smooth
    brows_bound := d.brows_bound
    transverse_bound := d.transverse_bound
    inverse_bound := d.inverse_bound
    value_bound := d.value_bound
    coefficientA_bound := d.coefficientA_bound
    coefficientB_bound := d.coefficientB_bound
    hR := hR
    hI := hI
    forcing_support := hsup
    forcingR_smooth := hr'
    forcingI_smooth := hi'
    forcingR_bound := hrb
    forcingI_bound := hib }
  let out : ActualSecondaryPhysicalPieceData F hF n j ell Mg CH delta W := {
    base := base
    spatialChart := d.spatialChart
    coordinate := d.coordinate
    maximal := d.maximal
    target := d.target
    immersion := d.immersion
    gram := d.gram
    symmetricR := fun z hz => hsr z (by simpa only [htarget] using hz)
    symmetricI := fun z hz => hsi z (by simpa only [htarget] using hz) }
  exact ⟨out,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_quadratic_piece
