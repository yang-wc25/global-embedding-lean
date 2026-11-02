import GlobalEmbedding.Paper.PlanarFreeCurveAssembly
import GlobalEmbedding.Paper.PlanarOrbitReparametrization
import GlobalEmbedding.Paper.PlanarHopfFlow
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The actual unit-speed free curve and its constructed global binormal

Source: `main.tex`, `lem:planar`, final assertion and proof, lines 253–266.
DAG: `planar-unit-free-curve-from-planar`.
The actual paraboloid lift is normalized by the genuine constructed canonical
orbit normalization. Every inverse-time and jet input to the accepted geometric
assembly is proved from that construction; no desired curve, solver, inverse,
freeness or binormal is supplied.
-/

noncomputable section
open scoped Manifold ContDiff InnerProductSpace

namespace GlobalEmbedding.Paper

section Native
variable {P M : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [ChartedSpace P M]
    [IsManifold 𝓘(ℝ, P) ∞ M]

/-- A genuine native smooth unit-speed planar map constructs a genuine native
smooth unit-speed free space curve and a global native smooth unit binormal.
All properties concern the same actual common orbit derivative. -/
theorem unit_free_curve_of_unit_planar (R : PeriodOneSmoothFlow 𝓘(ℝ, P) M)
    (f : M → Planar) (hf : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ x, ‖orbitDeriv R.flow f x‖ = 1) :
    ∃ c : M → SpaceCurve, ∃ ν : M → SpaceCurve,
      ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, SpaceCurve) ∞ c ∧
      ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, SpaceCurve) ∞ ν ∧
      (∀ x, ‖orbitDeriv R.flow c x‖ = 1) ∧
      (∀ x, LinearIndependent ℝ ![orbitDeriv R.flow c x,
        orbitDeriv R.flow (orbitDeriv R.flow c) x]) ∧
      (∀ x, ‖ν x‖ = 1) ∧
      (∀ x, ⟪ν x, orbitDeriv R.flow c x⟫_ℝ = 0) ∧
      (∀ x, ⟪ν x, orbitDeriv R.flow (orbitDeriv R.flow c) x⟫_ℝ = 0) := by
  let q : M → SpaceCurve := fun x ↦ planarQuadraticLift (f x)
  have hq : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, SpaceCurve) ∞ q :=
    planarQuadraticLift_contMDiff hf
  have hqfree (x : M) : LinearIndependent ℝ ![orbitDeriv R.flow q x,
      orbitDeriv R.flow (orbitDeriv R.flow q) x] :=
    planarQuadraticLift_native_free R f hf hunit x
  have hn (x : M) : orbitDeriv R.flow q x ≠ 0 := by
    simpa only [Matrix.cons_val_zero] using (hqfree x).ne_zero 0
  have hqv := contMDiff_orbitDeriv R.flow R.smooth q hq
  have hcont (x : M) : Continuous (fun t : ℝ ↦ orbitDeriv R.flow q (R.flow t x)) :=
    hqv.continuous.comp (R.smooth.continuous.comp
      (continuous_id.prodMk continuous_const))
  let c := planarOrbitReparametrized R.flow R.flow_zero R.flow_add R.flow_one q hn hcont
  have hc : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, SpaceCurve) ∞ c :=
    planarOrbitReparametrized_contMDiff R.flow R.flow_zero R.flow_add R.flow_one
      R.smooth q hq hn hcont
  let τ : M → ℝ → ℝ := fun x t ↦
    (planarOrbitNormalizationTimeIso R.flow R.flow_add R.flow_one q hn hcont x).symm t
  have hτ (x : M) : ContDiff ℝ ∞ (τ x) :=
    planarOrbitNormalizationTimeIso_symm_contDiff R.flow R.smooth R.flow_add R.flow_one
      q hq hn hcont x
  have hL (x : M) : 0 < planarOrbitLength R.flow q x :=
    planarOrbitLength_pos R.flow q hn x (hcont x)
  have htime (x : M) : deriv (τ x) 0 ≠ 0 := by
    change deriv (planarOrbitNormalizationTimeIso R.flow R.flow_add R.flow_one
      q hn hcont x).symm 0 ≠ 0
    rw [(planarOrbitNormalizationTimeIso_symm_hasDerivAt R.flow R.flow_add R.flow_one
      q hn hcont x 0).deriv]
    apply inv_ne_zero
    exact div_ne_zero (norm_ne_zero_iff.mpr (hn _)) (ne_of_gt (hL x))
  let b : M → ℝ := fun x ↦ (planarOrbitLength R.flow q x)⁻¹
  have hb (x : M) : b x ≠ 0 := inv_ne_zero (ne_of_gt (hL x))
  have hformula (x : M) (t : ℝ) : c (R.flow t x) = b x • q (R.flow (τ x t) x) :=
    planarOrbitReparametrized_orbit R.flow R.flow_zero R.flow_add R.flow_one
      q hn hcont x t
  obtain ⟨hcfree, ν, hν, hνspec⟩ := normalized_curve_free_binormal_of_orbit_formula
    R q c hq hc hqfree τ
    (fun x ↦ (hτ x).differentiable (by simp))
    (fun x ↦ (contDiff_infty_iff_deriv.mp (hτ x)).2.differentiable (by simp))
    htime b hb hformula
  refine ⟨c, ν, hc, hν, ?_, hcfree, ?_, ?_, ?_⟩
  · exact planarOrbitReparametrized_unitSpeed R.flow R.flow_zero R.flow_add R.flow_one
      q hn hcont
  · exact fun x ↦ (hνspec x).1
  · exact fun x ↦ (hνspec x).2.1
  · exact fun x ↦ (hνspec x).2.2

end Native

/-- The exact whole-Hopf-sphere free-curve conclusion follows from the actual
whole-sphere native unit-speed planar map, with no supplied geometry or inverse.
The original C≥2 provides the positive-C native sphere instance. -/
theorem unit_free_hopf_curve_of_unit_planar {C : ℕ} [Fact (0 < C)]
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (hunit : ∀ z, ‖orbitDeriv planarHopfFlow f z‖ = 1) :
    ∃ c : PlanarHopfSphere C → SpaceCurve, ∃ ν : PlanarHopfSphere C → SpaceCurve,
      ContMDiff (planarHopfModel C) 𝓘(ℝ, SpaceCurve) ∞ c ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, SpaceCurve) ∞ ν ∧
      (∀ z, ‖orbitDeriv planarHopfFlow c z‖ = 1) ∧
      (∀ z, LinearIndependent ℝ ![orbitDeriv planarHopfFlow c z,
        orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow c) z]) ∧
      (∀ z, ‖ν z‖ = 1) ∧
      (∀ z, ⟪ν z, orbitDeriv planarHopfFlow c z⟫_ℝ = 0) ∧
      (∀ z, ⟪ν z, orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow c) z⟫_ℝ = 0) :=
  unit_free_curve_of_unit_planar (planarHopfSmoothFlow C) f hf hunit

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.unit_free_curve_of_unit_planar
#print axioms GlobalEmbedding.Paper.unit_free_hopf_curve_of_unit_planar
