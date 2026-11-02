import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Offline.PairedValueCoincidenceRank
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A protected derivative neighborhood for the actual supported equation

Source: `thm:upgrade`, main.tex 1074 and 1082--1083. The defining equation
comes from the accepted supported-rank geometry. Its derivative is evaluated
at the CURRENT second form. Native continuity produces one actual tolerance
for both the second form and all its normalized probe columns. No rank of
an incidence derivative is supplied.
-/

noncomputable section
open Filter Set Module
open scoped Topology ContDiff
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline

variable {X P : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- One actual neighborhood keeps the original supported defining chart and
all q independent normal columns. Both the base second form and normalized
columns may vary. The tolerance is chosen before all probe fast angles. -/
theorem supported_equation_finite_column_tolerance
    {ambient locus : Set X} {B : X}
    (chart : SupportedLocusLocalEquations ambient locus B)
    {q : ℕ} (A : Fin q → X)
    (hA : LinearIndependent ℝ (fun i ↦ fderiv ℝ chart.equation B (A i))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (C : X) (T : Fin q → X),
      ‖C - B‖ < δ → (∀ i, ‖T i - A i‖ < δ) →
      C ∈ chart.domain ∧
        LinearIndependent ℝ (fun i ↦ fderiv ℝ chart.equation C (T i)) := by
  have hdf : ContinuousAt (fderiv ℝ chart.equation) B :=
    (chart.contDiffOn_equation.contDiffAt
      (chart.isOpen_domain.mem_nhds chart.mem_domain)).continuousAt_fderiv (by simp)
  let Φ : X × (Fin q → X) → (Fin q → Fin chart.codim → ℝ) :=
    fun z i ↦ fderiv ℝ chart.equation z.1 (z.2 i)
  have hΦ : ContinuousAt Φ (B, A) := by
    apply continuousAt_pi.mpr
    intro i
    exact (hdf.comp continuousAt_fst).clm_apply
      ((continuous_apply i).continuousAt.comp continuousAt_snd)
  have hcol : ∀ᶠ z in 𝓝 (B, A), LinearIndependent ℝ (Φ z) :=
    hΦ.eventually hA.eventually
  have hdom : ∀ᶠ z : X × (Fin q → X) in 𝓝 (B, A), z.1 ∈ chart.domain :=
    continuousAt_fst.eventually (chart.isOpen_domain.mem_nhds chart.mem_domain)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hdom.and hcol)
  refine ⟨δ, hδ, fun C T hC hT ↦ ?_⟩
  apply hnear (y := (C, T))
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [dist_eq_norm] using hC
  · rw [dist_eq_norm]
    exact (pi_norm_lt_iff hδ).mpr hT

/-- The literal paired second-form responses force the rank of the actual
composite supported equation. Its local defining derivative is evaluated at
`C u`, so moving normal coordinates are retained. A single tolerance is fixed
before the family, parameter, scale and all angles. The previous strong
supported-rank packet supplies `hA`; no incidence-rank premise occurs.

The global probe errors are allowed at every selected parameter. Pointwise
radial combinations are formed only after differentiating, and their angle
coefficients are never differentiated.

Consume a previously selected actual geometric tolerance. This fixes the
same neighborhood before finite cover and global wave-list assembly. -/
theorem supported_paired_incidence_of_finite_tolerance
    {ambient locus : Set X} {B : X}
    (chart : SupportedLocusLocalEquations ambient locus B)
    {q : ℕ} (A : Fin q → X) (δ : ℝ) (hδ : 0 < δ)
    (hnear : ∀ (C : X) (T : Fin q → X),
      ‖C - B‖ < δ → (∀ i, ‖T i - A i‖ < δ) →
      C ∈ chart.domain ∧
        LinearIndependent ℝ (fun i ↦ fderiv ℝ chart.equation C (T i))) :
    ∀ (C : P → X) (u : P) (σ : ℝ)
      (d0 d1 : Fin q → P) (θ : Fin q → ℝ) (R0 R1 : Fin q → X),
      DifferentiableAt ℝ C u → 0 < σ → ‖C u - B‖ < δ →
      (∀ i, fderiv ℝ C u (d0 i) = (σ * Real.cos (θ i)) • A i + R0 i) →
      (∀ i, fderiv ℝ C u (d1 i) = (σ * Real.sin (θ i)) • A i + R1 i) →
      (∀ i, ‖R0 i‖ ≤ σ * δ / 8) →
      (∀ i, ‖R1 i‖ ≤ σ * δ / 8) →
      C u ∈ chart.domain ∧
        q ≤ finrank ℝ (LinearMap.range (fderiv ℝ (chart.equation ∘ C) u).toLinearMap) := by
  intro C u σ d0 d1 θ R0 R1 hC hσ hclose h0 h1 hR0 hR1
  let d : Fin q → P := fun i ↦ σ⁻¹ • pairedRadialDirection (θ i) (d0 i) (d1 i)
  let T : Fin q → X := fun i ↦ fderiv ℝ C u (d i)
  have herror (i : Fin q) : ‖T i - A i‖ < δ := by
    have hresponse := pairedRadialDirection_response (fderiv ℝ C u)
      (θ i) σ (d0 i) (d1 i) (A i) (R0 i) (R1 i) (h0 i) (h1 i)
    have hdiff : T i - A i =
        σ⁻¹ • (Real.cos (θ i) • R0 i + Real.sin (θ i) • R1 i) := by
      dsimp only [T, d]
      rw [map_smul, hresponse, smul_add, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
      exact add_sub_cancel_left _ _
    have hraw : ‖Real.cos (θ i) • R0 i + Real.sin (θ i) • R1 i‖ ≤
        4 * (σ * δ / 8) := by
      simpa only [sub_zero] using pairedRadialDirection_four_remainders_norm_le
        (θ i) (R0 i) (0 : X) (R1 i) (0 : X) (by positivity : 0 ≤ σ * δ / 8)
        (hR0 i) (by simpa only [norm_zero] using (by positivity : 0 ≤ σ * δ / 8))
        (hR1 i) (by simpa only [norm_zero] using (by positivity : 0 ≤ σ * δ / 8))
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    calc
      σ⁻¹ * ‖Real.cos (θ i) • R0 i + Real.sin (θ i) • R1 i‖ ≤
          σ⁻¹ * (4 * (σ * δ / 8)) :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hσ.le)
      _ = δ / 2 := by field_simp; ring
      _ < δ := by linarith
  obtain ⟨hdom, hli⟩ := hnear (C u) T hclose herror
  have hφ : DifferentiableAt ℝ chart.equation (C u) :=
    (chart.contDiffOn_equation.contDiffAt
      (chart.isOpen_domain.mem_nhds hdom)).differentiableAt (by simp)
  have hder : fderiv ℝ (chart.equation ∘ C) u =
      (fderiv ℝ chart.equation (C u)).comp (fderiv ℝ C u) :=
    (hφ.hasFDerivAt.comp u hC.hasFDerivAt).fderiv
  let L := fderiv ℝ (chart.equation ∘ C) u
  have hcols : LinearIndependent ℝ (fun i ↦ L (d i)) := by
    simpa only [L, hder, ContinuousLinearMap.comp_apply, T] using hli
  let v : Fin q → LinearMap.range L.toLinearMap := fun i ↦ ⟨L (d i), ⟨d i, rfl⟩⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (LinearMap.range L.toLinearMap).subtype hcols
  refine ⟨hdom, ?_⟩
  simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank


theorem exists_supported_paired_incidence_tolerance_uniform
    {ambient locus : Set X} {B : X}
    (chart : SupportedLocusLocalEquations ambient locus B)
    {q : ℕ} (A : Fin q → X)
    (hA : LinearIndependent ℝ (fun i ↦ fderiv ℝ chart.equation B (A i))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P],
      ∀ (C : P → X) (u : P) (σ : ℝ)
      (d0 d1 : Fin q → P) (θ : Fin q → ℝ) (R0 R1 : Fin q → X),
      DifferentiableAt ℝ C u → 0 < σ → ‖C u - B‖ < δ →
      (∀ i, fderiv ℝ C u (d0 i) = (σ * Real.cos (θ i)) • A i + R0 i) →
      (∀ i, fderiv ℝ C u (d1 i) = (σ * Real.sin (θ i)) • A i + R1 i) →
      (∀ i, ‖R0 i‖ ≤ σ * δ / 8) →
      (∀ i, ‖R1 i‖ ≤ σ * δ / 8) →
      C u ∈ chart.domain ∧
        q ≤ finrank ℝ (LinearMap.range (fderiv ℝ (chart.equation ∘ C) u).toLinearMap) := by
  obtain ⟨δ, hδ, hnear⟩ := supported_equation_finite_column_tolerance chart A hA
  refine ⟨δ, hδ, ?_⟩
  intro P _ _
  exact supported_paired_incidence_of_finite_tolerance chart A δ hδ hnear

/-- Fixed-domain specialization of the parameter-space-independent tolerance.
The preceding theorem permits geometric neighborhoods to be selected before
the finite global probe list and its parameter dimension are known. -/
theorem exists_supported_paired_incidence_tolerance
    {ambient locus : Set X} {B : X}
    (chart : SupportedLocusLocalEquations ambient locus B)
    {q : ℕ} (A : Fin q → X)
    (hA : LinearIndependent ℝ (fun i ↦ fderiv ℝ chart.equation B (A i))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (C : P → X) (u : P) (σ : ℝ)
      (d0 d1 : Fin q → P) (θ : Fin q → ℝ) (R0 R1 : Fin q → X),
      DifferentiableAt ℝ C u → 0 < σ → ‖C u - B‖ < δ →
      (∀ i, fderiv ℝ C u (d0 i) = (σ * Real.cos (θ i)) • A i + R0 i) →
      (∀ i, fderiv ℝ C u (d1 i) = (σ * Real.sin (θ i)) • A i + R1 i) →
      (∀ i, ‖R0 i‖ ≤ σ * δ / 8) →
      (∀ i, ‖R1 i‖ ≤ σ * δ / 8) →
      C u ∈ chart.domain ∧
        q ≤ finrank ℝ (LinearMap.range (fderiv ℝ (chart.equation ∘ C) u).toLinearMap) := by
  obtain ⟨δ, hδ, htol⟩ := exists_supported_paired_incidence_tolerance_uniform chart A hA
  exact ⟨δ, hδ, htol P⟩

#print axioms supported_paired_incidence_of_finite_tolerance
#print axioms exists_supported_paired_incidence_tolerance_uniform

#print axioms exists_supported_paired_incidence_tolerance

#print axioms supported_equation_finite_column_tolerance

end GlobalEmbedding.Upgrade
