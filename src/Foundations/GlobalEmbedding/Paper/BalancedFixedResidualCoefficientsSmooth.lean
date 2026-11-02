import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic.Module

/-!
# Fixed residual coefficients inherit actual smoothness from two actual smooth residuals

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines371–378.
DAG node: `balanced-fixed-residual-coefficients-smooth`.
-/

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual fixed cubic/quartic residual coefficients are smooth without a
separate coefficient regularity hypothesis.

Proof: let H1=epsilon1^(-3)R1 and H2=epsilon2^(-3)R2, so actual residual identities
give H1=S3+epsilon1 S4 and H2=S3+epsilon2 S4. Thus the actual S4 equals
(epsilon2−epsilon1)^(-1)(H2−H1) and actual S3 equals H1−epsilon1 S4. Both actual
expressions are native smooth linear combinations of the original actual smooth
residual slices. No regularity of S3 or S4 is assumed. Source: `lem:balanced`,
fixed epsilon-independent S3,S4 in the source statement, lines371–378. -/
theorem balanced_fixed_residual_coefficients_smooth
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R1 R2 S3 S4 : M → F) (ε1 ε2 : ℝ)
    (hε1 : ε1 ≠ 0) (hε2 : ε2 ≠ 0) (hdiff : ε2 - ε1 ≠ 0)
    (hR1 : ContMDiff I 𝓘(ℝ, F) ∞ R1) (hR2 : ContMDiff I 𝓘(ℝ, F) ∞ R2)
    (h1 : ∀ x, R1 x = ε1 ^ 3 • S3 x + ε1 ^ 4 • S4 x)
    (h2 : ∀ x, R2 x = ε2 ^ 3 • S3 x + ε2 ^ 4 • S4 x) :
    ContMDiff I 𝓘(ℝ, F) ∞ S3 ∧ ContMDiff I 𝓘(ℝ, F) ∞ S4 := by
  let H1 : M → F := fun x ↦ (ε1 ^ 3)⁻¹ • R1 x
  let H2 : M → F := fun x ↦ (ε2 ^ 3)⁻¹ • R2 x
  have hcubic1 : (ε1 ^ 3)⁻¹ * ε1 ^ 3 = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hε1)
  have hcubic2 : (ε2 ^ 3)⁻¹ * ε2 ^ 3 = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hε2)
  have hquartic1 : (ε1 ^ 3)⁻¹ * ε1 ^ 4 = ε1 := by field_simp
  have hquartic2 : (ε2 ^ 3)⁻¹ * ε2 ^ 4 = ε2 := by field_simp
  have hH1 (x : M) : H1 x = S3 x + ε1 • S4 x := by
    simp only [H1, h1, smul_add, smul_smul, hcubic1, hquartic1, one_smul]
  have hH2 (x : M) : H2 x = S3 x + ε2 • S4 x := by
    simp only [H2, h2, smul_add, smul_smul, hcubic2, hquartic2, one_smul]
  have hS4 : S4 = fun x ↦ (ε2 - ε1)⁻¹ • (H2 x - H1 x) := by
    funext x
    have he : H2 x - H1 x = (ε2 - ε1) • S4 x := by rw [hH1, hH2]; module
    rw [he, smul_smul, inv_mul_cancel₀ hdiff, one_smul]
  have hS3 : S3 = fun x ↦ H1 x - ε1 • S4 x := by
    funext x
    rw [hH1]
    module
  have hH1smooth : ContMDiff I 𝓘(ℝ, F) ∞ H1 := (contMDiff_const (c := (ε1 ^ 3)⁻¹)).smul (I := 𝓘(ℝ, ℝ)) hR1
  have hH2smooth : ContMDiff I 𝓘(ℝ, F) ∞ H2 := (contMDiff_const (c := (ε2 ^ 3)⁻¹)).smul (I := 𝓘(ℝ, ℝ)) hR2
  have hS4smooth : ContMDiff I 𝓘(ℝ, F) ∞ S4 := by
    rw [hS4]
    exact (contMDiff_const (c := (ε2 - ε1)⁻¹)).smul (I := 𝓘(ℝ, ℝ)) (hH2smooth.sub hH1smooth)
  refine ⟨?_, hS4smooth⟩
  rw [hS3]
  exact hH1smooth.sub ((contMDiff_const (c := ε1)).smul (I := 𝓘(ℝ, ℝ)) hS4smooth)

#print axioms balanced_fixed_residual_coefficients_smooth

end GlobalEmbedding.Paper
