import GlobalEmbedding.Paper.BalancedGeometrySmooth
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The actual polynomial residual in the free-selector induction

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 474–475.
DAG node: `free-polynomial-residual`. Every column below is an actual native derivative.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The literal symmetrized pairing of actual first columns, namely the linear
metric variation. Source: the first and second cancellations at lines 442, 473. -/
noncomputable def freeMetricCrossTerm {N a : ℕ}
    (F V : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) : Matrix (Fin a) (Fin a) ℝ :=
  fun i j ↦ inner ℝ (balancedDirectionalDerivative F (D i) x)
      (balancedDirectionalDerivative V (D j) x) +
    inner ℝ (balancedDirectionalDerivative V (D i) x)
      (balancedDirectionalDerivative F (D j) x)

/-- The actual map in the source, with one fixed F, Z and W for every real parameter.
Source: line 474, Pε=F₀+εZ+ε²W. -/
noncomputable def freePolynomialFamily {N : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N)) (ε : ℝ) :
    M → EuclideanSpace ℝ (Fin N) := F + ε • Z + ε ^ 2 • W

omit [IsManifold I ∞ M] in
/-- Actual native differentiation commutes with multiplication by a constant.
The manifold scalar product rule has a zero constant derivative. This includes c=0.
Source: differentiating the actual polynomial map at line 474. -/
theorem free_directional_const_smul {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (c : ℝ)
    (D : ∀ x : M, TangentSpace I x) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x) :
    balancedDirectionalDerivative (c • f) D x =
      c • balancedDirectionalDerivative f D x := by
  change mvfderiv I ((fun _ : M ↦ c) • f) x (D x) = c • mvfderiv I f x (D x)
  rw [mvfderiv_smul mdifferentiableAt_const hf]
  simp [mvfderiv_const]

omit [IsManifold I ∞ M] in
/-- The literal polynomial has native smooth slices. The same smooth summands are
used at all parameters, so this assertion does not select a different map at each order.
Source: the actual polynomial in line 474. -/
theorem freePolynomialFamily_contMDiff {N : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W) (ε : ℝ) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (freePolynomialFamily F Z W ε) :=
by
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ ε) := contMDiff_const
  have hc2 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ ε ^ 2) := contMDiff_const
  exact (hF.add (hc.smul hZ)).add (hc2.smul hW)

omit [IsManifold I ∞ M] in
/-- Actual first columns of the polynomial are the literal quadratic polynomial
of first columns. Apply the accepted native sum rule twice and the constant-scalar rule.
Source: differentiating Pε at line 474. -/
theorem freePolynomialFamily_directional {N : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : ∀ x : M, TangentSpace I x) (ε : ℝ) (x : M) :
    balancedDirectionalDerivative (freePolynomialFamily F Z W ε) D x =
      balancedDirectionalDerivative F D x + ε • balancedDirectionalDerivative Z D x +
        ε ^ 2 • balancedDirectionalDerivative W D x := by
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ ε) := contMDiff_const
  have hc2 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ ε ^ 2) := contMDiff_const
  have hZε : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (ε • Z) := hc.smul hZ
  have hWε : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (ε ^ 2 • W) := hc2.smul hW
  unfold freePolynomialFamily
  rw [balanced_directional_add _ _ D x
      ((hF.add hZε).mdifferentiableAt (by norm_num))
      (hWε.mdifferentiableAt (by norm_num)),
    balanced_directional_add _ _ D x (hF.mdifferentiableAt (by norm_num))
      (hZε.mdifferentiableAt (by norm_num)),
    free_directional_const_smul _ _ D x (hZ.mdifferentiableAt (by norm_num)),
    free_directional_const_smul _ _ D x (hW.mdifferentiableAt (by norm_num))]

/-- Exact fourth-degree expansion of the genuine partial Gram, before making
either cancellation assumption. Expand the actual derivative columns and inner products,
then collect real polynomial coefficients. No formal substitute derivative is used.
Source: the polynomial residual calculation at lines 474–475. -/
theorem freePolynomialFamily_geometry {N a : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (ε : ℝ) (x : M) :
    balancedGeometry (freePolynomialFamily F Z W ε)
        (freePolynomialFamily_contMDiff F Z W hF hZ hW ε) D x =
      balancedGeometry F hF D x + ε • freeMetricCrossTerm F Z D x +
        ε ^ 2 • (freeMetricCrossTerm F W D x + balancedGeometry Z hZ D x) +
        ε ^ 3 • freeMetricCrossTerm Z W D x + ε ^ 4 • balancedGeometry W hW D x := by
  ext i j
  change inner ℝ (balancedDirectionalDerivative (freePolynomialFamily F Z W ε) (D i) x)
      (balancedDirectionalDerivative (freePolynomialFamily F Z W ε) (D j) x) = _
  rw [freePolynomialFamily_directional F Z W hF hZ hW (D i),
    freePolynomialFamily_directional F Z W hF hZ hW (D j)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    freeMetricCrossTerm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [balancedGeometry, Matrix.gram_apply, balancedDirectionalDerivative]
  ring

/-- The two actual cancellations give exactly the fixed cubic and quartic residual
required by balanced correction. Substitute the exact constant Gram and the two zero
coefficient identities into the preceding genuine polynomial expansion. In the full
induction the Z and W constructions discharge these identities; this lemma does not
assume that those constructions or the final free selector have already been obtained.
Source: lines 474–475. -/
theorem freePolynomialFamily_residual {N a : ℕ}
    (F Z W : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hZ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ Z)
    (hW : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ W)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hbase : ∀ x, balancedGeometry F hF D x = 1)
    (hlinear : ∀ x, freeMetricCrossTerm F Z D x = 0)
    (hquadratic : ∀ x, freeMetricCrossTerm F W D x + balancedGeometry Z hZ D x = 0) :
    ∀ ε x, balancedGeometry (freePolynomialFamily F Z W ε)
        (freePolynomialFamily_contMDiff F Z W hF hZ hW ε) D x =
      1 + ε ^ 3 • freeMetricCrossTerm Z W D x + ε ^ 4 • balancedGeometry W hW D x := by
  intro ε x
  rw [freePolynomialFamily_geometry F Z W hF hZ hW D ε x,
    hbase x, hlinear x, hquadratic x, smul_zero, smul_zero, add_zero, add_zero]

/-- The cubic coefficient in the actual residual is native smooth, entry by entry.
Apply accepted smoothness of actual directional derivatives, the native inner-product
map, and addition. Source: the fixed smooth coefficients in line 475. -/
theorem freeMetricCrossTerm_entry_contMDiff {N a : ℕ}
    (F V : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (hV : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ V)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (i j : Fin a) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ freeMetricCrossTerm F V D x i j) := by
  apply ContMDiff.add
  · exact (contDiff_inner (𝕜 := ℝ)).contMDiff.comp
      ((balanced_directional_contMDiff F hF (D i)).prodMk_space
        (balanced_directional_contMDiff V hV (D j)))
  · exact (contDiff_inner (𝕜 := ℝ)).contMDiff.comp
      ((balanced_directional_contMDiff V hV (D i)).prodMk_space
        (balanced_directional_contMDiff F hF (D j)))

#print axioms freePolynomialFamily_geometry
#print axioms freePolynomialFamily_residual
#print axioms freeMetricCrossTerm_entry_contMDiff

end GlobalEmbedding.Paper
