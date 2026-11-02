import GlobalEmbedding.Paper.BalancedPairingLiftPullback

/-!
# Actual native metric correction from quadratic data only on a local lift

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 413–418.
DAG node: `balanced-lift-metric-algebra`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The source's local fiber computation gives the actual native identity Gram.

Quadratic values q live only on the genuine lift domain F; no q on the whole manifold,
no global chart extension and no formal commuting generator are needed. Differentiate
the first pairing equations only along actual constant lift directions, using the genuine
normed inner-product rule. The accepted actual first-lift identity turns each resulting
derivative into the original native directional derivative. Actual second commutation
follows from the proved local lift Schwarz theorem. Symmetry of the original Gram gives
h symmetry, so once-indexed second pairings suffice. The actual quadratic identity cancels
all cross terms in the original native derivative Gram, yielding Id at the source point.
Q is still nonlocal: the input q may be its whole-function output evaluated on the lift. -/
theorem balanced_metric_eq_one_of_lift_pairings
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F] {N a : ℕ}
    (P U : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (hU : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ U)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (π : F → M) (s : Set F) (hs : IsOpen s)
    (hπ : ContMDiffOn 𝓘(ℝ, F) I ∞ π s) (x : F) (hx : x ∈ s) (u : Fin a → F)
    (hD : ∀ y ∈ s, ∀ i, D i (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u i)))
    (q : Fin a → F → ℝ) (r h : Matrix (Fin a) (Fin a) ℝ)
    (herror : balancedGeometry P hP D (π x) = 1 + h)
    (hfirst : ∀ i,
      (fun y ↦ inner ℝ (balancedDirectionalDerivative P (D i) (π y)) (U (π y)))
        =ᶠ[nhds x] -(q i))
    (hsecond : ∀ i j, i ≤ j →
      2 * inner ℝ (balancedDirectionalDerivative
        (balancedDirectionalDerivative P (D j)) (D i) (π x)) (U (π x)) = h i j + r i j)
    (hrsymmetric : ∀ i j, r i j = r j i)
    (hquadratic : ∀ i j,
      inner ℝ (balancedDirectionalDerivative U (D i) (π x))
          (balancedDirectionalDerivative U (D j) (π x)) =
        fderiv ℝ (q j) x (u i) + fderiv ℝ (q i) x (u j) + r i j) :
    balancedGeometry (P + U) (hP.add hU) D (π x) = 1 := by
  have hπat : MDifferentiableAt 𝓘(ℝ, F) I π x :=
    ((hπ x hx).contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt (by norm_num)
  have hDP (i : Fin a) : DifferentiableAt ℝ
      (fun y ↦ balancedDirectionalDerivative P (D i) (π y)) x :=
    (((balanced_directional_contMDiff P hP (D i)).mdifferentiableAt
      (by norm_num)).comp x hπat).differentiableAt
  have hUlift : DifferentiableAt ℝ (U ∘ π) x :=
    ((hU.mdifferentiableAt (by norm_num)).comp x hπat).differentiableAt
  have hDU (i : Fin a) : fderiv ℝ (U ∘ π) x (u i) =
      balancedDirectionalDerivative U (D i) (π x) :=
    (balanced_directional_lift_pullback_at U (D i) π x (u i)
      (hU.mdifferentiableAt (by norm_num)) hπat (hD x hx i)).symm
  have hD2P (i j : Fin a) :
      fderiv ℝ (fun y ↦ balancedDirectionalDerivative P (D j) (π y)) x (u i) =
        balancedDirectionalDerivative (balancedDirectionalDerivative P (D j))
          (D i) (π x) :=
    (balanced_directional_lift_pullback_at (balancedDirectionalDerivative P (D j))
      (D i) π x (u i)
      ((balanced_directional_contMDiff P hP (D j)).mdifferentiableAt (by norm_num))
      hπat (hD x hx i)).symm
  have hcomm (i j : Fin a) := balanced_directional_commute_of_lift P hP (D i) (D j)
    π s hs hπ x hx (u i) (u j) (fun y hy ↦ hD y hy i) (fun y hy ↦ hD y hy j)
  have hhsymmetric (i j : Fin a) : h i j = h j i := by
    have hg : balancedGeometry P hP D (π x) i j =
        balancedGeometry P hP D (π x) j i := by
      change inner ℝ (balancedDirectionalDerivative P (D i) (π x))
          (balancedDirectionalDerivative P (D j) (π x)) =
        inner ℝ (balancedDirectionalDerivative P (D j) (π x))
          (balancedDirectionalDerivative P (D i) (π x))
      exact real_inner_comm _ _
    rw [herror] at hg
    have hid : (1 : Matrix (Fin a) (Fin a) ℝ) i j =
        (1 : Matrix (Fin a) (Fin a) ℝ) j i := by simp only [Matrix.one_apply, eq_comm]
    change (1 : Matrix (Fin a) (Fin a) ℝ) i j + h i j =
      (1 : Matrix (Fin a) (Fin a) ℝ) j i + h j i at hg
    linarith
  have hsecondAll (i j : Fin a) :
      2 * inner ℝ (balancedDirectionalDerivative
        (balancedDirectionalDerivative P (D j)) (D i) (π x)) (U (π x)) = h i j + r i j := by
    obtain hij | hji := le_total i j
    · exact hsecond i j hij
    · rw [hcomm i j, hhsymmetric i j, hrsymmetric i j]
      exact hsecond j i hji
  ext i j
  have hi := fderiv_inner_apply ℝ (hDP j) hUlift (u i)
  have hj := fderiv_inner_apply ℝ (hDP i) hUlift (u j)
  simp only [Function.comp_apply] at hi hj
  have hpj := congrArg (fun L : F →L[ℝ] ℝ ↦ L (u i))
    ((hfirst j).fderiv_eq (𝕜 := ℝ))
  have hpi := congrArg (fun L : F →L[ℝ] ℝ ↦ L (u j))
    ((hfirst i).fderiv_eq (𝕜 := ℝ))
  rw [fderiv_neg] at hpj hpi
  change fderiv ℝ (fun y ↦ inner ℝ (balancedDirectionalDerivative P (D j) (π y))
    (U (π y))) x (u i) = -fderiv ℝ (q j) x (u i) at hpj
  change fderiv ℝ (fun y ↦ inner ℝ (balancedDirectionalDerivative P (D i) (π y))
    (U (π y))) x (u j) = -fderiv ℝ (q i) x (u j) at hpi
  rw [hpj, hDU i, hD2P i j] at hi
  rw [hpi, hDU j, hD2P j i, ← hcomm i j] at hj
  have hq := hquadratic i j
  have hsec := hsecondAll i j
  have herr := congrArg (fun A : Matrix (Fin a) (Fin a) ℝ ↦ A i j) herror
  change inner ℝ (balancedDirectionalDerivative P (D i) (π x))
    (balancedDirectionalDerivative P (D j) (π x)) =
      (1 : Matrix (Fin a) (Fin a) ℝ) i j + h i j at herr
  change inner ℝ (balancedDirectionalDerivative (P + U) (D i) (π x))
      (balancedDirectionalDerivative (P + U) (D j) (π x)) =
    (1 : Matrix (Fin a) (Fin a) ℝ) i j
  rw [balanced_directional_add P U (D i) (π x)
      (hP.mdifferentiableAt (by norm_num)) (hU.mdifferentiableAt (by norm_num)),
    balanced_directional_add P U (D j) (π x)
      (hP.mdifferentiableAt (by norm_num)) (hU.mdifferentiableAt (by norm_num))]
  simp only [inner_add_left, inner_add_right]
  have hsym : inner ℝ (balancedDirectionalDerivative U (D i) (π x))
      (balancedDirectionalDerivative P (D j) (π x)) =
      inner ℝ (balancedDirectionalDerivative P (D j) (π x))
        (balancedDirectionalDerivative U (D i) (π x)) := real_inner_comm _ _
  linarith

end GlobalEmbedding.Paper
