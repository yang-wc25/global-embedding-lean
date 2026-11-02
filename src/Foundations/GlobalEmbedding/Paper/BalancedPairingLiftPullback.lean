import GlobalEmbedding.Paper.BalancedPairingMap
import GlobalEmbedding.Paper.BalancedDirectionalCalculus
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Actual first/second pairing on local Euclidean lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 413–418.
DAG node: `balanced-pairing-lift-pullback`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical normed-space tangent identifications turn the actual directional mfderiv
into the actual Fréchet derivative. This is Mathlib's mfderiv_eq_fderiv evaluated at u. -/
theorem balanced_directional_model_apply {N : ℕ}
    (f : F → EuclideanSpace ℝ (Fin N)) (u : F) (x : F) :
    balancedDirectionalDerivative (I := 𝓘(ℝ, F)) f
      (fun y ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm u) x =
        fderiv ℝ f x u := by
  unfold balancedDirectionalDerivative
  rw [mfderiv_eq_fderiv]
  rfl

/-- Actual local pushforward of a direction identifies the native directional derivative
with the true derivative of the lift. This is the same actual manifold chain-rule
identification as the accepted partial-Gram pullback, retaining its vector value. -/
theorem balanced_directional_lift_pullback_at {N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : ∀ y : M, TangentSpace I y) (π : F → M) (x : F) (u : F)
    (hP : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) P (π x))
    (hπ : MDifferentiableAt 𝓘(ℝ, F) I π x)
    (hD : D (π x) = mfderiv 𝓘(ℝ, F) I π x
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm u)) :
    balancedDirectionalDerivative P D (π x) = fderiv ℝ (P ∘ π) x u := by
  unfold balancedDirectionalDerivative
  rw [hD]
  have hc := mfderiv_comp_apply x hP hπ
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm u)
  have h := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (P (π x))) hc
  rw [mfderiv_eq_fderiv] at h
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
  simpa only [NormedSpace.fromTangentSpace] using h.symm

/-- The actual second directional derivative is the genuine iterated derivative of
the local lift. Only local pushforward equalities and smoothness on the original open
set are used. Apply the actual first-derivative chain rule to the smooth native first
derivative, then differentiate its neighborhood equality with the true first lift derivative. -/
theorem balanced_second_directional_lift_pullback_at [IsManifold I ∞ M] {N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (A B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (π : F → M) (s : Set F) (hs : IsOpen s)
    (hπ : ContMDiffOn 𝓘(ℝ, F) I ∞ π s) (x : F) (hx : x ∈ s) (u v : F)
    (hA : ∀ y ∈ s, A (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm u))
    (hB : ∀ y ∈ s, B (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) :
    balancedDirectionalDerivative (balancedDirectionalDerivative P B) A (π x) =
      fderiv ℝ (fun y ↦ fderiv ℝ (P ∘ π) y v) x u := by
  have hπat (y : F) (hy : y ∈ s) : MDifferentiableAt 𝓘(ℝ, F) I π y :=
    ((hπ y hy).contMDiffAt (hs.mem_nhds hy)).mdifferentiableAt (by norm_num)
  rw [balanced_directional_lift_pullback_at (balancedDirectionalDerivative P B) A π x u
    ((balanced_directional_contMDiff P hP B).mdifferentiableAt (by norm_num))
    (hπat x hx) (hA x hx)]
  have heq : (balancedDirectionalDerivative P B ∘ π) =ᶠ[nhds x]
      (fun y ↦ fderiv ℝ (P ∘ π) y v) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact balanced_directional_lift_pullback_at P B π y v
      (hP.mdifferentiableAt (by norm_num)) (hπat y hy) (hB y hy)
  exact congrArg (fun L : F →L[ℝ] EuclideanSpace ℝ (Fin N) ↦ L u)
    (heq.fderiv_eq (𝕜 := ℝ))

/-- Actual directions pushed from constant local lift directions commute on every
smooth P. Use the proved actual second-lift identity twice and Mathlib's genuine C2
Schwarz theorem for the actual local lift. This discharges the metric theorem's second
column commutation without adding formal commuting generators to source bundle data. -/
theorem balanced_directional_commute_of_lift [IsManifold I ∞ M] {N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (A B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (π : F → M) (s : Set F) (hs : IsOpen s)
    (hπ : ContMDiffOn 𝓘(ℝ, F) I ∞ π s) (x : F) (hx : x ∈ s) (u v : F)
    (hA : ∀ y ∈ s, A (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm u))
    (hB : ∀ y ∈ s, B (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) :
    balancedDirectionalDerivative (balancedDirectionalDerivative P B) A (π x) =
      balancedDirectionalDerivative (balancedDirectionalDerivative P A) B (π x) := by
  rw [balanced_second_directional_lift_pullback_at P hP A B π s hs hπ x hx u v hA hB,
    balanced_second_directional_lift_pullback_at P hP B A π s hs hπ x hx v u hB hA]
  have hc : ContDiffAt ℝ ∞ (P ∘ π) x :=
    (hP.contMDiffAt.comp x ((hπ x hx).contMDiffAt (hs.mem_nhds hx))).contDiffAt
  have hdf : DifferentiableAt ℝ (fderiv ℝ (P ∘ π)) x :=
    (hc.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have heval (w : F) : fderiv ℝ (fun y ↦ fderiv ℝ (P ∘ π) y w) x =
      (fderiv ℝ (fderiv ℝ (P ∘ π)) x).flip w := by
    have h := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using h.fderiv
  simp only [heval]
  exact (hc.isSymmSndFDerivAt (by simp)).eq u v

/-- All actual native pairing columns pull back to the genuine local Euclidean-lift
columns, and hence their complete linear pairing operators agree.

The lift is smooth only on the specified open set, as an actual local bundle lift is.
First columns follow from the actual chain rule. For a second column apply it to the
smooth first native derivative; the first-column equality holds on a neighborhood, so
its actual derivatives agree there. Thus no globally smooth extension of a chart inverse,
formal commuting derivation, or unknown second-derivative data is assumed. -/
theorem balanced_pairing_lift_pullback [IsManifold I ∞ M] {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (π : F → M) (s : Set F) (hs : IsOpen s)
    (hπ : ContMDiffOn 𝓘(ℝ, F) I ∞ π s) (x : F) (hx : x ∈ s) (u : Fin a → F)
    (hD : ∀ y ∈ s, ∀ i, D i (π y) = mfderiv 𝓘(ℝ, F) I π y
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u i))) :
    balancedPairingColumns P (fun i ↦ D i) (π x) =
      balancedPairingColumns (I := 𝓘(ℝ, F)) (P ∘ π)
        (fun i y ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u i)) x ∧
    balancedPairingMap P (fun i ↦ D i) (π x) =
      balancedPairingMap (I := 𝓘(ℝ, F)) (P ∘ π)
        (fun i y ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u i)) x := by
  have hπat (y : F) (hy : y ∈ s) : MDifferentiableAt 𝓘(ℝ, F) I π y :=
    ((hπ y hy).contMDiffAt (hs.mem_nhds hy)).mdifferentiableAt (by norm_num)
  have hfirst (i : Fin a) (y : F) (hy : y ∈ s) :
      balancedDirectionalDerivative P (D i) (π y) = fderiv ℝ (P ∘ π) y (u i) :=
    balanced_directional_lift_pullback_at P (D i) π y (u i)
      (hP.mdifferentiableAt (by norm_num)) (hπat y hy) (hD y hy i)
  have hcolumns : balancedPairingColumns P (fun i ↦ D i) (π x) =
      balancedPairingColumns (I := 𝓘(ℝ, F)) (P ∘ π)
        (fun i y ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u i)) x := by
    funext index
    rcases index with i | ij
    · simp only [balancedPairingColumns]
      rw [balanced_directional_model_apply]
      exact hfirst i x hx
    · simp only [balancedPairingColumns]
      rw [balanced_second_directional_lift_pullback_at P hP (D ij.val.1) (D ij.val.2)
        π s hs hπ x hx (u ij.val.1) (u ij.val.2)
        (fun y hy ↦ hD y hy ij.val.1) (fun y hy ↦ hD y hy ij.val.2),
        balanced_directional_model_apply]
      have hmodel : balancedDirectionalDerivative (I := 𝓘(ℝ, F)) (P ∘ π)
          (fun y ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (u ij.val.2)) =
          (fun y ↦ fderiv ℝ (P ∘ π) y (u ij.val.2)) :=
        funext fun y ↦ balanced_directional_model_apply _ _ y
      rw [hmodel]
  refine ⟨hcolumns, ?_⟩
  unfold balancedPairingMap
  rw [hcolumns]

end GlobalEmbedding.Paper
