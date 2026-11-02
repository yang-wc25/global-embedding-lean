import GlobalEmbedding.Paper.BalancedContraction
import GlobalEmbedding.Paper.BoundedContinuousBilinearLiftSpec
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Actual common contraction ball and interval over arbitrary auxiliary parameters

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `balanced-uniform-family-contraction`.
-/

open scoped BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- All auxiliary parameters share an actual contraction ball, interval and linear size bound.

Use the discrete topology only internally to put all uniformly bounded parameter families
in Mathlib's actual bounded-continuous-function Banach spaces. Lift the original bilinear
map and actual operator evaluation pointwise; the given original uniform bounds give the
actual lifted operator and forcing bounds. Apply the already proved uniform contraction
theorem once in these genuine Banach spaces. Evaluation gives every original fixed equation
and the same radius/interval/size bounds. For individual uniqueness, replace one component by
the competing fixed point. This actual bounded family solves the lifted equation; lifted
uniqueness makes it the original family. The exported statement imposes no parameter topology
or continuity. Source: the common small interval over parameters in `lem:balanced`. -/
theorem uniform_quadratic_family_contraction
    {P X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (B : X →L[ℝ] X →L[ℝ] Y) (A : P → ℝ → Y →L[ℝ] X) (f : P → ℝ → X)
    (K : ℝ) (hA : ∃ L : ℝ, ∀ p t, ‖A p t‖ ≤ L)
    (hf : ∀ p t, ‖f p t‖ ≤ K * |t|) :
    ∃ r δ C : ℝ, 0 < r ∧ 0 < δ ∧ 0 < C ∧
      ∀ t : ℝ, |t| < δ → ∃ v : P → X,
        (∀ p, ‖v p‖ ≤ r ∧ v p = f p t + A p t (B (v p) (v p)) ∧ ‖v p‖ ≤ C * |t|) ∧
        ∀ p (y : X), ‖y‖ ≤ r → y = f p t + A p t (B y y) → y = v p := by
  classical
  let : TopologicalSpace P := ⊥
  have : DiscreteTopology P := ⟨rfl⟩
  obtain ⟨L, hL⟩ := hA
  have hAb (p : P) (t : ℝ) : ‖A p t‖ ≤ |L| + 1 :=
    (hL p t).trans ((le_abs_self L).trans (le_add_of_nonneg_right (by norm_num)))
  let Kpos := max K 0
  have hKpos : 0 ≤ Kpos := le_max_right _ _
  have hfb (p : P) (t : ℝ) : ‖f p t‖ ≤ Kpos * |t| :=
    (hf p t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t))
  let af : ℝ → P →ᵇ (Y →L[ℝ] X) := fun t ↦
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun p ↦ A p t) (|L| + 1)
      (fun p ↦ hAb p t)
  let ff : ℝ → P →ᵇ X := fun t ↦
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun p ↦ f p t) (Kpos * |t|)
      (fun p ↦ hfb p t)
  have haf (t : ℝ) : ‖af t‖ ≤ |L| + 1 :=
    (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun p ↦ hAb p t)
  have hff (t : ℝ) : ‖ff t‖ ≤ Kpos * |t| :=
    (BoundedContinuousFunction.norm_le (mul_nonneg hKpos (abs_nonneg t))).mpr (fun p ↦ hfb p t)
  let ev : (Y →L[ℝ] X) →L[ℝ] Y →L[ℝ] X := (ContinuousLinearMap.apply ℝ X).flip
  let eval := boundedContinuousBilinearLift (P := P) ev
  let bb := boundedContinuousBilinearLift (P := P) B
  let aa : ℝ → (P →ᵇ Y) →L[ℝ] (P →ᵇ X) := fun t ↦ eval (af t)
  have haa (t : ℝ) : ‖aa t‖ ≤ ‖eval‖ * (|L| + 1) :=
    (eval.le_opNorm (af t)).trans
      (mul_le_mul_of_nonneg_left (haf t) (norm_nonneg eval))
  obtain ⟨r, δ, C, hr, hδ, hC, hsol⟩ := uniform_quadratic_contraction bb aa ff Kpos
    ⟨‖eval‖ * (|L| + 1), haa⟩ hff
  refine ⟨r, δ, C, hr, hδ, hC, ?_⟩
  intro t ht
  obtain ⟨V, hVr, hVeq, hVsize, hVunique⟩ := hsol t ht
  have hpoint (p : P) : ‖V p‖ ≤ r ∧
      V p = f p t + A p t (B (V p) (V p)) ∧ ‖V p‖ ≤ C * |t| := by
    refine ⟨(V.norm_coe_le_norm p).trans hVr, ?_, (V.norm_coe_le_norm p).trans hVsize⟩
    have h := congrArg (fun F : P →ᵇ X ↦ F p) hVeq
    exact h
  refine ⟨fun p ↦ V p, hpoint, ?_⟩
  intro p y hyr hyeq
  let W : P →ᵇ X := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun q ↦ if q = p then y else V q) r (fun q ↦ by
      split
      · exact hyr
      · exact (hpoint q).1)
  have hWr : ‖W‖ ≤ r := (BoundedContinuousFunction.norm_le hr.le).mpr (fun q ↦ by
    change ‖if q = p then y else V q‖ ≤ r
    split
    · exact hyr
    · exact (hpoint q).1)
  have hWeq : W = ff t + aa t (bb W W) := by
    apply BoundedContinuousFunction.ext
    intro q
    change W q = f q t + A q t (B (W q) (W q))
    by_cases hqp : q = p
    · subst q
      have hWp : W p = y := by simp [W]
      rw [hWp]
      exact hyeq
    · have hWq : W q = V q := by simp [W, hqp]
      rw [hWq]
      exact (hpoint q).2.1
  have hWV : W = V := hVunique W hWr hWeq
  have h := congrArg (fun F : P →ᵇ X ↦ F p) hWV
  simpa [W] using h

#print axioms uniform_quadratic_family_contraction

end GlobalEmbedding.Paper
