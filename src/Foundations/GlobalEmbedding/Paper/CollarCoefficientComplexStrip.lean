import GlobalEmbedding.Paper.CollarPeriodicComplexStrip

/-!
# Actual source real coefficient complex strip

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. DAG node: `collar-coefficient-complex-strip`.
-/

open Set Filter Metric
open scoped Topology

namespace GlobalEmbedding.Paper

/-- Actual real finite-dimensional coefficients analytic and periodic inside an open real
base domain extend to one genuine complex base neighborhood times imaginary torus strip.
The extension is genuinely complex analytic, periodic on an invariant complex open domain,
agrees with the actual real data throughout the smaller real base chart, and has uniform
bounds for all joint complex derivatives on the strip.

Source: Proposition `prop:collar`, proof lines 530–534. Embed the actual real value coordinates
by the actual real continuous linear inclusion into complex coordinates. Outside the specified
open real base domain define this real-variable coefficient to be zero. This preserves actual
periodicity everywhere and the genuine real analytic germs at the base orbit. The proved
periodic complex-strip construction builds the actual complex extension and all derivative
bounds. Shrink its positive base radius to lie inside the original real base domain; then every
real point in the smaller chart still has its original coefficient value. All joint derivative
bounds in particular control spatial derivatives through order three on every smaller chart
and strip. No complex extension or derivative bound is assumed. -/
theorem collar_coefficient_complex_strip {b a N : ℕ}
    (f : (Fin (b + a) → ℝ) → (Fin N → ℝ)) (V : Set (Fin b → ℝ))
    (hV : IsOpen V) (p₀ : Fin b → ℝ) (hp₀ : p₀ ∈ V)
    (hf : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      AnalyticAt ℝ f x)
    (hperiod : ∀ x : Fin (b + a) → ℝ, (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V →
      ∀ t : Fin a → ℤ,
        f (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = f x) :
    ∃ (U : Set (Fin (b + a) → ℂ)) (g : (Fin (b + a) → ℂ) → (Fin N → ℂ))
      (ε : ℝ) (M : ℕ → ℝ), 0 < ε ∧ IsOpen U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ (z : Fin (b + a) → ℂ) (t : Fin a → ℤ),
        z + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ)) ∈ U ↔ z ∈ U) ∧
      (∀ z ∈ U, ∀ t : Fin a → ℤ,
        g (z + Fin.append (fun _ : Fin b ↦ (0 : ℂ)) (fun j ↦ (t j : ℂ))) = g z) ∧
      (∀ x : Fin (b + a) → ℝ,
        (∀ i : Fin b, |x (Fin.castAdd a i) - p₀ i| < ε) →
        (fun i : Fin b ↦ x (Fin.castAdd a i)) ∈ V ∧
          g (fun j ↦ (x j : ℂ)) = (fun l ↦ (f x l : ℂ))) ∧
      (∀ j, 0 ≤ M j) ∧
      (∀ z : Fin (b + a) → ℂ,
        (∀ i : Fin b, ‖z (Fin.castAdd a i) - (p₀ i : ℂ)‖ < ε) →
        (∀ j : Fin a, |(z (Fin.natAdd b j)).im| < ε) →
        z ∈ U ∧ ∀ j : ℕ, ‖iteratedFDeriv ℂ j g z‖ ≤ M j) := by
  classical
  let π (x : Fin (b + a) → ℝ) : Fin b → ℝ := fun i ↦ x (Fin.castAdd a i)
  have hπ : Continuous π := by fun_prop
  let C : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) :=
    ContinuousLinearMap.pi (fun l ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj l))
  let F (x : Fin (b + a) → ℝ) : Fin N → ℂ := if π x ∈ V then C (f x) else 0
  have hlocal (x : Fin (b + a) → ℝ) (hx : π x ∈ V) : AnalyticAt ℝ F x := by
    have he : F =ᶠ[𝓝 x] (fun y ↦ C (f y)) := by
      filter_upwards [(hV.preimage hπ).mem_nhds hx] with y hy
      change π y ∈ V at hy
      simp only [F, ite_eq_left hy]
    exact (analyticAt_congr he).mpr ((C.analyticAt (f x)).comp (hf x hx))
  have hFa (y : Fin a → ℝ) : AnalyticAt ℝ F (Fin.append p₀ y) :=
    hlocal _ (by simpa only [π, Fin.append_left] using hp₀)
  have hFp (x : Fin (b + a) → ℝ) (t : Fin a → ℤ) :
      F (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = F x := by
    have he : π (x + Fin.append (fun _ : Fin b ↦ (0 : ℝ)) (fun j ↦ (t j : ℝ))) = π x := by
      ext i
      simp [π]
    by_cases hx : π x ∈ V
    · simp only [F, he, ite_eq_left hx]
      rw [hperiod x hx t]
    · simp only [F, he, ite_eq_right hx]
  obtain ⟨U, g, ε, M, hε, hU, hg, hreal, hinv, hgp, hM, hstrip⟩ :=
    collar_periodic_complex_strip F p₀ hFa hFp
  obtain ⟨η, hη, hηV⟩ := Metric.isOpen_iff.mp hV p₀ hp₀
  let δ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  refine ⟨U, g, δ, M, hδ, hU, hg, hinv, hgp, ?_, hM, ?_⟩
  · intro x hx
    have hxV : π x ∈ V := by
      apply hηV
      rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hη]
      intro i
      exact (hx i).trans_le (min_le_right _ _)
    have hp : ∀ i : Fin b, ‖(x (Fin.castAdd a i) : ℂ) - (p₀ i : ℂ)‖ < ε := by
      intro i
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (hx i).trans_le (min_le_left _ _)
    have him : ∀ j : Fin a, |((x (Fin.natAdd b j) : ℂ)).im| < ε := by
      intro j
      simpa only [Complex.ofReal_im, abs_zero] using hε
    refine ⟨hxV, ?_⟩
    rw [hreal x (hstrip _ hp him).1]
    simp only [F, ite_eq_left hxV]
    rfl
  · intro z hp him
    exact hstrip z (fun i ↦ (hp i).trans_le (min_le_left _ _))
      (fun j ↦ (him j).trans_le (min_le_left _ _))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_coefficient_complex_strip
