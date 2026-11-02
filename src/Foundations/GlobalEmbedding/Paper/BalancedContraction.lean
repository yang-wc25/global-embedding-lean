import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Uniform quadratic contraction

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:balanced`,
proof, lines 403–410; DAG node `balanced-contraction`.
-/

namespace GlobalEmbedding.Paper

/-- A uniformly bounded family of quadratic maps with forcing of size `O(|t|)` has a unique
fixed point in one sufficiently small closed ball, with size `O(|t|)` uniformly in `t`.

Proof: The hypothesis at `t = 1` implies `0 ≤ K`. Choose `M ≥ 1` uniformly bounding `‖A t (B x y)‖` by `M ‖x‖ ‖y‖`, and set
`r = 1 / (4M)`. Choose `δ > 0` so that `K δ ≤ r / 2` (if `K = 0`, choose any positive
`δ`). The map sends the ball of radius `r` into itself, since its norm there is at most
`r / 2 + M r² = 3r / 4`. Bilinearity yields
`B x x - B y y = B (x - y) x + B y (x - y)`, so the map has Lipschitz constant at most
`2Mr = 1 / 2` on the ball. The ball is nonempty and complete: apply the contraction theorem;
uniqueness in the ball follows from the same estimate. For the fixed point `x`,
`‖x‖ ≤ K |t| + M ‖x‖² ≤ K |t| + ‖x‖ / 4`, hence
`‖x‖ ≤ (4K / 3) |t|`. A strictly positive constant can be chosen larger than `4K / 3`.
Source: Lemma `lem:balanced`, proof, lines 403–410. -/
theorem uniform_quadratic_contraction
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (B : X →L[ℝ] X →L[ℝ] Y) (A : ℝ → Y →L[ℝ] X) (f : ℝ → X)
    (K : ℝ) (hA : ∃ L : ℝ, ∀ t, ‖A t‖ ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ K * |t|) :
    ∃ r δ C : ℝ, 0 < r ∧ 0 < δ ∧ 0 < C ∧
      ∀ t : ℝ, |t| < δ → ∃ x : X,
        ‖x‖ ≤ r ∧ x = f t + A t (B x x) ∧ ‖x‖ ≤ C * |t| ∧
          ∀ y : X, ‖y‖ ≤ r → y = f t + A t (B y y) → y = x := by
  classical
  obtain ⟨L, hL⟩ := hA
  have hK : 0 ≤ K := by
    have h := (norm_nonneg (f 1)).trans (hf 1)
    simpa using h
  let M := (|L| + 1) * ‖B‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMbound : (|L| + 1) * ‖B‖ ≤ M := by dsimp [M]; linarith
  have hquad (t : ℝ) (x y : X) : ‖A t (B x y)‖ ≤ M * ‖x‖ * ‖y‖ := by
    calc
      ‖A t (B x y)‖ ≤ ‖A t‖ * ‖B x y‖ := (A t).le_opNorm _
      _ ≤ (|L| + 1) * (‖B‖ * ‖x‖ * ‖y‖) := by
        gcongr
        · exact (hL t).trans ((le_abs_self L).trans (le_add_of_nonneg_right (by norm_num)))
        · exact B.le_opNorm₂ x y
      _ ≤ M * ‖x‖ * ‖y‖ := by
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hMbound (norm_nonneg x)) (norm_nonneg y)]
  let r := 1 / (4 * M)
  have hr : 0 < r := by dsimp [r]; positivity
  have hMr : M * r = 1 / 4 := by dsimp [r]; field_simp
  let δ := r / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 2 * (K + 1) * δ = r := by
    dsimp [δ]
    field_simp
  have hKδ : K * δ ≤ r / 2 := by nlinarith
  let F := fun (t : ℝ) (x : X) ↦ f t + A t (B x x)
  have hdiag (x y : X) : B x x - B y y = B (x - y) x + B y (x - y) := by
    simp only [map_sub, sub_apply]
    abel
  have hdiff (t : ℝ) (x y : X) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
      ‖F t x - F t y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have heq : F t x - F t y = A t (B (x - y) x) + A t (B y (x - y)) := by
      dsimp [F]
      rw [add_sub_add_left_eq_sub, ← map_sub, hdiag, map_add]
    rw [heq]
    calc
      ‖A t (B (x - y) x) + A t (B y (x - y))‖ ≤
          ‖A t (B (x - y) x)‖ + ‖A t (B y (x - y))‖ := norm_add_le _ _
      _ ≤ M * ‖x - y‖ * ‖x‖ + M * ‖y‖ * ‖x - y‖ :=
        add_le_add (hquad t (x - y) x) (hquad t y (x - y))
      _ ≤ M * ‖x - y‖ * r + M * r * ‖x - y‖ := by gcongr
      _ = (M * r + M * r) * ‖x - y‖ := by ring
      _ = (1 / 2 : ℝ) * ‖x - y‖ := by rw [hMr]; ring
  refine ⟨r, δ, 2 * K + 1, hr, hδ, by positivity, ?_⟩
  intro t ht
  have hft : ‖f t‖ ≤ r / 2 :=
    (hf t).trans ((mul_le_mul_of_nonneg_left ht.le hK).trans hKδ)
  let s := Metric.closedBall (0 : X) r
  have hnorm {x : X} (hx : x ∈ s) : ‖x‖ ≤ r := by
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using hx
  have hmaps : Set.MapsTo (F t) s s := by
    intro x hx
    have hxr := hnorm hx
    have hMx : M * ‖x‖ ≤ 1 / 4 := by nlinarith
    have hqx : ‖A t (B x x)‖ ≤ ‖x‖ / 4 := by
      have h := mul_le_mul_of_nonneg_right hMx (norm_nonneg x)
      exact (hquad t x x).trans (by nlinarith)
    have hFx : ‖F t x‖ ≤ r := by
      calc
        ‖F t x‖ ≤ ‖f t‖ + ‖A t (B x x)‖ := norm_add_le _ _
        _ ≤ r / 2 + ‖x‖ / 4 := add_le_add hft hqx
        _ ≤ r := by linarith
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using hFx
  have hcontract : ContractingWith (1 / 2 : NNReal) (hmaps.restrict (F t) s s) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (F t x.val) (F t y.val) ≤ ((1 / 2 : NNReal) : ℝ) * dist x.val y.val
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    simpa only [dist_eq_norm] using hdiff t x.val y.val (hnorm x.property) (hnorm y.property)
  have hzero : (0 : X) ∈ s := by
    simpa only [s, Metric.mem_closedBall, dist_self] using hr.le
  obtain ⟨x, hxs, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hcontract hzero (edist_ne_top _ _)
  have hxr := hnorm hxs
  have hxeq : x = f t + A t (B x x) := hfix.symm
  have hMx : M * ‖x‖ ≤ 1 / 4 := by nlinarith
  have hqx : ‖A t (B x x)‖ ≤ ‖x‖ / 4 := by
    have h := mul_le_mul_of_nonneg_right hMx (norm_nonneg x)
    exact (hquad t x x).trans (by nlinarith)
  have hsize : ‖x‖ ≤ (2 * K + 1) * |t| := by
    have hxest : ‖x‖ ≤ K * |t| + ‖x‖ / 4 := by
      calc
        ‖x‖ = ‖f t + A t (B x x)‖ := congrArg norm hxeq
        _ ≤ ‖f t‖ + ‖A t (B x x)‖ := norm_add_le _ _
        _ ≤ K * |t| + ‖x‖ / 4 := add_le_add (hf t) hqx
    nlinarith [mul_nonneg hK (abs_nonneg t), abs_nonneg t]
  refine ⟨x, hxr, hxeq, hsize, ?_⟩
  intro y hyr hyeq
  have hd := hdiff t y x hyr hxr
  have hfy : F t y = y := hyeq.symm
  have hfx : F t x = x := hxeq.symm
  rw [hfy, hfx] at hd
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

#print axioms uniform_quadratic_contraction

end GlobalEmbedding.Paper
