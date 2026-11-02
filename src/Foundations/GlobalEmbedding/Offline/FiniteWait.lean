import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite waiting for the smooth metric-repair iteration

Source: `literature/parallelizable-stable-plus-one/main.tex`, the finite-wait paragraph
in the proof of `thm:repair` (lines 772–776 in the supplied manuscript), and DAG node
`repair-finite-wait-convergence`.

These results prove the scalar recurrence and common-tail obligations. They do not
construct the geometric one-step update, prove its estimates, or claim the complete
metric-repair theorem. In the paper, `A = B / 4` and the nonnegative coefficients tend
to zero as the geometric scale decreases. No smallness assumption on the initial
value of the higher-order norm is needed. The scalar lemmas even allow negative `x`;
only the nonnegativity of the multiplicative coefficients is used.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Offline

/-- The repair recurrence is bounded on a tail, without any initial smallness condition.

Source: `thm:repair`, finite-wait paragraph; DAG `repair-finite-wait-convergence`.
Choose a tail on which `c ≤ 1/4` and set `M = max (x N) (4*A+1)`. Induction preserves
`x ≤ M` on this tail because the update is monotone in `x` and maps `(-∞, M]` into itself.
This bound is only an intermediate step; it does not by itself prove the sharper
limsup bound `A`, which is the next theorem. -/
theorem finite_wait_eventually_bounded
    {x c : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ n, x (n + 1) ≤ A + c n * (1 + x n)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, x n ≤ M := by
  have hc_small : ∀ᶠ n in atTop, c n ≤ (1 : ℝ) / 4 :=
    hc.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc_small
  let M : ℝ := max (x N) (4 * A + 1)
  have hAM : 4 * A + 1 ≤ M := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  have htail : ∀ k : ℕ, x (N + k) ≤ M := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero] using (le_max_left (x N) (4 * A + 1))
    | succ k ih =>
        have hpos : 0 ≤ 1 + M := by linarith
        calc
          x (N + (k + 1)) ≤ A + c (N + k) * (1 + x (N + k)) := by
            simpa only [Nat.add_assoc] using hstep (N + k)
          _ ≤ A + c (N + k) * (1 + M) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl ih)
              (hc_nonneg (N + k)))
          _ ≤ A + ((1 : ℝ) / 4) * (1 + M) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right (hN (N + k) (by omega)) hpos)
          _ ≤ M := by linarith
  refine ⟨M, hM, eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact htail k

/-- Every fixed higher-order norm eventually lies below `A + η`, for every `η > 0`.

Source: `thm:repair`, finite-wait paragraph; DAG `repair-finite-wait-convergence`.
First obtain the genuine tail bound `M`. Then `c n * (1+M)` tends to zero, so the
recurrence bounds the next term by `A+η` on a further tail. This is the exact scalar
argument behind the paper's `limsup x ≤ B/4`, with `A = B/4`, and does not require
any higher-order entrance smallness. -/
theorem finite_wait_eventually_le
    {x c : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ n, x (n + 1) ≤ A + c n * (1 + x n))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, x n ≤ A + η := by
  obtain ⟨M, _hM, hbounded⟩ :=
    finite_wait_eventually_bounded hA hc_nonneg hc hstep
  have hproduct : Tendsto (fun n ↦ c n * (1 + M)) atTop (𝓝 0) := by
    simpa using hc.mul_const (1 + M)
  have hsmall : ∀ᶠ n in atTop, c n * (1 + M) < η :=
    hproduct.eventually (eventually_lt_nhds hη)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hbounded.and hsmall)
  refine eventually_atTop.2 ⟨N + 1, ?_⟩
  intro n hn
  have hpred : N ≤ n - 1 := by omega
  have hpred_succ : n - 1 + 1 = n := by omega
  calc
    x n ≤ A + c (n - 1) * (1 + x (n - 1)) := by
      simpa only [hpred_succ] using hstep (n - 1)
    _ ≤ A + c (n - 1) * (1 + M) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hN (n - 1) hpred).1) (hc_nonneg (n - 1)))
    _ ≤ A + η := (add_lt_add_of_le_of_lt le_rfl (hN (n - 1) hpred).2).le

/-- The paper's next controlled norm bound is reached after finitely many steps.

Source: `thm:repair`, finite-wait paragraph; DAG `repair-finite-wait-convergence`.
Apply the scalar tail theorem with `A=B/4` and `η=B/8`; the positive reserve leaves
strict room below `B/2`. -/
theorem finite_wait_eventually_lt_half
    {x c : ℕ → ℝ} {B : ℝ}
    (hB : 0 < B)
    (hc_nonneg : ∀ n, 0 ≤ c n)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ n, x (n + 1) ≤ B / 4 + c n * (1 + x n)) :
    ∀ᶠ n in atTop, x n < B / 2 := by
  have h := finite_wait_eventually_le (A := B / 4) (by linarith)
    hc_nonneg hc hstep (η := B / 8) (by linarith)
  filter_upwards [h] with n hn
  linarith

/-- A finite family of recurrence tests has one common finite waiting threshold.

Source: `thm:repair`, finite-wait paragraph; DAG `repair-finite-wait-convergence`.
Each derivative order has its own finite constant and positive tolerance. Intersect
its eventual tail with the other finitely many tails. The statement includes an empty
family and does not add any initial uniform bound on the values `x i 0`. -/
theorem finite_wait_common_tail
    {ι : Type*} [Finite ι]
    (x c : ι → ℕ → ℝ) (A η : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i)
    (hc_nonneg : ∀ i n, 0 ≤ c i n)
    (hc : ∀ i, Tendsto (c i) atTop (𝓝 0))
    (hstep : ∀ i n, x i (n + 1) ≤ A i + c i n * (1 + x i n))
    (hη : ∀ i, 0 < η i) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, x i n ≤ A i + η i := by
  apply eventually_atTop.1
  exact eventually_all.2 fun i ↦
    finite_wait_eventually_le (hA i) (hc_nonneg i) (hc i) (hstep i) (hη i)

/-- Eventual stage tests admit one increasing sequence of finite exit times.

Source: `thm:repair`, finite-wait paragraph; DAG `repair-finite-wait-convergence`.
For each stage, take the finite intersection of all earlier stage-test tails and
apply Mathlib's increasing extraction theorem. The resulting exit times tend to
infinity and every completed test remains valid at every later time. This is an
abstract scheduling consequence of eventual tests; the geometric iteration must
still establish those tests for its actual evolving maps. -/
theorem finite_wait_stage_schedule
    (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ exit : ℕ → ℕ, StrictMono exit ∧ Tendsto exit atTop atTop ∧
      ∀ k n, exit k ≤ n → ∀ j ≤ k, P j n := by
  have hfinite (k : ℕ) : ∀ᶠ n in atTop, ∀ j ≤ k, P j n := by
    have h := (eventually_all_finset (Finset.range (k + 1))).2
      (fun j _hj ↦ hP j)
    filter_upwards [h] with n hn j hj
    exact hn j (Finset.mem_range.2 (by omega))
  have htail (k : ℕ) : ∀ᶠ n in atTop, ∀ m ≥ n, ∀ j ≤ k, P j m := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hfinite k)
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn m hm
    exact hN m (hn.trans hm)
  obtain ⟨exit, hstrict, hexit⟩ := extraction_forall_of_eventually htail
  exact ⟨exit, hstrict, hstrict.tendsto_atTop, hexit⟩

#print axioms finite_wait_eventually_bounded
#print axioms finite_wait_eventually_le
#print axioms finite_wait_eventually_lt_half
#print axioms finite_wait_common_tail
#print axioms finite_wait_stage_schedule

end GlobalEmbedding.Offline
