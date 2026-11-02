import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The original finite backward reserve bootstrap

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 662–667.
DAG node: `mean-iteration-finite-reserve`. The precomputed decreasing derivative orders
give one positive domain threshold before any later observation order is chosen.
The actual mean operator's local size estimates remain an explicit caller obligation.
-/

namespace GlobalEmbedding.Paper

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The finite backward list of bounds, independent of epsilon and of the operator.
The nonnegative majorant avoids imposing positivity on an unused local estimate. -/
noncomputable def meanReserveBound (p : ℕ → Seminorm ℝ E) (H : E)
    (C : ℕ → ℝ → ℝ) (q loss : ℕ) : ℕ → ℝ
  | 0 => p (q * loss) H
  | i + 1 => p ((q - (i + 1)) * loss) H +
      max 0 (C ((q - (i + 1)) * loss) (meanReserveBound p H C q loss i))

/-- A total finite-recursion step for an operator defined ONLY on the original reserve.
The outside value is never used in the proved iteration and adds no extension hypothesis. -/
noncomputable def meanReserveStep (p : Seminorm ℝ E) (H : E) (rho : ℝ)
    (T : {A : E // p (A - H) < rho} → E) (A : E) : E :=
  if h : p (A - H) < rho then H - T ⟨A, h⟩ else H

/-- All precomputed bounds are finite nonnegative real numbers, including zero dimensions. -/
theorem meanReserveBound_nonneg (p : ℕ → Seminorm ℝ E) (H : E)
    (C : ℕ → ℝ → ℝ) (q loss i : ℕ) : 0 ≤ meanReserveBound p H C q loss i := by
  cases i with
  | zero => exact apply_nonneg _ _
  | succ i => exact add_nonneg (apply_nonneg _ _) (le_max_left _ _)

/-- Faithful finite backward reserve bootstrap on the original local operator domain.

Precompute s_i=(q-i)loss and the displayed L_i, then let M be the finite maximum of
max(0,C_0(L_i)) for i<q. The positive threshold min(1,rho/(2(1+M))) is chosen before T,
epsilon and every later observation order. Induction gives the decreasing-order bound
using s_(i+1)+loss=s_i. Monotonicity also bounds the order-loss norm of A_i, so the order0
estimate retains rho/2 of the original reserve BEFORE the next operator evaluation.
All steps are finite; no Banach contraction, convergence or j-dependent entrance condition
is used. The cases q=1, loss=0 and M=0 use the same proof.
Source: `lem:increments` proof, main.tex662–667; accepted original stage1 proof unchanged. -/
theorem mean_iteration_finite_reserve (p : ℕ → Seminorm ℝ E)
    (hp : ∀ s t, s ≤ t → ∀ A, p s A ≤ p t A) (H : E) (rho : ℝ) (hrho : 0 < rho)
    (C : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
      ∀ T : ℝ → {A : E // p 0 (A - H) < rho} → E,
        (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
          (A : {A : E // p 0 (A - H) < rho}),
          p (s + loss) A.val ≤ R → p s (T epsilon A) ≤ epsilon * C s R) →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
          let A := fun i : ℕ ↦ (meanReserveStep (p 0) H rho (T epsilon))^[i] H
          (∀ i ≤ q, p 0 (A i - H) ≤ rho / 2 ∧
            p ((q - i) * loss) (A i) ≤ meanReserveBound p H C q loss i) ∧
          ∀ i < q, ∃ hi : p 0 (A i - H) < rho,
            A (i + 1) = H - T epsilon ⟨A i, hi⟩ := by
  classical
  let L := meanReserveBound p H C q loss
  have hne : (Finset.range q).Nonempty := ⟨0, by simp; omega⟩
  let M : ℝ := max 0 ((Finset.range q).sup' hne (fun i ↦ max 0 (C 0 (L i))))
  have hM : 0 ≤ M := le_max_left _ _
  have hCi (i : ℕ) (hi : i < q) : max 0 (C 0 (L i)) ≤ M :=
    (Finset.le_sup' (f := fun i ↦ max 0 (C 0 (L i)))
      (Finset.mem_range.mpr hi)).trans (le_max_right _ _)
  let epsilon0 := min 1 (rho / (2 * (1 + M)))
  have he0 : 0 < epsilon0 := lt_min zero_lt_one (div_pos hrho (by positivity))
  refine ⟨epsilon0, he0, min_le_left _ _, ?_⟩
  intro T hT epsilon he he0lt
  have he1 : epsilon ≤ 1 := he0lt.le.trans (min_le_left _ _)
  have hefrac : epsilon ≤ rho / (2 * (1 + M)) :=
    he0lt.le.trans (min_le_right _ _)
  have herho : epsilon * M ≤ rho / 2 := by
    have hmul := (le_div_iff₀ (show 0 < 2 * (1 + M) by positivity)).mp hefrac
    nlinarith
  let A := fun i : ℕ ↦ (meanReserveStep (p 0) H rho (T epsilon))^[i] H
  have hb : ∀ i ≤ q, p 0 (A i - H) ≤ rho / 2 ∧
      p ((q - i) * loss) (A i) ≤ L i := by
    intro i
    induction i with
    | zero =>
      intro hi
      constructor
      · simp only [A, Function.iterate_zero_apply, sub_self, map_zero]
        positivity
      · simp [A, L, meanReserveBound]
    | succ i ih =>
      intro his
      have hi : i < q := by omega
      obtain ⟨hres, hhigh⟩ := ih (by omega)
      have hdom : p 0 (A i - H) < rho := lt_of_le_of_lt hres (by linarith)
      have hstep : A (i + 1) = H - T epsilon ⟨A i, hdom⟩ := by
        change (meanReserveStep (p 0) H rho (T epsilon))^[i + 1] H = _
        rw [Function.iterate_succ_apply']
        change meanReserveStep (p 0) H rho (T epsilon) (A i) = _
        simp only [meanReserveStep, dite_eq_left hdom]
      have horder : (q - (i + 1)) * loss + loss = (q - i) * loss := by
        have hh : q - i = q - (i + 1) + 1 := by omega
        rw [hh, Nat.add_mul, one_mul]
      have hloss : loss ≤ (q - i) * loss := by
        have hh : 1 ≤ q - i := by omega
        nlinarith
      have hzero := hT epsilon he he1 0 (L i) ⟨A i, hdom⟩
        (by simpa only [zero_add] using (hp loss ((q - i) * loss) hloss (A i)).trans hhigh)
      have hnext := hT epsilon he he1 ((q - (i + 1)) * loss) (L i) ⟨A i, hdom⟩
        (by simpa only [horder] using hhigh)
      constructor
      · rw [hstep]
        have hval : p 0 (H - T epsilon ⟨A i, hdom⟩ - H) =
            p 0 (T epsilon ⟨A i, hdom⟩) := by
          rw [sub_sub_cancel_left, map_neg_eq_map]
        rw [hval]
        calc
          _ ≤ epsilon * C 0 (L i) := hzero
          _ ≤ epsilon * max 0 (C 0 (L i)) := by gcongr; exact le_max_right _ _
          _ ≤ epsilon * M := by gcongr; exact hCi i hi
          _ ≤ rho / 2 := herho
      · rw [hstep]
        calc
          _ ≤ p ((q - (i + 1)) * loss) H +
              p ((q - (i + 1)) * loss) (T epsilon ⟨A i, hdom⟩) :=
            map_sub_le_add _ _ _
          _ ≤ p ((q - (i + 1)) * loss) H +
              epsilon * C ((q - (i + 1)) * loss) (L i) := by gcongr
          _ ≤ p ((q - (i + 1)) * loss) H +
              max 0 (C ((q - (i + 1)) * loss) (L i)) := by
            have hmajor := le_max_right 0 (C ((q - (i + 1)) * loss) (L i))
            have hpos := le_max_left 0 (C ((q - (i + 1)) * loss) (L i))
            nlinarith
          _ = L (i + 1) := rfl
  refine ⟨hb, ?_⟩
  intro i hi
  have hdom : p 0 (A i - H) < rho := lt_of_le_of_lt (hb i hi.le).1 (by linarith)
  refine ⟨hdom, ?_⟩
  change (meanReserveStep (p 0) H rho (T epsilon))^[i + 1] H = _
  rw [Function.iterate_succ_apply']
  change meanReserveStep (p 0) H rho (T epsilon) (A i) = _
  simp only [meanReserveStep, dite_eq_left hdom]
  rfl

#print axioms meanReserveBound
#print axioms meanReserveStep
#print axioms meanReserveBound_nonneg
#print axioms mean_iteration_finite_reserve

end GlobalEmbedding.Paper
