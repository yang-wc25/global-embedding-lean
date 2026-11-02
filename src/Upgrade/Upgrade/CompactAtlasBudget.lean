import GlobalEmbedding.Offline.CoordinateStageSeries

/-!
# Finite upgrade displacements in the original atlas C² norm

Each stage is one global map and every chart function is its literal pullback.
The proof telescopes these maps and reuses the previously checked finite-sum
estimate for `paperCoordinateCj`.  No replacement norm, chart-count factor, or
unguarded `toReal` is used.  This is the finite-operation budget at the end of
the proof of `thm:upgrade`, not a reconstruction of increments or repair.
-/

open Set GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal

namespace GlobalEmbedding.Upgrade

/-- Every prefix of a finite sequence of global perturbations obeys the sum
of its actual original coordinate budgets.  Smoothness is only required for
the finitely many maps which occur. -/
theorem finite_global_perturbations_paperAtlas_budget
    {M ι : Type*} [Fintype ι] {n q : ℕ}
    (a m : ℕ) (F : ℕ → M → Fin q → ℝ)
    (chart : ι → (Fin n → ℝ) → M) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hF : ∀ k ≤ m, ∀ i, ContDiffOn ℝ ∞ (F k ∘ chart i) (O i))
    (b : ℕ → ℝ) (hb : ∀ k < m, 0 ≤ b k)
    (hstep : ∀ k < m,
      paperAtlasCj a (fun i ↦ (F (k + 1) ∘ chart i) - (F k ∘ chart i)) O S ≤
        ENNReal.ofReal (b k)) :
    ∀ k ≤ m,
      paperAtlasCj a (fun i ↦ (F k ∘ chart i) - (F 0 ∘ chart i)) O S ≤
        ENNReal.ofReal (∑ j ∈ Finset.range k, b j) := by
  intro k hk
  apply iSup_le
  intro i
  have hlocal := paperCoordinateCj_sum_le a (hO i) (hSO i)
    (Finset.range k) (fun j ↦ (F (j + 1) ∘ chart i) - (F j ∘ chart i))
    (fun j hj ↦ (hF (j + 1) (by have := Finset.mem_range.mp hj; omega) i).sub
      (hF j (by have := Finset.mem_range.mp hj; omega) i))
    b (fun j hj ↦ hb j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk))
    (fun j hj ↦ (le_iSup
      (fun i ↦ paperCoordinateCj a
        ((F (j + 1) ∘ chart i) - (F j ∘ chart i)) (O i) (S i)) i).trans
      (hstep j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)))
  have htel : (fun x ↦ ∑ j ∈ Finset.range k,
      ((F (j + 1) ∘ chart i) - (F j ∘ chart i)) x) =
      (F k ∘ chart i) - (F 0 ∘ chart i) := by
    funext x
    exact Finset.sum_range_sub (fun j ↦ F j (chart i x)) k
  rwa [htel] at hlocal

/-- The same original C² norm is finite and strictly below the prescribed
budget at every intermediate stage.  This is useful for keeping every stage
inside the *initial* phase and diagonal-separation neighborhoods. -/
theorem finite_global_perturbations_paperAtlas_C2_lt
    {M ι : Type*} [Fintype ι] {n q : ℕ}
    (m : ℕ) (F : ℕ → M → Fin q → ℝ)
    (chart : ι → (Fin n → ℝ) → M) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hF : ∀ k ≤ m, ∀ i, ContDiffOn ℝ ∞ (F k ∘ chart i) (O i))
    (b : ℕ → ℝ) (hb : ∀ k < m, 0 ≤ b k)
    (hstep : ∀ k < m,
      paperAtlasCj 2 (fun i ↦ (F (k + 1) ∘ chart i) - (F k ∘ chart i)) O S ≤
        ENNReal.ofReal (b k))
    {ε : ℝ} (hε : 0 < ε) (hsum : ∑ j ∈ Finset.range m, b j < ε) :
    ∀ k ≤ m,
      let c := paperAtlasCj 2 (fun i ↦ (F k ∘ chart i) - (F 0 ∘ chart i)) O S
      c ≠ ⊤ ∧ c.toReal < ε := by
  intro k hk
  have hbnd := finite_global_perturbations_paperAtlas_budget 2 m F chart O S
    hO hSO hF b hb hstep k hk
  have hsumle : ∑ j ∈ Finset.range k, b j ≤ ∑ j ∈ Finset.range m, b j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun j hj _ ↦ hb j (Finset.mem_range.mp hj))
  have hstrict := hbnd.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (hsumle.trans_lt hsum))
  have hfinite := ne_of_lt (hstrict.trans (ENNReal.ofReal_lt_top))
  refine ⟨hfinite, ?_⟩
  exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hstrict |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

end GlobalEmbedding.Upgrade
