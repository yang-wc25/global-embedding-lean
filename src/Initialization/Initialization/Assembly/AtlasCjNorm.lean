import GlobalEmbedding.Paper.FiniteCjNorm
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The actual C^j norm over a finite atlas, including an empty source

Chart norms are the existing sum of actual derivative suprema. The atlas norm
is their genuine finite maximum, with an inserted zero for an empty atlas.
No estimate grows with the number of charts.
-/

noncomputable section
open Set

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E V : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def finiteAtlasCjNorm (j : ℕ) (u : ι → E → V) (U : ι → Set E) : ℝ := by
  classical
  exact (insert 0 (Finset.univ.image (fun i ↦ finiteCjNorm j (u i) (U i)))).max'
    (by simp)

theorem finiteAtlasCjNorm_nonneg (j : ℕ) (u : ι → E → V) (U : ι → Set E) :
    0 ≤ finiteAtlasCjNorm j u U := by
  classical
  exact Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

/-- Uniform chart estimates imply the literal maximum estimate, without a
factor depending on atlas cardinality. -/
theorem finiteAtlasCjNorm_le (j : ℕ) (u : ι → E → V) (U : ι → Set E)
    (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, finiteCjNorm j (u i) (U i) ≤ B) :
    finiteAtlasCjNorm j u U ≤ B := by
  classical
  apply Finset.max'_le
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hB
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact h i

/-- A fixed sequence bounding actual jets yields the original finite C^j
supremum norm in each chart. Its supremum boundedness is proved internally. -/
theorem finiteCjNorm_le_sum_of_jet_bounds
    (j : ℕ) (u : E → V) (U : Set E) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k)
    (h : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k u x‖ ≤ B k) :
    finiteCjNorm j u U ≤ ∑ k ∈ Finset.range (j+1), B k := by
  apply Finset.sum_le_sum
  intro k hk
  apply csSup_le (by simp : (insert 0 (Set.range (fun x : U ↦ ‖iteratedFDeriv ℝ k u x‖))).Nonempty)
  intro b hb
  rcases Set.mem_insert_iff.mp hb with rfl | hb
  · exact hB k
  · obtain ⟨x, rfl⟩ := hb
    exact h k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk) x x.property

theorem finiteAtlasCjNorm_le_sum_of_jet_bounds
    (j : ℕ) (u : ι → E → V) (U : ι → Set E) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k)
    (h : ∀ i k, k ≤ j → ∀ x ∈ U i, ‖iteratedFDeriv ℝ k (u i) x‖ ≤ B k) :
    finiteAtlasCjNorm j u U ≤ ∑ k ∈ Finset.range (j+1), B k :=
  finiteAtlasCjNorm_le j u U _ (Finset.sum_nonneg (fun k _ ↦ hB k))
    (fun i ↦ finiteCjNorm_le_sum_of_jet_bounds j (u i) (U i) B hB (h i))

theorem finiteAtlasCjNorm_empty [IsEmpty ι] (j : ℕ) (u : ι → E → V) (U : ι → Set E) :
    finiteAtlasCjNorm j u U = 0 :=
  le_antisymm (finiteAtlasCjNorm_le j u U 0 le_rfl (fun i ↦ isEmptyElim i))
    (finiteAtlasCjNorm_nonneg j u U)

end GlobalEmbedding.Initialization
