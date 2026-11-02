import Smoothing.ParameterRound2CompactPair
import GlobalEmbedding.Offline.RepairDisplacementBudget

/-!
# Original weighted norm algebra for the actual repair initialization

All quantities are the original full-joint coordinate partial norms. Addition,
constant scaling and finite-order domination are proved without replacing the
atlas maximum by a chart sum. Finiteness is checked before toReal is used.
These are the concrete estimates needed for G0=sqrt(1-delta0^2) F0 and
H0=h0+delta0^-2(hstar-h0) at the literal 442/440 derivative orders.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι : Type*} [Fintype ι] {a q : ℕ}

/-- Order monotonicity directly in the unchanged sorted-partial definition. -/
theorem parameterRound2_paperAtlasCj_mono_order {j k : ℕ} (hjk : j ≤ k)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasCj j f O S ≤ paperAtlasCj k f O S := by
  refine iSup_le fun i => iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  exact le_iSup_of_le i (le_iSup_of_le ⟨l.val, l.property.1, l.property.2.trans hjk⟩
    (le_iSup_of_le x (le_iSup_of_le c le_rfl)))

/-- Original atlas addition uses the exact two original atlas norms. -/
theorem parameterRound2_paperAtlasCj_add_le
    (j : ℕ) (f g : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (hfFinite : paperAtlasCj j f O S ≠ ⊤) (hgFinite : paperAtlasCj j g O S ≠ ⊤) :
    paperAtlasCj j (fun i x => f i x + g i x) O S ≤
      paperAtlasCj j f O S + paperAtlasCj j g O S := by
  refine iSup_le fun i => ?_
  have hfi : paperCoordinateCj j (f i) (O i) (S i) ≤
      ENNReal.ofReal (paperAtlasCj j f O S).toReal := by
    rw [ENNReal.ofReal_toReal hfFinite]
    exact le_iSup (fun i => paperCoordinateCj j (f i) (O i) (S i)) i
  have hgi : paperCoordinateCj j (g i) (O i) (S i) ≤
      ENNReal.ofReal (paperAtlasCj j g O S).toReal := by
    rw [ENNReal.ofReal_toReal hgFinite]
    exact le_iSup (fun i => paperCoordinateCj j (g i) (O i) (S i)) i
  have h := paperCoordinateCj_add_le j (hO i) (hSO i) (f i) (g i) (hf i) (hg i)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hfi hgi
  simpa only [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hfFinite, ENNReal.ofReal_toReal hgFinite] using h

/-- Exact absolute scalar control in the original atlas maximum. -/
theorem parameterRound2_paperAtlasCj_smul_le
    (j : ℕ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfFinite : paperAtlasCj j f O S ≠ ⊤) (c : ℝ) :
    paperAtlasCj j (fun i x => c • f i x) O S ≤
      ENNReal.ofReal |c| * paperAtlasCj j f O S := by
  refine iSup_le fun i => ?_
  have hfi : paperCoordinateCj j (f i) (O i) (S i) ≤
      ENNReal.ofReal (paperAtlasCj j f O S).toReal := by
    rw [ENNReal.ofReal_toReal hfFinite]
    exact le_iSup (fun i => paperCoordinateCj j (f i) (O i) (S i)) i
  have h := paperCoordinateCj_smul_le j (hO i) (hSO i) (f i) (hf i) c
    ENNReal.toReal_nonneg hfi
  simpa only [ENNReal.ofReal_mul (abs_nonneg c), ENNReal.ofReal_toReal hfFinite] using h

/-- A true finite top derivative order proves weighted finiteness at every
scale, including t=0. There is no converse use of the toReal totalization. -/
theorem parameterRound2_paperAtlasWeighted_finite_of_topOrder
    (base m : ℕ) (t : ℝ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasCj (m + base) f O S ≠ ⊤) :
    paperAtlasWeighted base m t f O S ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  have hjm : j + base ≤ m + base := by have := Finset.mem_range.mp hj; omega
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ne_top_of_le_ne_top hfinite (parameterRound2_paperAtlasCj_mono_order hjm f O S))

/-- The true weighted norm is controlled by the corresponding finite top
order with the explicit number of derivative levels, never a chart count. -/
theorem parameterRound2_paperAtlasWeighted_le_topOrder
    (base m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasWeighted base m t f O S ≤ (m + 1 : ℝ≥0∞) * paperAtlasCj (m + base) f O S := by
  calc
    paperAtlasWeighted base m t f O S ≤
        ∑ _j ∈ Finset.range (m + 1), paperAtlasCj (m + base) f O S := by
      apply Finset.sum_le_sum
      intro j hj
      have hw : ENNReal.ofReal t ^ j ≤ 1 :=
        pow_le_one₀ (by positivity) (by simpa using ENNReal.ofReal_le_ofReal ht1)
      have hnorm := parameterRound2_paperAtlasCj_mono_order
        (show j + base ≤ m + base by have := Finset.mem_range.mp hj; omega) f O S
      simpa only [one_mul] using mul_le_mul hw hnorm (by positivity) (by positivity)
    _ = _ := by simp [nsmul_eq_mul]

/-- The complete original weighted sum respects addition with no extra factor. -/
theorem parameterRound2_paperAtlasWeighted_add_le
    (base m : ℕ) (t : ℝ) (f g : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (hfFinite : paperAtlasCj (m + base) f O S ≠ ⊤)
    (hgFinite : paperAtlasCj (m + base) g O S ≠ ⊤) :
    paperAtlasWeighted base m t (fun i x => f i x + g i x) O S ≤
      paperAtlasWeighted base m t f O S + paperAtlasWeighted base m t g O S := by
  unfold paperAtlasWeighted
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j + base ≤ m + base := by have := Finset.mem_range.mp hj; omega
  have h := parameterRound2_paperAtlasCj_add_le (j + base) f g O S hO hSO hf hg
    (ne_top_of_le_ne_top hfFinite (parameterRound2_paperAtlasCj_mono_order hjm f O S))
    (ne_top_of_le_ne_top hgFinite (parameterRound2_paperAtlasCj_mono_order hjm g O S))
  simpa only [mul_add] using mul_le_mul_right h (ENNReal.ofReal t ^ j)

/-- The same exact scalar factor controls every original weighted level. -/
theorem parameterRound2_paperAtlasWeighted_smul_le
    (base m : ℕ) (t : ℝ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i))
    (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfFinite : paperAtlasCj (m + base) f O S ≠ ⊤) (c : ℝ) :
    paperAtlasWeighted base m t (fun i x => c • f i x) O S ≤
      ENNReal.ofReal |c| * paperAtlasWeighted base m t f O S := by
  unfold paperAtlasWeighted
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j + base ≤ m + base := by have := Finset.mem_range.mp hj; omega
  have h := parameterRound2_paperAtlasCj_smul_le (j + base) f O S hO hSO hf
    (ne_top_of_le_ne_top hfFinite (parameterRound2_paperAtlasCj_mono_order hjm f O S)) c
  calc
    _ ≤ ENNReal.ofReal t ^ j * (ENNReal.ofReal |c| * paperAtlasCj (j + base) f O S) :=
      mul_le_mul_right h _
    _ = _ := by ac_rfl

#print axioms parameterRound2_paperAtlasWeighted_add_le
#print axioms parameterRound2_paperAtlasWeighted_smul_le
#print axioms parameterRound2_paperAtlasWeighted_le_topOrder
end
end GlobalEmbedding.Continuation
