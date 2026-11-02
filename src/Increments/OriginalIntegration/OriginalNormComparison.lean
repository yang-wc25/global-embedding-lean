import FaithfulRepair.OriginalJetFiniteness
import GlobalEmbedding.Offline.CoordinateStageSeries
import GlobalEmbedding.Offline.PaperSmoothingEstimates

/-!
# Quantitative recovery of the unchanged original norm from internal cover samples

The internal samples may be compact carriers manufactured inside the original
coordinate norm pieces.  Only their physical covering property is used here.
Every derivative in the result is still evaluated on the original `Omega`.
The explicit comparison cost depends on dimension, derivative order and the
original transition budget; it is chosen before the number of charts, all
sample sets and the function.  No compactness of original norm domains is used.

This is the norm transport needed to run an internal compact-germ repair and
return its SAME sequence and limit to the original paper norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation.OriginalIntegration

def originalCoverNormCost (a : ℕ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (j+1),
    (k.factorial : ℝ) * (max 1 (a : ℝ))^j * bufferedTransitionPrefix T k ^ k

theorem originalCoverNormCost_pos (a : ℕ) (T : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (j : ℕ) : 0 < originalCoverNormCost a T j := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range (j+1),
      (k.factorial : ℝ) * (max 1 (a : ℝ))^j * bufferedTransitionPrefix T k ^ k := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
      (pow_nonneg (le_trans (by norm_num) (one_le_bufferedTransitionPrefix hT k)) _)
  unfold originalCoverNormCost
  linarith

theorem originalCoverNormCost_term_le (a : ℕ) (T : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) {j k : ℕ} (hk : k ≤ j) :
    (k.factorial : ℝ) * (max 1 (a : ℝ))^j * bufferedTransitionPrefix T k ^ k ≤
      originalCoverNormCost a T j := by
  have hle := Finset.single_le_sum (s := Finset.range (j+1))
    (f := fun k => (k.factorial : ℝ) * (max 1 (a : ℝ))^j * bufferedTransitionPrefix T k ^ k)
    (fun l _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
      (pow_nonneg (le_trans (by norm_num) (one_le_bufferedTransitionPrefix hT l)) _))
    (Finset.mem_range.mpr (by omega : k < j+1))
  unfold originalCoverNormCost
  linarith

variable {a q : ℕ} {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- A finite original Cj bound on the internal cover samples gives an explicit
bound on the unchanged original domains.  The physical cover is a geometric
property of the actual samples, not an assumed norm comparison. -/
theorem original_norm_bound_from_cover
    (chart : ι → OpenPartialHomeomorph X (Fin a → ℝ))
    (hSmoothTransition : ∀ i j, ContDiffOn ℝ ∞ ((chart i).symm.trans (chart j))
      ((chart i).symm.trans (chart j)).source)
    (Omega S : ι → Set (Fin a → ℝ))
    (hOmega : ∀ i, Omega i ⊆ (chart i).target)
    (hS : ∀ i, S i ⊆ (chart i).target)
    (hCover : ∀ i y, y ∈ Omega i → ∃ l,
      (chart i).symm y ∈ (chart l).source ∧ (chart l) ((chart i).symm y) ∈ S l)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ Omega i,
      y ∈ ((chart i).symm.trans (chart l)).source →
      ‖iteratedFDeriv ℝ k ((chart i).symm.trans (chart l)) y‖ ≤ T k)
    (f : X → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (chart i).symm) (chart i).target)
    (j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hBound : paperAtlasCj j (fun i => f ∘ (chart i).symm)
      (fun i => (chart i).target) S ≤ ENNReal.ofReal B) :
    paperAtlasCj j (fun i => f ∘ (chart i).symm)
      (fun i => (chart i).target) Omega ≤
      ENNReal.ofReal (originalCoverNormCost a T j * B) := by
  have hD : 1 ≤ max 1 (a : ℝ) := le_max_left _ _
  have hD0 : 0 ≤ max 1 (a : ℝ) := le_trans zero_le_one hD
  apply paperAtlasCj_le_of_jet_bound j _ _ Omega
    (fun i => (chart i).open_target) hOmega hf
  intro i k hk y hy
  obtain ⟨l,hl,hSl⟩ := hCover i y hy
  let e := (chart i).symm.trans (chart l)
  have he : y ∈ e.source := ⟨hOmega i hy,hl⟩
  have hMaps : MapsTo e e.source (chart l).target := fun z hz => (chart l).map_source hz.2
  have hEq : (f ∘ (chart i).symm) =ᶠ[𝓝 y] (f ∘ (chart l).symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds he] with z hz
    change f ((chart i).symm z) = f ((chart l).symm ((chart l) ((chart i).symm z)))
    have hzl : (chart i).symm z ∈ (chart l).source := hz.2
    rw [(chart l).left_inv hzl]
  rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
  have hComp := parameter_general_composition_jet_le T hT e.open_source
    (chart l).open_target (hSmoothTransition i l) (hf l) hMaps he k
    ((max 1 (a : ℝ))^j * B)
    (fun r hr => by
      have hlocal : paperCoordinateCj j (f ∘ (chart l).symm) (chart l).target (S l) ≤
          ENNReal.ofReal B := (le_iSup (fun z => paperCoordinateCj j
            (f ∘ (chart z).symm) (chart z).target (S z)) l).trans hBound
      have hjet := iteratedFDeriv_le_of_paperCoordinateCj_le (chart l).open_target
        (hS l) (hf l) hB hlocal (hr.trans hk) hSl
      have hpow : (a : ℝ)^r ≤ (max 1 (a : ℝ))^j :=
        (pow_le_pow_left₀ (Nat.cast_nonneg a) (le_max_right _ _) r).trans
          (pow_le_pow_right₀ hD (hr.trans hk))
      exact hjet.trans (mul_le_mul_of_nonneg_right hpow hB))
    (fun r hr _ => hTransition i l r hr y hy he)
  calc
    ‖iteratedFDeriv ℝ k ((f ∘ (chart l).symm) ∘ e) y‖ ≤
        (k.factorial : ℝ) * ((max 1 (a : ℝ))^j * B) * bufferedTransitionPrefix T k ^ k := hComp
    _ = ((k.factorial : ℝ) * (max 1 (a : ℝ))^j * bufferedTransitionPrefix T k ^ k) * B := by ring
    _ ≤ originalCoverNormCost a T j * B :=
      mul_le_mul_of_nonneg_right (originalCoverNormCost_term_le a T hT hk) hB

/-- Extended-norm comparison, including the top case.  Every finite real
projection used in the proof is guarded.  The cost has no chart-count input. -/
theorem original_norm_le_cover_norm
    (chart : ι → OpenPartialHomeomorph X (Fin a → ℝ))
    (hSmoothTransition : ∀ i j, ContDiffOn ℝ ∞ ((chart i).symm.trans (chart j))
      ((chart i).symm.trans (chart j)).source)
    (Omega S : ι → Set (Fin a → ℝ))
    (hOmega : ∀ i, Omega i ⊆ (chart i).target)
    (hS : ∀ i, S i ⊆ (chart i).target)
    (hCover : ∀ i y, y ∈ Omega i → ∃ l,
      (chart i).symm y ∈ (chart l).source ∧ (chart l) ((chart i).symm y) ∈ S l)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ Omega i,
      y ∈ ((chart i).symm.trans (chart l)).source →
      ‖iteratedFDeriv ℝ k ((chart i).symm.trans (chart l)) y‖ ≤ T k)
    (f : X → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (chart i).symm) (chart i).target)
    (j : ℕ) :
    paperAtlasCj j (fun i => f ∘ (chart i).symm) (fun i => (chart i).target) Omega ≤
      ENNReal.ofReal (originalCoverNormCost a T j) *
        paperAtlasCj j (fun i => f ∘ (chart i).symm) (fun i => (chart i).target) S := by
  let c := paperAtlasCj j (fun i => f ∘ (chart i).symm) (fun i => (chart i).target) S
  by_cases hc : c = ⊤
  · change _ ≤ ENNReal.ofReal (originalCoverNormCost a T j) * c
    rw [hc, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (originalCoverNormCost_pos a T hT j))]
    exact le_top
  · have h := original_norm_bound_from_cover chart hSmoothTransition Omega S hOmega hS
      hCover T hT hTransition f hf j c.toReal ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal hc])
    rw [ENNReal.ofReal_mul (originalCoverNormCost_pos a T hT j).le,
      ENNReal.ofReal_toReal hc] at h
    exact h

end GlobalEmbedding.Continuation.OriginalIntegration

#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_norm_bound_from_cover
#print axioms GlobalEmbedding.Continuation.OriginalIntegration.original_norm_le_cover_norm
