import Smoothing.ParameterRound2NormAlgebra

/-!
# Original weighted triangle estimate for the actual normalized defect identity

This module keeps the true three terms in (6.6): the tensor smoothing tail,
the literal finite-increment metric error, and the true bilinear cross term.
No squared smoothing error is introduced. Finiteness is proved before every
real projection, and the original atlas maximum and total-joint norm remain.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι : Type*} [Fintype ι] {a q : ℕ}

theorem parameterRound2_topOrder_finite_of_weighted
    (base m : ℕ) {t : ℝ} (ht : 0 < t)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasWeighted base m t f O S ≠ ⊤) :
    paperAtlasCj (m+base) f O S ≠ ⊤ := by
  have hsum : (∑ j ∈ Finset.range (m+1), ENNReal.ofReal t^j * paperAtlasCj (j+base) f O S) ≠ ⊤ := hfinite
  have hterm := ENNReal.sum_ne_top.mp hsum m (by simp)
  have hpos : ENNReal.ofReal t^m ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr ht) m
  intro htop
  rw [htop,ENNReal.mul_top hpos] at hterm
  exact hterm rfl

theorem parameterRound2_paperAtlasWeighted_neg
    (base m : ℕ) (t : ℝ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) :
    paperAtlasWeighted base m t (fun i x => -f i x) O S = paperAtlasWeighted base m t f O S := by
  unfold paperAtlasWeighted
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal t^j*z)
    (paperAtlasCj_neg (j+base) f O S hO hSO hf)

theorem parameterRound2_paperAtlasWeighted_sub_le
    (base m : ℕ) (t : ℝ) (f g : ι → (Fin a → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin a → ℝ)) (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (hfFinite : paperAtlasCj (m+base) f O S ≠ ⊤)
    (hgFinite : paperAtlasCj (m+base) g O S ≠ ⊤) :
    paperAtlasWeighted base m t (fun i x => f i x-g i x) O S ≤
      paperAtlasWeighted base m t f O S + paperAtlasWeighted base m t g O S := by
  have hn : paperAtlasCj (m+base) (fun i x => -g i x) O S ≠ ⊤ := by
    exact ne_top_of_le_ne_top hgFinite (le_of_eq (paperAtlasCj_neg (m+base) g O S hO hSO hg))
  have h := parameterRound2_paperAtlasWeighted_add_le base m t f (fun i x => -g i x)
    O S hO hSO hf (fun i => (hg i).neg) hfFinite hn
  simpa only [← sub_eq_add_neg,parameterRound2_paperAtlasWeighted_neg base m t g O S hO hSO hg] using h

/-- Actual weighted three-term estimate for b*(a*f-g-h), with the original
atlas MAX. The first scalar is the genuine delta square, the second is the
genuine inverse next delta square in the concrete repair consumer. -/
theorem parameterRound2_paperAtlasWeighted_normalized_three_terms
    (m : ℕ) {t : ℝ} (ht : 0 < t)
    (f g h : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) (O i))
    (hfFinite : paperAtlasWeighted 0 m t f O S ≠ ⊤)
    (hgFinite : paperAtlasWeighted 0 m t g O S ≠ ⊤)
    (hhFinite : paperAtlasWeighted 0 m t h O S ≠ ⊤)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let R := fun i x => b • (a • f i x-g i x-h i x)
    paperAtlasWeighted 0 m t R O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 m t R O S).toReal ≤
        b * (a*(paperAtlasWeighted 0 m t f O S).toReal +
          (paperAtlasWeighted 0 m t g O S).toReal + (paperAtlasWeighted 0 m t h O S).toReal) := by
  intro R
  have hft := parameterRound2_topOrder_finite_of_weighted 0 m ht f O S hfFinite
  have hgt := parameterRound2_topOrder_finite_of_weighted 0 m ht g O S hgFinite
  have hht := parameterRound2_topOrder_finite_of_weighted 0 m ht h O S hhFinite
  let af := fun i x => a • f i x
  have haf : ∀ i, ContDiffOn ℝ ∞ (af i) (O i) := fun i => (hf i).const_smul a
  have haft : paperAtlasCj (m+0) af O S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hft)
      (parameterRound2_paperAtlasCj_smul_le (m+0) f O S hO hSO hf hft a)
  have hafw := parameterRound2_paperAtlasWeighted_smul_le 0 m t f O S hO hSO hf hft a
  rw [abs_of_nonneg ha] at hafw
  have hafFinite : paperAtlasWeighted 0 m t af O S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfFinite) hafw
  let af_g := fun i x => af i x-g i x
  have hafg := parameterRound2_paperAtlasWeighted_sub_le 0 m t af g O S hO hSO haf hg haft hgt
  have hafgFinite : paperAtlasWeighted 0 m t af_g O S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hafFinite,hgFinite⟩) hafg
  have hafgt := parameterRound2_topOrder_finite_of_weighted 0 m ht af_g O S hafgFinite
  have hafgs : ∀ i, ContDiffOn ℝ ∞ (af_g i) (O i) := fun i => (haf i).sub (hg i)
  let inner := fun i x => af_g i x-h i x
  have hinner := parameterRound2_paperAtlasWeighted_sub_le 0 m t af_g h O S hO hSO hafgs hh hafgt hht
  have hinnerFinite : paperAtlasWeighted 0 m t inner O S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hafgFinite,hhFinite⟩) hinner
  have hinnert := parameterRound2_topOrder_finite_of_weighted 0 m ht inner O S hinnerFinite
  have hinners : ∀ i, ContDiffOn ℝ ∞ (inner i) (O i) := fun i => (hafgs i).sub (hh i)
  have houter := parameterRound2_paperAtlasWeighted_smul_le 0 m t inner O S hO hSO hinners hinnert b
  rw [abs_of_nonneg hb] at houter
  have hle : paperAtlasWeighted 0 m t R O S ≤
      ENNReal.ofReal b * (ENNReal.ofReal a * paperAtlasWeighted 0 m t f O S +
        paperAtlasWeighted 0 m t g O S + paperAtlasWeighted 0 m t h O S) :=
    houter.trans (mul_le_mul_right
      (hinner.trans (add_le_add (hafg.trans (add_le_add hafw le_rfl)) le_rfl)) _)
  have hbound : ENNReal.ofReal b * (ENNReal.ofReal a * paperAtlasWeighted 0 m t f O S +
      paperAtlasWeighted 0 m t g O S + paperAtlasWeighted 0 m t h O S) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfFinite,hgFinite⟩,hhFinite⟩)
  refine ⟨ne_top_of_le_ne_top hbound hle,?_⟩
  have hreal := ENNReal.toReal_mono hbound hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfFinite,hgFinite⟩) hhFinite,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfFinite) hgFinite,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal ha] at hreal
  exact hreal

#print axioms parameterRound2_paperAtlasWeighted_normalized_three_terms
end
end GlobalEmbedding.Continuation
