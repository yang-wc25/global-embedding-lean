import Smoothing.ParameterRound2InitialWeights

/-!
# Exact original weighted initialization estimate

A contraction of the actual map and addition of the actual normalized metric
error have the original pair budget. Only the tensor error through order m is
used, with the explicit finite derivative-level factor m+1. The full-joint
map base is still 2; no parameter derivative is omitted.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι : Type*} [Fintype ι] {a q q' : ℕ}

theorem parameterRound2_initial_coordinate_pair_budget
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (g e : ι → (Fin a → ℝ) → Fin q' → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (O i))
    (he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i))
    (hfFinite : paperAtlasCj (m+2) f O S ≠ ⊤)
    (hgFinite : paperAtlasCj m g O S ≠ ⊤)
    (heFinite : paperAtlasCj m e O S ≠ ⊤)
    (c b : ℝ) (hc : |c| ≤ 1) (hb : 0 ≤ b) :
    let W := paperAtlasWeighted 2 m t (fun i x => c • f i x) O S +
      paperAtlasWeighted 0 m t (fun i x => g i x + b • e i x) O S
    W ≠ ⊤ ∧ W.toReal ≤
      (paperAtlasWeighted 2 m t f O S).toReal +
      (paperAtlasWeighted 0 m t g O S).toReal +
        b * (m+1) * (paperAtlasCj m e O S).toReal := by
  dsimp only
  let Wf := paperAtlasWeighted 2 m t f O S
  let Wg := paperAtlasWeighted 0 m t g O S
  let Ne := paperAtlasCj m e O S
  have hWf : Wf ≠ ⊤ := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 m t f O S hfFinite
  have hWg : Wg ≠ ⊤ := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 m t g O S (by simpa using hgFinite)
  have hesc : paperAtlasCj m (fun i x => b • e i x) O S ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top heFinite)
      (parameterRound2_paperAtlasCj_smul_le m e O S hO hSO he heFinite b)
  have hfsc := parameterRound2_paperAtlasWeighted_smul_le 2 m t f O S hO hSO hf hfFinite c
  have hfsc' : paperAtlasWeighted 2 m t (fun i x => c • f i x) O S ≤ Wf := by
    apply hfsc.trans
    have hc' : ENNReal.ofReal |c| ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hc
    simpa only [one_mul] using mul_le_mul_left hc' Wf
  have hadd := parameterRound2_paperAtlasWeighted_add_le 0 m t g (fun i x => b • e i x)
    O S hO hSO hg (fun i => (he i).const_smul b) (by simpa using hgFinite) (by simpa using hesc)
  have hes := parameterRound2_paperAtlasWeighted_smul_le 0 m t e O S hO hSO he
    (by simpa using heFinite) b
  have hetop := parameterRound2_paperAtlasWeighted_le_topOrder 0 m ht ht1 e O S
  have hew : paperAtlasWeighted 0 m t (fun i x => b • e i x) O S ≤
      ENNReal.ofReal b * (m + 1 : ℝ≥0∞) * Ne := by
    rw [abs_of_nonneg hb] at hes
    apply hes.trans
    simpa only [Nat.add_zero, mul_assoc] using mul_le_mul_right hetop (ENNReal.ofReal b)
  have hle : paperAtlasWeighted 2 m t (fun i x => c • f i x) O S +
      paperAtlasWeighted 0 m t (fun i x => g i x + b • e i x) O S ≤
        Wf + Wg + ENNReal.ofReal b * (m + 1 : ℝ≥0∞) * Ne := by
    calc
      _ ≤ Wf + (Wg + ENNReal.ofReal b * (m + 1 : ℝ≥0∞) * Ne) :=
        add_le_add hfsc' (hadd.trans (add_le_add le_rfl hew))
      _ = _ := by ac_rfl
  have hbound : Wf + Wg + ENNReal.ofReal b * (m + 1 : ℝ≥0∞) * Ne ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hWf,hWg⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)) heFinite⟩
  refine ⟨ne_top_of_le_ne_top hbound hle, ?_⟩
  have hreal := ENNReal.toReal_mono hbound hle
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hWf,hWg⟩)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)) heFinite),
    ENNReal.toReal_add hWf hWg, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hb] at hreal
  have hcast : ((m : ℝ≥0∞) + 1).toReal = (m : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  simpa only [hcast] using hreal

#print axioms parameterRound2_initial_coordinate_pair_budget
end
end GlobalEmbedding.Continuation
