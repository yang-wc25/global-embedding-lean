import Initialization.Colored.NativeReferenceJets

/-!
# Fixed-order reference bounds for the same actual selector map

The outer derivative constants are obtained from the actual smooth selector on
the compact whole product. They are chosen before the frequency, local patches,
cutoffs, phases, and source point. Composition uses the genuine radial extension
and its genuine derivatives on an open neighborhood of the sphere product.
-/

noncomputable section
open Function Set Metric
open scoped ContDiff Topology Manifold

namespace GlobalEmbedding.Initialization
open GlobalEmbedding.Paper

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition with the actual ambient extension, with all hypotheses stated
on genuine derivatives. This works in any open coordinate neighborhood. -/
theorem coloredSelectorMap_reference_bound {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → color i = color j →
      Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
    (O : Set E) (hO : IsOpen O)
    (hZ : ContDiffOn ℝ ∞ (coloredProductAmbient color χ ℓ T) O)
    (x : E) (hx : x ∈ O) (j : ℕ) (B D : ℝ)
    (houter : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i (selectorAmbientExtension (fun _ : Fin n ↦ C) S)
        (hopfProductInclusion (fun _ : Fin n ↦ C)
          (coloredProduct color χ ℓ hdisjoint hsquare T x))‖ ≤ B)
    (hinner : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (coloredProductAmbient color χ ℓ T) x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ j (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x‖ ≤
      (j.factorial : ℝ) * B * D ^ j := by
  let P := fun _ : Fin n ↦ C
  have hg : ContDiffOn ℝ ∞ (selectorAmbientExtension P S) (hopfRadialDomain P) :=
    fun z hz ↦ (selectorAmbientExtension_contDiffAt P S hS hz).contDiffWithinAt
  have hmaps : MapsTo (coloredProductAmbient color χ ℓ T) O (hopfRadialDomain P) := by
    intro y _
    exact hopfProductInclusion_mem_radial P
      (coloredProduct color χ ℓ hdisjoint hsquare T y)
  have houter' (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (selectorAmbientExtension P S) (hopfRadialDomain P)
        (coloredProductAmbient color χ ℓ T x)‖ ≤ B := by
    rw [iteratedFDerivWithin_of_isOpen i (hopfRadialDomain P).isOpen (hmaps hx)]
    exact houter i hi
  have hinner' (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i (coloredProductAmbient color χ ℓ T) O x‖ ≤ D ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    exact hinner i hi hij
  have hb := norm_iteratedFDerivWithin_comp_le hg hZ
    (by simp : (j : ℕ∞ω) ≤ ∞) (hopfRadialDomain P).isOpen.uniqueDiffOn
    hO.uniqueDiffOn hmaps hx houter' hinner'
  rw [iteratedFDerivWithin_of_isOpen j hO hx,
    ← coloredSelectorMap_eq_extension S color χ ℓ hdisjoint hsquare T] at hb
  exact hb

/-- A finite outer-jet envelope. Only the already fixed selector enters here. -/
def coloredSelectorOuterEnvelope (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), B i

theorem coloredSelectorOuterEnvelope_nonneg (B : ℕ → ℝ)
    (hB : ∀ i, 0 ≤ B i) (j : ℕ) : 0 ≤ coloredSelectorOuterEnvelope B j :=
  Finset.sum_nonneg (fun i _ ↦ hB i)

theorem le_coloredSelectorOuterEnvelope (B : ℕ → ℝ)
    (hB : ∀ i, 0 ≤ B i) {i j : ℕ} (hij : i ≤ j) :
    B i ≤ coloredSelectorOuterEnvelope B j := by
  exact Finset.single_le_sum (fun k _ ↦ hB k) (by simp; omega)

/-- The reference constants are existentially fixed before T and all local
preparation data. The supplied inner budget is an estimate on the already
constructed ambient map, which the preceding native wave lemmas produce. -/
theorem exists_coloredSelectorMap_reference_bounds {n C : ℕ} [Fact (0 < C)]
    (S : FreeHopfProduct (fun _ : Fin n ↦ C) → F)
    (hS : ContMDiff (freeHopfModel (fun _ : Fin n ↦ C)) 𝓘(ℝ, F) ∞ S)
    (U : ℕ → ℝ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 < R j) ∧
      ∀ (color : ι → Fin C) (χ : ι → E → ℝ) (ℓ : Fin n → ι → E → ℝ)
        (hdisjoint : ∀ i k, i ≠ k → color i = color k →
          Disjoint (tsupport (χ i)) (tsupport (χ k)))
        (hsquare : ∀ x, ∑ i, χ i x ^ 2 = 1) (T : ℝ)
        (O : Set E) (hO : IsOpen O)
        (hZ : ContDiffOn ℝ ∞ (coloredProductAmbient color χ ℓ T) O)
        (x : E) (hx : x ∈ O) (j : ℕ),
        (∀ i, 1 ≤ i → i ≤ j →
          ‖iteratedFDeriv ℝ i (coloredProductAmbient color χ ℓ T) x‖ ≤ U j) →
        ‖iteratedFDeriv ℝ j (coloredSelectorMap S color χ ℓ hdisjoint hsquare T) x‖ ≤ R j := by
  obtain ⟨B, hBpos, hB⟩ := selectorAmbientExtension_uniform_derivatives
    (fun _ : Fin n ↦ C) S hS
  let R : ℕ → ℝ := fun j ↦ max 1
    ((j.factorial : ℝ) * coloredSelectorOuterEnvelope B j * (max 1 (U j)) ^ j)
  refine ⟨R, fun j ↦ lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro color χ ℓ hdisjoint hsquare T O hO hZ x hx j hj
  apply le_trans (coloredSelectorMap_reference_bound S hS color χ ℓ hdisjoint hsquare T
    O hO hZ x hx j (coloredSelectorOuterEnvelope B j) (max 1 (U j)) ?_ ?_)
    (le_max_right _ _)
  · intro i hi
    exact (hB i (coloredProduct color χ ℓ hdisjoint hsquare T x)).trans
      (le_coloredSelectorOuterEnvelope B (fun k ↦ (hBpos k).le) hi)
  · intro i hi hij
    exact (hj i hi hij).trans ((le_max_right _ _).trans
      (le_self_pow₀ (le_max_left _ _) (by omega)))

end GlobalEmbedding.Initialization
