import Initialization.Geometry.AmbientVolume
import GlobalEmbedding.Offline.VolumePacking
import Mathlib.Tactic

/-! Genuine Euclidean packing with arbitrary fixed radius ratio. -/

open Set Metric MeasureTheory
open scoped ENNReal

namespace GlobalEmbedding.Initialization

/-- Actual Euclidean volume bounds the number of δ-separated centers in an
arbitrary Aδ-ball. The bound is independent of δ, the index type and the net
size. This includes dimension zero and an empty finite set. -/
theorem euclidean_packing_card_le
    {n : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n))
    {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ENNReal.ofReal δ ≤ edist (c i) (c j))
    (hnear : ∀ i ∈ s, edist (c i) p ≤ ENNReal.ofReal (A * δ)) :
    s.card ≤ ⌈(3 * (A + 1)) ^ n⌉₊ := by
  obtain ⟨α, hα, hvol⟩ := exists_euclidean_ball_volume_coefficient n
  have hsmall : 0 < δ / 3 := by positivity
  have hbig : 0 < (A + 1) * δ := by positivity
  have hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) ≤ edist (c i) (c j) := by
    intro i hi j hj hij
    apply le_trans ?_ (hsep i hi j hj hij)
    rw [← ENNReal.ofReal_add hsmall.le hsmall.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hinside : ∀ i ∈ s, eball (c i) (ENNReal.ofReal (δ / 3)) ⊆
      eball p (ENNReal.ofReal ((A + 1) * δ)) := by
    intro i hi
    apply eball_subset
    · calc
        edist (c i) p + ENNReal.ofReal (δ / 3) ≤
            ENNReal.ofReal (A * δ) + ENNReal.ofReal (δ / 3) :=
          add_le_add (hnear i hi) le_rfl
        _ = ENNReal.ofReal (A * δ + δ / 3) :=
          (ENNReal.ofReal_add (mul_nonneg hA hδ.le) hsmall.le).symm
        _ ≤ ENNReal.ofReal ((A + 1) * δ) := ENNReal.ofReal_le_ofReal (by nlinarith)
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hnear i hi)
  have hmeasure := GlobalEmbedding.Offline.measure_packing_card_mul_le s c p volume
    (ENNReal.ofReal (δ / 3)) (ENNReal.ofReal ((A + 1) * δ))
    (ENNReal.ofReal (α * (δ / 3) ^ n))
    (ENNReal.ofReal (α * ((A + 1) * δ) ^ n))
    hdisjoint hinside (fun i _ ↦ le_of_eq (hvol (c i) (δ / 3) hsmall).symm)
    (le_of_eq (hvol p ((A + 1) * δ) hbig))
  have hdenom : 0 < α * (δ / 3) ^ n := by positivity
  have hnum : 0 ≤ α * ((A + 1) * δ) ^ n := by positivity
  have hreal : (s.card : ℝ) * (α * (δ / 3) ^ n) ≤ α * ((A + 1) * δ) ^ n := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hdenom.le, ENNReal.toReal_ofReal hnum] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hratio : α * ((A + 1) * δ) ^ n / (α * (δ / 3) ^ n) =
      (3 * (A + 1)) ^ n := by
    rw [mul_pow, div_pow, mul_pow]
    field_simp
  have hcard : (s.card : ℝ) ≤ (3 * (A + 1)) ^ n := by
    rw [← hratio]
    exact (le_div_iff₀ hdenom).2 hreal
  exact_mod_cast hcard.trans (Nat.le_ceil ((3 * (A + 1)) ^ n))

end GlobalEmbedding.Initialization
