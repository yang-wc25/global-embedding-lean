import GlobalEmbedding.Paper.FiniteCjNormSpecification
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Actual coordinate coefficients and finite Fréchet jet norms

Source: `literature/parallelizable-stable-plus-one/main.tex`, notation225–238 and
`lem:increments`. These are explicitly coefficient gauges, before the separate smooth
mixed-coordinate-partial identification. No raw atlas boundedness is inferred.
-/

open scoped ENNReal

namespace GlobalEmbedding.Paper

/-- The actual component and ordered-coordinate coefficient supremum through order j.
It is extended-valued and records unbounded families faithfully. Its identification
with the paper's scalar mixed partials requires a separate smoothness argument. -/
noncomputable def coordinateJetGauge {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ k : Fin (j + 1), ⨆ x : U, ⨆ σ : Fin k.val → Fin n, ⨆ c : Fin q,
    ENNReal.ofReal ‖iteratedFDeriv ℝ k.val f x (fun a ↦ Pi.single (σ a) 1) c‖

/-- Finite-coordinate multilinear expansion bounds the actual operator norm by
n^k times a common bound on every standard-basis component. Empty coordinate
and degree-zero cases are included in the same finite sums. -/
theorem coordinate_multilinear_opNorm_le {n q k : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Fin n → ℝ) (Fin q → ℝ))
    {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ σ : Fin k → Fin n, ∀ c : Fin q,
      ‖p (fun a ↦ Pi.single (σ a) 1) c‖ ≤ B) :
    ‖p‖ ≤ (n : ℝ) ^ k * B := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hv : (fun i ↦ ∑ j : Fin n, v i j • (Pi.single j 1 : Fin n → ℝ)) = v := by
    funext i j
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : p v = ∑ σ : Fin k → Fin n,
      p (fun i ↦ v i (σ i) • (Pi.single (σ i) 1 : Fin n → ℝ)) := by
    conv_lhs => rw [← hv]
    rw [p.map_sum]
  rw [hexp]
  calc
    _ ≤ ∑ σ : Fin k → Fin n,
        ‖p (fun i ↦ v i (σ i) • (Pi.single (σ i) 1 : Fin n → ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Fin k → Fin n, (∏ i : Fin k, ‖v i‖) * B := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [p.map_smul_univ, norm_smul, norm_prod]
      apply mul_le_mul
      · exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
          norm_le_pi_norm (v i) (σ i))
      · exact (pi_norm_le_iff_of_nonneg hB).2 (hp σ)
      · positivity
      · positivity
    _ = ((n : ℝ) ^ k * B) * ∏ i : Fin k, ‖v i‖ := by
      simp [mul_comm, mul_left_comm, mul_assoc]

/-- Every actual basis coefficient lies below its actual derivative operator norm. -/
theorem coordinate_jet_coefficient_le {n q k : ℕ}
    (f : (Fin n → ℝ) → Fin q → ℝ) (x : Fin n → ℝ)
    (σ : Fin k → Fin n) (c : Fin q) :
    ‖iteratedFDeriv ℝ k f x (fun a ↦ Pi.single (σ a) 1) c‖ ≤
      ‖iteratedFDeriv ℝ k f x‖ := by
  exact (norm_le_pi_norm _ c).trans (by
    simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ k f x).le_opNorm (fun a ↦ Pi.single (σ a) 1))

/-- Honest bounded operator ranges bound the extended coordinate coefficient gauge. -/
theorem coordinateJetGauge_le_finiteCjNorm {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ))
    (hf : ∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖)) :
    coordinateJetGauge j f U ≤ ENNReal.ofReal (finiteCjNorm j f U) := by
  apply iSup_le
  intro k
  apply iSup_le
  intro x
  apply iSup_le
  intro σ
  apply iSup_le
  intro c
  apply ENNReal.ofReal_le_ofReal
  exact (coordinate_jet_coefficient_le f x σ c).trans
    ((finiteCjNorm_specification j f U hf).2.1 k.val (by omega) x x.property)

/-- Actual finite coordinate bounds supply the boundedness needed by real conditional
suprema; the existing real Cj norm is then controlled with no chart-count factor. -/
theorem finiteCjNorm_le_coordinate_bound {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ))
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ k ≤ j, ∀ x ∈ U, ∀ σ : Fin k → Fin n, ∀ c : Fin q,
      ‖iteratedFDeriv ℝ k f x (fun a ↦ Pi.single (σ a) 1) c‖ ≤ B) :
    (∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖)) ∧
      finiteCjNorm j f U ≤ (∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k) * B := by
  have hb : ∀ k ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ k f x‖ ≤ (n : ℝ) ^ k * B := by
    intro k hk x hx
    exact coordinate_multilinear_opNorm_le _ hB (hf k hk x hx)
  have hbounded : ∀ k ≤ j,
      BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖) := by
    intro k hk
    exact ⟨(n : ℝ) ^ k * B, by rintro r ⟨x, rfl⟩; exact hb k hk x x.property⟩
  refine ⟨hbounded, ?_⟩
  have h := (finiteCjNorm_specification j f U hbounded).2.2.1
    (fun k ↦ (n : ℝ) ^ k * B) (fun _ _ ↦ by positivity) hb
  simpa only [Finset.sum_mul] using h

/-- The complete-lattice supremum bounds each actual coefficient, without finiteness. -/
theorem coordinate_jet_coefficient_le_gauge {n q k j : ℕ}
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ)) (hk : k ≤ j)
    (x : U) (σ : Fin k → Fin n) (c : Fin q) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ k f x (fun a ↦ Pi.single (σ a) 1) c‖ ≤
      coordinateJetGauge j f U := by
  exact le_iSup_of_le ⟨k, by omega⟩ (le_iSup_of_le x
    (le_iSup_of_le σ (le_iSup_of_le c le_rfl)))

/-- Finiteness of the extended coefficient gauge is exactly genuine boundedness
of all actual derivative operator ranges. No conditional real supremum is totalized
into evidence of boundedness. -/
theorem coordinateJetGauge_ne_top_iff {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ)) :
    coordinateJetGauge j f U ≠ ⊤ ↔
      ∀ k ≤ j, BddAbove (Set.range fun x : U ↦ ‖iteratedFDeriv ℝ k f x‖) := by
  constructor
  · intro hfinite
    apply (finiteCjNorm_le_coordinate_bound j f U
      (B := (coordinateJetGauge j f U).toReal) ENNReal.toReal_nonneg ?_).1
    intro k hk x hx σ c
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1
      (coordinate_jet_coefficient_le_gauge f U hk ⟨x, hx⟩ σ c)
  · intro hf
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (coordinateJetGauge_le_finiteCjNorm j f U hf)

/-- Two-sided real comparison is used only after the actual extended gauge is finite. -/
theorem coordinateJetGauge_toReal_comparison {n q : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (U : Set (Fin n → ℝ))
    (hfinite : coordinateJetGauge j f U ≠ ⊤) :
    (coordinateJetGauge j f U).toReal ≤ finiteCjNorm j f U ∧
      finiteCjNorm j f U ≤ (∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k) *
        (coordinateJetGauge j f U).toReal := by
  have hf := (coordinateJetGauge_ne_top_iff j f U).1 hfinite
  constructor
  · have h := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2
      (coordinateJetGauge_le_finiteCjNorm j f U hf)
    simpa only [ENNReal.toReal_ofReal (finiteCjNorm_specification j f U hf).1] using h
  · apply (finiteCjNorm_le_coordinate_bound j f U
      (B := (coordinateJetGauge j f U).toReal) ENNReal.toReal_nonneg ?_).2
    intro k hk x hx σ c
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).1
      (coordinate_jet_coefficient_le_gauge f U hk ⟨x, hx⟩ σ c)

/-- Finite-chart MAX of the actual coefficient gauges, with empty supremum zero.
This remains an explicit coefficient intermediate until scalar-partial identification. -/
noncomputable def coordinateAtlasJetGauge {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (U : ι → Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ i, coordinateJetGauge j (f i) (U i)

/-- Literal weighted sum of cumulative atlas gauges; base0 is the ordinary field
convention, base2 the map-twojet convention. Product coordinates keep all derivatives. -/
noncomputable def coordinateAtlasWeightedGauge {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (U : ι → Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (j + 1), ENNReal.ofReal ell ^ a *
    coordinateAtlasJetGauge (a + base) f U

/-- Finite atlas MAX is finite exactly when the actual coordinate jets in EVERY
chart have genuinely bounded operator ranges. No chart-count constant is introduced. -/
theorem coordinateAtlasJetGauge_ne_top_iff {ι : Type*} [Fintype ι] {n q : ℕ} (j : ℕ)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ) (U : ι → Set (Fin n → ℝ)) :
    coordinateAtlasJetGauge j f U ≠ ⊤ ↔
      ∀ i, ∀ k ≤ j, BddAbove (Set.range fun x : U i ↦ ‖iteratedFDeriv ℝ k (f i) x‖) := by
  constructor
  · intro h i
    apply (coordinateJetGauge_ne_top_iff j (f i) (U i)).1
    exact ne_top_of_le_ne_top h (le_iSup (fun i ↦ coordinateJetGauge j (f i) (U i)) i)
  · intro h
    exact iSup_ne_top (fun i ↦ (coordinateJetGauge_ne_top_iff j (f i) (U i)).2 (h i))

/-- Literal weighted field/twojet coefficient norms are finite from actual chart
bounds through j+base; this includes empty charts/domains and ell0. -/
theorem coordinateAtlasWeightedGauge_ne_top {ι : Type*} [Fintype ι] {n q : ℕ}
    (base j : ℕ) (ell : ℝ) (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (U : ι → Set (Fin n → ℝ))
    (hf : ∀ i, ∀ k ≤ j + base,
      BddAbove (Set.range fun x : U i ↦ ‖iteratedFDeriv ℝ k (f i) x‖)) :
    coordinateAtlasWeightedGauge base j ell f U ≠ ⊤ := by
  apply ENNReal.sum_ne_top.2
  intro a ha
  apply ENNReal.mul_ne_top
  · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  · apply (coordinateAtlasJetGauge_ne_top_iff (a + base) f U).2
    intro i k hk
    exact hf i k (by simp only [Finset.mem_range] at ha; omega)

end GlobalEmbedding.Paper
