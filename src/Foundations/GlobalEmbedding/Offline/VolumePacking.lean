import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scale-independent volume packing for the enlarged-support graph

Source: main.tex, `prop:initialization`, line 801; DAG leaf
`initialization-colored-cutoffs-separated-net-volume-packing-degree`.

The distance is an extended metric, allowing distinct Riemannian components
to be infinitely far apart. Measures remain extended-valued until an explicit
finite upper bound justifies taking their real values. The proof uses actual
disjoint balls and countable additivity, not an assumed packing-number bound.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace GlobalEmbedding.Offline

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- Finite additivity on the actual disjoint small balls bounds their number.
No global finiteness of the measure or metric distance is required. -/
theorem measure_packing_card_mul_le
    {ι : Type*} (s : Finset ι) (c : ι → X) (p : X)
    (μ : Measure X) (r R L U : ℝ≥0∞)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → r + r ≤ edist (c i) (c j))
    (hinside : ∀ i ∈ s, eball (c i) r ⊆ eball p R)
    (hlower : ∀ i ∈ s, L ≤ μ (eball (c i) r))
    (hupper : μ (eball p R) ≤ U) :
    (s.card : ℝ≥0∞) * L ≤ U := by
  have hd : (s : Set ι).PairwiseDisjoint (fun i ↦ eball (c i) r) := by
    intro i hi j hj hij
    exact eball_disjoint (hsep i hi j hj hij)
  calc
    (s.card : ℝ≥0∞) * L = ∑ _i ∈ s, L := by simp
    _ ≤ ∑ i ∈ s, μ (eball (c i) r) := Finset.sum_le_sum hlower
    _ = μ (⋃ i ∈ s, eball (c i) r) :=
      (measure_biUnion_finset hd (fun _ _ ↦ measurableSet_eball)).symm
    _ ≤ μ (eball p R) := measure_mono (iUnion₂_subset hinside)
    _ ≤ U := hupper

/-- The exact scale-free neighbor packing estimate. With separation `R/10`,
neighbor centers at distance at most `R/2`, and small balls of radius `R/30`,
their cardinality is at most `ceil ((β/α)*30^n)`.

The small balls are genuinely disjoint and lie in the OPEN radius-`R` ball.
Only the displayed lower and upper volume inequalities are needed; in the
Riemannian application these are supplied by uniform coordinate volume bounds.
The case `n=0`, empty neighbor sets, and disconnected spaces is retained. -/
theorem packing_card_le_scale_free
    {ι : Type*} (s : Finset ι) (c : ι → X) (p : X) (μ : Measure X)
    (n : ℕ) {R α β : ℝ} (hR : 0 < R) (hα : 0 < α) (hβ : 0 ≤ β)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ENNReal.ofReal (R / 10) ≤ edist (c i) (c j))
    (hnear : ∀ i ∈ s, edist (c i) p ≤ ENNReal.ofReal (R / 2))
    (hlower : ∀ i ∈ s, ENNReal.ofReal (α * (R / 30) ^ n) ≤
      μ (eball (c i) (ENNReal.ofReal (R / 30))))
    (hupper : μ (eball p (ENNReal.ofReal R)) ≤ ENNReal.ofReal (β * R ^ n)) :
    s.card ≤ ⌈(β / α) * (30 : ℝ) ^ n⌉₊ := by
  have hr : 0 ≤ R / 30 := by positivity
  have hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ENNReal.ofReal (R / 30) + ENNReal.ofReal (R / 30) ≤ edist (c i) (c j) := by
    intro i hi j hj hij
    apply le_trans ?_ (hsep i hi j hj hij)
    rw [← ENNReal.ofReal_add hr hr]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hinside : ∀ i ∈ s,
      eball (c i) (ENNReal.ofReal (R / 30)) ⊆ eball p (ENNReal.ofReal R) := by
    intro i hi
    apply eball_subset
    · calc
        edist (c i) p + ENNReal.ofReal (R / 30) ≤
            ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 30) :=
          add_le_add (hnear i hi) le_rfl
        _ = ENNReal.ofReal (R / 2 + R / 30) :=
          (ENNReal.ofReal_add (by positivity) hr).symm
        _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal (by linarith)
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hnear i hi)
  have hmeasure := measure_packing_card_mul_le s c p μ
    (ENNReal.ofReal (R / 30)) (ENNReal.ofReal R)
    (ENNReal.ofReal (α * (R / 30) ^ n)) (ENNReal.ofReal (β * R ^ n))
    hdisjoint hinside hlower hupper
  have hsmall : 0 < α * (R / 30) ^ n := by positivity
  have hlarge : 0 ≤ β * R ^ n := by positivity
  have hreal : (s.card : ℝ) * (α * (R / 30) ^ n) ≤ β * R ^ n := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hsmall.le, ENNReal.toReal_ofReal hlarge] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hratio : β * R ^ n / (α * (R / 30) ^ n) = (β / α) * (30 : ℝ) ^ n := by
    rw [div_pow]
    field_simp
  have hcard : (s.card : ℝ) ≤ (β / α) * (30 : ℝ) ^ n := by
    rw [← hratio]
    exact (le_div_iff₀ hsmall).2 hreal
  exact_mod_cast hcard.trans (Nat.le_ceil ((β / α) * (30 : ℝ) ^ n))

/-- The ACTUAL enlarged closed-ball intersection graph. -/
def closedBallIntersectionGraph {ι : Type*} (c : ι → X) (R : ℝ≥0∞) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (closedEBall (c i) R ∩ closedEBall (c j) R).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- An actual enlarged-ball intersection bounds the distance of its centers.
The intermediate point is supplied by the intersection itself. -/
theorem closedBallIntersectionGraph_edist_le
    {ι : Type*} (c : ι → X) (R : ℝ≥0∞) {i j : ι}
    (h : (closedBallIntersectionGraph c R).Adj i j) :
    edist (c j) (c i) ≤ R + R := by
  obtain ⟨z, hzi, hzj⟩ := h.2
  exact (edist_triangle_left (c j) (c i) z).trans (add_le_add hzj hzi)

/-- The actual closed radius-`R/4` intersection graph has the stated degree
bound, derived from volume comparison at radii `R/30` and `R`. The conclusion
uses the native finite cardinality of its neighbor set, which is equal to
`SimpleGraph.degree` under any chosen finite enumeration. -/
theorem closedBallIntersectionGraph_degree_le
    {ι : Type*} [Fintype ι] (c : ι → X) (μ : Measure X)
    (n : ℕ) {R α β : ℝ} (hR : 0 < R) (hα : 0 < α) (hβ : 0 ≤ β)
    (hsep : ∀ i j, i ≠ j → ENNReal.ofReal (R / 10) ≤ edist (c i) (c j))
    (hlower : ∀ i, ENNReal.ofReal (α * (R / 30) ^ n) ≤
      μ (eball (c i) (ENNReal.ofReal (R / 30))))
    (hupper : ∀ i, μ (eball (c i) (ENNReal.ofReal R)) ≤ ENNReal.ofReal (β * R ^ n))
    (i : ι) :
    ((closedBallIntersectionGraph c (ENNReal.ofReal (R / 4))).neighborSet i).ncard ≤
      ⌈(β / α) * (30 : ℝ) ^ n⌉₊ := by
  classical
  let G := closedBallIntersectionGraph c (ENNReal.ofReal (R / 4))
  let s := (G.neighborSet i).toFinset
  have hnear (j : ι) (hj : j ∈ s) : edist (c j) (c i) ≤ ENNReal.ofReal (R / 2) := by
    have hadj : G.Adj i j := by
      change j ∈ G.neighborSet i
      exact Set.mem_toFinset.mp hj
    have h := closedBallIntersectionGraph_edist_le c (ENNReal.ofReal (R / 4)) hadj
    calc
      edist (c j) (c i) ≤ ENNReal.ofReal (R / 4) + ENNReal.ofReal (R / 4) := h
      _ = ENNReal.ofReal (R / 4 + R / 4) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal (R / 2) := by congr 1; ring
  have h := packing_card_le_scale_free s c (c i) μ n hR hα hβ
    (fun j _hj k _hk hjk ↦ hsep j k hjk) hnear (fun j _hj ↦ hlower j) (hupper i)
  simpa only [s, G, Set.toFinset_card, Set.fintypeCard_eq_ncard] using h

/-- The exact radii from the manuscript, with `K≥1`. The constant
`ceil ((β/α)*30^n)` is independent of both `K` and the number of centers.
This is the volume-packing DAG leaf, expressed for the actual given measure
and extended distance; the preceding volume-comparison provider supplies its
two-sided ball bounds when the measure is Riemannian volume. -/
theorem scaled_closedBallIntersectionGraph_degree_le
    {ι : Type*} [Fintype ι] (c : ι → X) (μ : Measure X)
    (n : ℕ) {ρ K α β : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hsep : ∀ i j, i ≠ j → ENNReal.ofReal (ρ / (10 * K)) ≤ edist (c i) (c j))
    (hvolume : ∀ x : X, ∀ s : ℝ, 0 < s → s ≤ ρ →
      ENNReal.ofReal (α * s ^ n) ≤ μ (eball x (ENNReal.ofReal s)) ∧
      μ (eball x (ENNReal.ofReal s)) ≤ ENNReal.ofReal (β * s ^ n))
    (i : ι) :
    ((closedBallIntersectionGraph c (ENNReal.ofReal (ρ / (4 * K)))).neighborSet i).ncard ≤
      ⌈(β / α) * (30 : ℝ) ^ n⌉₊ := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hR : 0 < ρ / K := div_pos hρ hKpos
  have hRle : ρ / K ≤ ρ := (div_le_iff₀ hKpos).2 (by nlinarith)
  have hfour : ρ / (4 * K) = (ρ / K) / 4 := by ring
  have hten : ρ / (10 * K) = (ρ / K) / 10 := by ring
  rw [hfour]
  apply closedBallIntersectionGraph_degree_le c μ n hR hα hβ
  · intro j k hjk
    simpa only [hten] using hsep j k hjk
  · intro j
    exact (hvolume (c j) ((ρ / K) / 30) (by positivity)
      ((by linarith : (ρ / K) / 30 ≤ ρ / K).trans hRle)).1
  · intro j
    exact (hvolume (c j) (ρ / K) hR hRle).2

#print axioms measure_packing_card_mul_le
#print axioms packing_card_le_scale_free
#print axioms closedBallIntersectionGraph_edist_le
#print axioms closedBallIntersectionGraph_degree_le
#print axioms scaled_closedBallIntersectionGraph_degree_le

end GlobalEmbedding.Offline
