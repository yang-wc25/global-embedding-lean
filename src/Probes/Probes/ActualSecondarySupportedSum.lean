import Probes.ActualSecondaryJointQuadratic
import Smoothing.ParameterTransferBounds

/-!
# The actual ordered secondary sum uses only local primary multiplicity

The four signed branches and all ordered pairs are retained. Only the
identically zero opposite-sign diagonal records are omitted, exactly as in
the original quadratic cancellation. The bound uses the number of active
primary supports at the observation point, never the total number of charts,
primary labels or subordinate pieces. Per-branch profiles and support are
supplied by the actual quadratic secondary producer.
-/

noncomputable section
open Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {Label X Y : Type*} [Fintype Label] [DecidableEq Label]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The literal full ordered nonzero secondary sum, with no phase quotient
or half-list replacing the original four branches. -/
def actualSecondaryNonzeroSum (W : Label → Label → Fin 4 → X → Y) : X → Y :=
  fun z => ∑ nu, ∑ mu, ∑ q ∈ Finset.univ.filter
    (fun q : Fin 4 => nu ≠ mu ∨ q = 0 ∨ q = 3), W nu mu q z

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem actual_secondary_active_record_card_le
    (K : Label → Set X) (x : X) (L : ℕ)
    (hL : (Finset.univ.filter (fun nu => x ∈ K nu)).card ≤ L) :
    (Finset.univ.filter (fun r : (Label × Label) × Fin 4 =>
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) ∧ x ∈ K r.1.1 ∩ K r.1.2)).card ≤
        4 * L ^ 2 := by
  classical
  let active := Finset.univ.filter (fun nu => x ∈ K nu)
  have hsub : (Finset.univ.filter (fun r : (Label × Label) × Fin 4 =>
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) ∧ x ∈ K r.1.1 ∩ K r.1.2)) ⊆
      (active.product active).product Finset.univ := by
    intro r hr
    have hp := (Finset.mem_filter.mp hr).2.2
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ((active.product active).product Finset.univ).card := Finset.card_le_card hsub
    _ = 4 * active.card ^ 2 := by simp [pow_two]; omega
    _ ≤ 4 * L ^ 2 := by gcongr

/-- Native joint jets of the literal secondary sum. Off-support terms have
actual zero germs; the existing finite-sum jet theorem is reused after the
original active-record count. The constant is `4 L² C`, not `4 card(Label)² C`.
All fields are already expressed in the SAME observation coordinates. -/
theorem actual_secondary_supported_sum_weighted_jets
    (W : Label → Label → Fin 4 → X → Y) (K : Label → Set X)
    (O : Label → Label → Fin 4 → Set X) (S : Set X)
    (hO : ∀ nu mu q, IsOpen (O nu mu q))
    (hSO : ∀ nu mu q, S ∩ (K nu ∩ K mu) ⊆ O nu mu q)
    (hW : ∀ nu mu q, ContDiffOn ℝ ∞ (W nu mu q) (O nu mu q))
    (hsupport : ∀ nu mu q, tsupport (W nu mu q) ⊆ K nu ∩ K mu)
    (L j : ℕ) (hL : ∀ x ∈ S, (Finset.univ.filter (fun nu => x ∈ K nu)).card ≤ L)
    (tau delta C : ℝ) (htau : 0 < tau) (hC : 0 ≤ C)
    (hbound : ∀ nu mu q, ∀ x ∈ S ∩ (K nu ∩ K mu),
      tau ^ j * ‖iteratedFDeriv ℝ j (W nu mu q) x‖ ≤ C * delta ^ 2) :
    ∀ x ∈ S, tau ^ j * ‖iteratedFDeriv ℝ j (actualSecondaryNonzeroSum W) x‖ ≤
      ((4 * L ^ 2 : ℕ) : ℝ) * C * delta ^ 2 := by
  classical
  let f : ((Label × Label) × Fin 4) → X → Y := fun r z =>
    if r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then W r.1.1 r.1.2 r.2 z else 0
  have he : actualSecondaryNonzeroSum W = fun z => ∑ r, f r z := by
    funext z
    simp only [actualSecondaryNonzeroSum, Fintype.sum_prod_type, Finset.sum_filter, f]
  intro x hx
  let active := Finset.univ.filter (fun r : (Label × Label) × Fin 4 =>
    (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) ∧ x ∈ K r.1.1 ∩ K r.1.2)
  have hactive : active.card ≤ 4 * L ^ 2 :=
    actual_secondary_active_record_card_le K x L (hL x hx)
  have hreg : ∀ r ∈ active, ContDiffAt ℝ ∞ (f r) x := by
    intro r hr
    obtain ⟨hq, hK⟩ := (Finset.mem_filter.mp hr).2
    simpa only [f, if_pos hq] using
      (hW r.1.1 r.1.2 r.2).contDiffAt
        ((hO r.1.1 r.1.2 r.2).mem_nhds (hSO r.1.1 r.1.2 r.2 ⟨hx, hK⟩))
  have hzero : ∀ r ∉ active, f r =ᶠ[𝓝 x] (fun _ => 0) := by
    intro r hr
    by_cases hq : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3
    · have hK : x ∉ K r.1.1 ∩ K r.1.2 := by
        intro hxK
        exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hxK⟩)
      have hs : x ∉ tsupport (W r.1.1 r.1.2 r.2) :=
        fun hh => hK (hsupport r.1.1 r.1.2 r.2 hh)
      filter_upwards [(isClosed_tsupport (W r.1.1 r.1.2 r.2)).isOpen_compl.mem_nhds hs] with y hy
      simp only [f, if_pos hq, image_eq_zero_of_notMem_tsupport hy]
    · exact Filter.Eventually.of_forall fun _ => by simp only [f, if_neg hq]
  have hb : ∀ r ∈ active, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ C * delta ^ 2 / tau ^ j := by
    intro r hr
    obtain ⟨hq, hK⟩ := (Finset.mem_filter.mp hr).2
    have h : ‖iteratedFDeriv ℝ j (W r.1.1 r.1.2 r.2) x‖ ≤ C * delta ^ 2 / tau ^ j :=
      (le_div_iff₀ (pow_pos htau j)).2
      (by simpa only [mul_comm] using hbound r.1.1 r.1.2 r.2 x ⟨hx, hK⟩)
    simpa only [f, if_pos hq] using h
  have hsum := parameter_finite_sum_jet_le f x active (4 * L ^ 2) j
    (C * delta ^ 2 / tau ^ j) hactive (by positivity) hreg hzero hb
  rw [he]
  calc
    _ ≤ tau ^ j * (((4 * L ^ 2 : ℕ) : ℝ) * (C * delta ^ 2 / tau ^ j)) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg htau.le _)
    _ = _ := by field_simp [(pow_pos htau j).ne'] <;> ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_active_record_card_le
#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_sum_weighted_jets
