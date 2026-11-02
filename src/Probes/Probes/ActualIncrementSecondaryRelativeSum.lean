import Probes.ActualSecondaryRefinedObservationSum
import Smoothing.ParameterRound2GlobalCorrectionSupport

/-!
# Actual secondary sums using only relative support in the true open germ

Every original signed ordered pair is summed over its real secondary chart
refinement before the pair sum. The local factor is exactly `4 L² R`; R is
the true active subordinate count, never the total number of subordinates.
Only support of each literal wave restricted to W is used. Ksub need not be
closed in the ambient manifold and may meet the boundary of W. The same
finite signed ordered sum and its exact 4 L² R constant are preserved.
-/

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {Label Sub X P V : Type*} [Fintype Label] [DecidableEq Label] [Fintype Sub]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_secondary_relative_refined_observation_sum_weighted_jets
    (waves : ((Label × Label) × Fin 4) → Sub → P → V)
    (K : Label → Set P) (Ksub : ((Label × Label) × Fin 4) → Sub → Set P)
    (hsub : ∀ r a, Ksub r a ⊆ K r.1.1 ∩ K r.1.2)
    (W : Set P) (hW : IsOpen W)
    (hsupport : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) → ∀ a,
      tsupport (fun y : W => waves r a y) ⊆ Subtype.val ⁻¹' Ksub r a)
    (kappa : X → P) (Omega S : Set X) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : ((Label × Label) × Fin 4) → Sub → Set X) (hO : ∀ r a, IsOpen (O r a))
    (hSO : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) → ∀ a,
      S ∩ kappa ⁻¹' Ksub r a ⊆ O r a)
    (hreg : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) → ∀ a,
      ContDiffOn ℝ ∞ (waves r a ∘ kappa) (O r a))
    (L R j : ℕ)
    (hL : ∀ x ∈ S, (Finset.univ.filter (fun nu => kappa x ∈ K nu)).card ≤ L)
    (hR : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) → ∀ x ∈ S,
      (Finset.univ.filter (fun a => kappa x ∈ Ksub r a)).card ≤ R)
    (tau Budget : ℝ) (htau : 0 < tau) (hBudget : 0 ≤ Budget)
    (hbound : ∀ r : (Label × Label) × Fin 4,
      (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) → ∀ a,
      ∀ x ∈ S ∩ kappa ⁻¹' Ksub r a,
        tau ^ j * ‖iteratedFDeriv ℝ j (waves r a ∘ kappa) x‖ ≤ Budget) :
    ∀ x ∈ S,
      ContDiffAt ℝ ∞ (actualSecondaryRefinedNonzeroSum (fun r a => waves r a ∘ kappa)) x ∧
      tau ^ j * ‖iteratedFDeriv ℝ j
        (actualSecondaryRefinedNonzeroSum (fun r a => waves r a ∘ kappa)) x‖ ≤
          ((4 * L ^ 2 * R : ℕ) : ℝ) * Budget := by
  let f : (((Label × Label) × Fin 4) × Sub) → X → V := fun t x =>
    if t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3 then waves t.1 t.2 (kappa x) else 0
  have he : actualSecondaryRefinedNonzeroSum (fun r a => waves r a ∘ kappa) =
      fun x => ∑ t, f t x := by
    funext x
    simp [actualSecondaryRefinedNonzeroSum, actualSecondaryNonzeroSum,
      Fintype.sum_prod_type, Finset.sum_filter, f, Finset.sum_ite_irrel]
  intro x hx
  let active := Finset.univ.filter (fun t : (((Label × Label) × Fin 4) × Sub) =>
    (t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3) ∧ kappa x ∈ Ksub t.1 t.2)
  have hactive : active.card ≤ 4 * L ^ 2 * R :=
    actual_secondary_refined_active_card_le K Ksub hsub (kappa x) L R (hL x hx)
      (fun r hq => hR r hq x hx)
  have hactiveReg : ∀ t ∈ active, ContDiffAt ℝ ∞ (f t) x := by
    intro t ht
    obtain ⟨hq, hKs⟩ := (Finset.mem_filter.mp ht).2
    simpa only [f, if_pos hq, Function.comp_def] using
      (hreg t.1 hq t.2).contDiffAt ((hO t.1 t.2).mem_nhds (hSO t.1 hq t.2 ⟨hx, hKs⟩))
  have hzero : ∀ t ∉ active, f t =ᶠ[𝓝 x] (fun _ => 0) := by
    intro t ht
    by_cases hq : t.1.1.1 ≠ t.1.1.2 ∨ t.1.2 = 0 ∨ t.1.2 = 3
    · have hnot : kappa x ∉ Ksub t.1 t.2 := by
        intro hh
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hh⟩)
      have hz := parameterRound2_relative_observation_zero_germ (waves t.1 t.2) W
        (Ksub t.1 t.2) hW (hsupport t.1 hq t.2) kappa x
        (hkappa.continuousAt (hOmega.mem_nhds (hSOmega hx))) (hmap (hSOmega hx)) hnot
      simpa only [f, if_pos hq, Function.comp_def] using hz
    · exact Filter.Eventually.of_forall fun _ => by simp only [f, if_neg hq]
  have hAll (t) : ContDiffAt ℝ ∞ (f t) x := by
    by_cases ht : t ∈ active
    · exact hactiveReg t ht
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero t ht)
  have hb : ∀ t ∈ active, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ Budget / tau ^ j := by
    intro t ht
    obtain ⟨hq, hKs⟩ := (Finset.mem_filter.mp ht).2
    have hh : ‖iteratedFDeriv ℝ j (waves t.1 t.2 ∘ kappa) x‖ ≤ Budget / tau ^ j :=
      (le_div_iff₀ (pow_pos htau j)).2
        (by simpa only [mul_comm] using hbound t.1 hq t.2 x ⟨hx, hKs⟩)
    simpa only [f, if_pos hq, Function.comp_def] using hh
  rw [he]
  refine ⟨ContDiffAt.sum (fun t _ => hAll t), ?_⟩
  have hsum := parameter_finite_sum_jet_le f x active (4 * L ^ 2 * R) j
    (Budget / tau ^ j) hactive (by positivity) hactiveReg hzero hb
  calc
    _ ≤ tau ^ j * (((4 * L ^ 2 * R : ℕ) : ℝ) * (Budget / tau ^ j)) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg htau.le _)
    _ = _ := by field_simp [(pow_pos htau j).ne']

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_relative_refined_observation_sum_weighted_jets
