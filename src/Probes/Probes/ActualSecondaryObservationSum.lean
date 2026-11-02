import Probes.ActualSecondarySupportedWave
import Probes.ActualSecondarySupportedSum

/-!
# Actual observation pullbacks and the local secondary interaction count

Observation charts need only be continuous on their genuine open domains.
The globally supported fields retain their relative support on the original
manifold domain. Off-support observation terms have true zero germs, so no
global continuity of a totalized inverse chart is assumed. The full ordered
four-branch sum has constant `4 L²`, with no total chart-count factor.
-/

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {X P V Label : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Fintype Label] [DecidableEq Label]

omit [Fintype Label] [DecidableEq Label] in
/-- Relative global support creates a true zero germ in an actual observation
chart. No continuity of the observation inverse outside its domain is needed. -/
theorem actual_supported_observation_zero_germ
    (f : P → V) (W K : Set P) (hW : IsOpen W) (hK : IsClosed K)
    (hs : tsupport (fun y : W => f y) ⊆ Subtype.val ⁻¹' K)
    (kappa : X → P) (x : X) (hkappa : ContinuousAt kappa x)
    (hxW : kappa x ∈ W) (hxK : kappa x ∉ K) :
    f ∘ kappa =ᶠ[𝓝 x] (fun _ => 0) := by
  have hnear : ∀ᶠ y in 𝓝 x, kappa y ∈ W ∩ Kᶜ :=
    hkappa.eventually ((hW.inter hK.isOpen_compl).mem_nhds ⟨hxW, hxK⟩)
  filter_upwards [hnear] with y hy
  have hn : (⟨kappa y, hy.1⟩ : W) ∉ tsupport (fun z : W => f z) :=
    fun h => hy.2 (hs h)
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hz

/-- The SAME literal ordered secondary fields are pulled back and summed in
one observation chart. Active piece regularity/jets come from actual local
secondary construction and chart transfer; inactive regularity is proved from
the true global support. All parameter directions remain in the derivatives. -/
theorem actual_secondary_observation_sum_weighted_jets
    (waves : Label → Label → Fin 4 → P → V) (K : Label → Set P)
    (W : Set P) (hW : IsOpen W) (hK : ∀ nu, IsClosed (K nu))
    (hsupport : ∀ nu mu q, tsupport (fun y : W => waves nu mu q y) ⊆
      Subtype.val ⁻¹' (K nu ∩ K mu))
    (kappa : X → P) (Omega S : Set X) (hOmega : IsOpen Omega)
    (hSOmega : S ⊆ Omega) (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (O : Label → Label → Fin 4 → Set X) (hO : ∀ nu mu q, IsOpen (O nu mu q))
    (hSO : ∀ nu mu q, S ∩ kappa ⁻¹' (K nu ∩ K mu) ⊆ O nu mu q)
    (hreg : ∀ nu mu q, ContDiffOn ℝ ∞ (waves nu mu q ∘ kappa) (O nu mu q))
    (L j : ℕ)
    (hL : ∀ x ∈ S, (Finset.univ.filter (fun nu => kappa x ∈ K nu)).card ≤ L)
    (tau delta C : ℝ) (htau : 0 < tau) (hC : 0 ≤ C)
    (hbound : ∀ nu mu q, ∀ x ∈ S ∩ kappa ⁻¹' (K nu ∩ K mu),
      tau ^ j * ‖iteratedFDeriv ℝ j (waves nu mu q ∘ kappa) x‖ ≤ C * delta ^ 2) :
    ∀ x ∈ S,
      ContDiffAt ℝ ∞ (actualSecondaryNonzeroSum (fun nu mu q => waves nu mu q ∘ kappa)) x ∧
      tau ^ j * ‖iteratedFDeriv ℝ j
        (actualSecondaryNonzeroSum (fun nu mu q => waves nu mu q ∘ kappa)) x‖ ≤
          ((4 * L ^ 2 : ℕ) : ℝ) * C * delta ^ 2 := by
  let f : ((Label × Label) × Fin 4) → X → V := fun r x =>
    if r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3 then waves r.1.1 r.1.2 r.2 (kappa x) else 0
  have he : actualSecondaryNonzeroSum (fun nu mu q => waves nu mu q ∘ kappa) =
      fun x => ∑ r, f r x := by
    funext x
    simp only [actualSecondaryNonzeroSum, Fintype.sum_prod_type, Finset.sum_filter, f,
      Function.comp_apply]
  intro x hx
  let active := Finset.univ.filter (fun r : (Label × Label) × Fin 4 =>
    (r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3) ∧ kappa x ∈ K r.1.1 ∩ K r.1.2)
  have hactive : active.card ≤ 4 * L ^ 2 :=
    actual_secondary_active_record_card_le (fun nu => kappa ⁻¹' K nu) x L (hL x hx)
  have hactiveReg : ∀ r ∈ active, ContDiffAt ℝ ∞ (f r) x := by
    intro r hr
    obtain ⟨hq, hKs⟩ := (Finset.mem_filter.mp hr).2
    simpa only [f, if_pos hq, Function.comp_def] using
      (hreg r.1.1 r.1.2 r.2).contDiffAt
        ((hO r.1.1 r.1.2 r.2).mem_nhds (hSO r.1.1 r.1.2 r.2 ⟨hx, hKs⟩))
  have hzero : ∀ r ∉ active, f r =ᶠ[𝓝 x] (fun _ => 0) := by
    intro r hr
    by_cases hq : r.1.1 ≠ r.1.2 ∨ r.2 = 0 ∨ r.2 = 3
    · have hnot : kappa x ∉ K r.1.1 ∩ K r.1.2 := by
        intro hh
        exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hh⟩)
      have hz := actual_supported_observation_zero_germ (waves r.1.1 r.1.2 r.2) W
        (K r.1.1 ∩ K r.1.2) hW ((hK r.1.1).inter (hK r.1.2))
        (hsupport r.1.1 r.1.2 r.2) kappa x
        (hkappa.continuousAt (hOmega.mem_nhds (hSOmega hx))) (hmap (hSOmega hx)) hnot
      simpa only [f, if_pos hq, Function.comp_def] using hz
    · exact Filter.Eventually.of_forall fun _ => by simp only [f, if_neg hq]
  have hAll (r) : ContDiffAt ℝ ∞ (f r) x := by
    by_cases hr : r ∈ active
    · exact hactiveReg r hr
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero r hr)
  have hb : ∀ r ∈ active, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ C * delta ^ 2 / tau ^ j := by
    intro r hr
    obtain ⟨hq, hKs⟩ := (Finset.mem_filter.mp hr).2
    have hh : ‖iteratedFDeriv ℝ j (waves r.1.1 r.1.2 r.2 ∘ kappa) x‖ ≤
        C * delta ^ 2 / tau ^ j := (le_div_iff₀ (pow_pos htau j)).2
      (by simpa only [mul_comm] using hbound r.1.1 r.1.2 r.2 x ⟨hx, hKs⟩)
    simpa only [f, if_pos hq, Function.comp_def] using hh
  rw [he]
  refine ⟨ContDiffAt.sum (fun r _ => hAll r), ?_⟩
  have hsum := parameter_finite_sum_jet_le f x active (4 * L ^ 2) j
    (C * delta ^ 2 / tau ^ j) hactive (by positivity) hactiveReg hzero hb
  calc
    _ ≤ tau ^ j * (((4 * L ^ 2 : ℕ) : ℝ) * (C * delta ^ 2 / tau ^ j)) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg htau.le _)
    _ = _ := by field_simp [(pow_pos htau j).ne']

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_supported_observation_zero_germ
#print axioms GlobalEmbedding.Continuation.actual_secondary_observation_sum_weighted_jets
