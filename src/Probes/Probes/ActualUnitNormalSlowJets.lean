import Probes.ActualIncrementSampleProjection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize

/-! Uniform slow jets of actual vector normalization on a positive norm
reserve. Constants depend on finite input jets and the scalar lower margin;
they precede every source function and scale. This is applied below to the
actual first/transverse free-normal projection, never to an assumed unit field. -/

noncomputable section
open GlobalEmbedding.Paper Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

private theorem operation_jets_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
  have hi (i : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    have hc := hg.continuousOn_iteratedFDerivWithin (m := i) (by simp) hU.uniqueDiffOn
    exact (hc.mono hKU).congr (fun x hx ↦
      (iteratedFDerivWithin_of_isOpen i hU (hKU hx)).symm)
  induction j with
  | zero =>
      obtain ⟨C, hC⟩ := hi 0
      refine ⟨max 0 C, le_max_left _ _, ?_⟩
      intro i hi x hx
      have : i = 0 := by omega
      subst i
      exact (hC x hx).trans (le_max_right _ _)
  | succ j ih =>
      obtain ⟨C, hC, hCb⟩ := ih
      obtain ⟨T, hT⟩ := hi (j + 1)
      refine ⟨max C T, hC.trans (le_max_left _ _), ?_⟩
      intro i hi x hx
      by_cases hij : i ≤ j
      · exact (hCb i hij x hx).trans (le_max_left _ _)
      · have : i = j + 1 := by omega
        subst i
        exact (hT x hx).trans (le_max_right _ _)

private theorem operation_scaled_composition
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (f : D → E) (U : Set E) (O : Set D)
    (hU : IsOpen U) (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g U)
    (hf : ContDiffOn ℝ ∞ f O) (hmap : MapsTo f O U)
    (k : ℕ) (ell M C : ℝ) (hell : 0 < ell) (hM : 1 ≤ M)
    {x : D} (hx : x ∈ O)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hfb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    ell ^ k * ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ k.factorial * C * M ^ k := by
  have hD : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDerivWithin ℝ i f O x‖ ≤ (M / ell) ^ i := by
    intro i hi hik
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    have hMi : M ≤ M ^ i := le_self_pow₀ hM (by omega)
    calc
      _ ≤ M / ell ^ i := (le_div_iff₀ (pow_pos hell i)).2 (by nlinarith [hfb i hik])
      _ ≤ M ^ i / ell ^ i := div_le_div_of_nonneg_right hMi (by positivity)
      _ = (M / ell) ^ i := (div_pow M ell i).symm
  have hb := norm_iteratedFDerivWithin_comp_le hg hf (n := k) (by simp)
    hU.uniqueDiffOn hO.uniqueDiffOn hmap hx
    (fun i hi ↦ by rw [iteratedFDerivWithin_of_isOpen i hU (hmap hx)]; exact hC i hi) hD
  rw [iteratedFDerivWithin_of_isOpen k hO hx] at hb
  calc
    _ ≤ ell ^ k * (k.factorial * C * (M / ell) ^ k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = k.factorial * C * M ^ k := by rw [div_pow]; field_simp

variable {N : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem actual_normalize_contDiffOn :
    ContDiffOn ℝ ∞ (NormedSpace.normalize : V → V) ({0}ᶜ : Set V) := by
  have hn : ContDiffOn ℝ ∞ (fun v : V => ‖v‖) ({0}ᶜ : Set V) :=
    contDiffOn_id.norm ℝ (fun _ hv => hv)
  exact (hn.inv (fun v hv => norm_ne_zero_iff.mpr hv)).smul contDiffOn_id

theorem actual_unit_normalization_slow_jets (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
      (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O) (f : D → V)
      (_hf : ContDiffOn ℝ ∞ f O) (ell : ℝ) (_hell : 0 < ell),
      (∀ x ∈ S, c ≤ ‖f x‖) →
      (∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k f x‖ ≤ M) →
      (∀ x ∈ S, ‖NormedSpace.normalize (f x)‖ = 1) ∧
      ∀ k ≤ j, ∀ x ∈ S, ell^k*‖iteratedFDeriv ℝ k (NormedSpace.normalize ∘ f) x‖ ≤ C := by
  let U : Set V := {0}ᶜ
  let K : Set V := {v | c ≤ ‖v‖} ∩ closedBall 0 M
  have hK : IsCompact K := (isCompact_closedBall (0 : V) M).inter_left
    (isClosed_le continuous_const continuous_norm)
  have hKU : K ⊆ U := by
    intro v hv
    have hp : 0 < ‖v‖ := hc.trans_le hv.1
    exact norm_pos_iff.mp hp
  obtain ⟨C,hC,hCb⟩ := operation_jets_on_compact (NormedSpace.normalize : V → V) U K
    isClosed_singleton.isOpen_compl hK hKU actual_normalize_contDiffOn j
  let T := max 1 M
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨j.factorial*C*T^j,by positivity,?_⟩
  intro D _ _ O S hO hSO f hf ell hell hreserve hjets
  have hnonzero (x : D) (hx : x ∈ S) : f x ≠ 0 :=
    norm_pos_iff.mp (hc.trans_le (hreserve x hx))
  refine ⟨fun x hx => NormedSpace.norm_normalize (hnonzero x hx),?_⟩
  intro k hk x hx
  let P := O ∩ f ⁻¹' U
  have hP : IsOpen P := hf.continuousOn.isOpen_inter_preimage hO isClosed_singleton.isOpen_compl
  have hxP : x ∈ P := ⟨hSO hx,hnonzero x hx⟩
  have hVal : ‖f x‖ ≤ M := by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hjets 0 (Nat.zero_le j) x hx
  have hfxK : f x ∈ K := ⟨hreserve x hx,by simpa using hVal⟩
  have hb := operation_scaled_composition (NormedSpace.normalize : V → V) f U P
    isClosed_singleton.isOpen_compl hP actual_normalize_contDiffOn (hf.mono inter_subset_left)
    (fun y hy => hy.2) k ell T C hell hT hxP
    (fun i hi => hCb i (hi.trans hk) _ hfxK)
    (fun i hi => (hjets i (hi.trans hk) x hx).trans (le_max_right _ _))
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hC)
    (pow_le_pow_right₀ hT hk) (by positivity) (by positivity))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_normalize_contDiffOn
#print axioms GlobalEmbedding.Continuation.actual_unit_normalization_slow_jets
