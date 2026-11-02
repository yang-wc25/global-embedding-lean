import Probes.ActualRefinementBumpJets
import Smoothing.TensorLocalNormalizationBounds

/-!
The existing separated-center construction produces actual globally smooth
square cutoffs. A fixed denominator repair allows the raw cover to exist
only near the required set. All derivative constants are selected from the
fixed model, construction radius and local 5^dim multiplicity, before the
finite center family. No total atlas or center count enters these costs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Offline Set Function Metric Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def round4RefinementSquareCutoff (s : Finset E) (r : ℝ) (c : s) : E → ℝ :=
  tensorLocalNormalizedCutoff (fun z : s => actualRefinementBump E r z.val) c

def round4RefinementRawJetProfile (r : ℝ) (j : ℕ) : ℝ :=
  actualRefinementBumpJetCost E j / r^j

theorem round4RefinementRawJetProfile_nonneg {r : ℝ} (hr : 0 < r) (j : ℕ) :
    0 ≤ round4RefinementRawJetProfile E r j :=
  div_nonneg (actualRefinementBumpJetCost_nonneg E j) (pow_nonneg hr.le j)

def round4RefinementSquareProfile (r : ℝ) (hr : 0 < r) : ℕ → ℝ :=
  Classical.choose (exists_tensorLocalNormalizedCutoff_derivative_bounds.{u,u,u} (E := E) (X := E)
    (round4RefinementRawJetProfile E r) (round4RefinementRawJetProfile_nonneg E hr)
    (5^Module.finrank ℝ E))

theorem round4RefinementSquareProfile_nonneg (r : ℝ) (hr : 0 < r) (j : ℕ) :
    0 ≤ round4RefinementSquareProfile E r hr j :=
  (Classical.choose_spec (exists_tensorLocalNormalizedCutoff_derivative_bounds.{u,u,u} (E := E) (X := E)
    (round4RefinementRawJetProfile E r) (round4RefinementRawJetProfile_nonneg E hr)
    (5^Module.finrank ℝ E))).1 j

theorem round4_refinement_raw_local_multiplicity
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) (x : E) :
    (activeCutoffIndices (fun z : s => actualRefinementBump E r z.val) x).card ≤
      5^Module.finrank ℝ E := by
  classical
  let active := activeCutoffIndices (fun z : s => actualRefinementBump E r z.val) x
  have hsubset : active.image Subtype.val ⊆ s.filter (fun c => dist c x ≤ 2*r) := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    have hh := (mem_activeCutoffIndices _ _ _).mp hz
    rw [actualRefinementBump_tsupport E r hr z.val] at hh
    exact Finset.mem_filter.mpr ⟨z.property, by simpa only [mem_closedBall, dist_comm] using hh⟩
  have hcard : (active.image Subtype.val).card = active.card :=
    Finset.card_image_of_injective active Subtype.val_injective
  rw [← hcard]
  exact (Finset.card_le_card hsubset).trans (actual_separated_local_refinement_count s r hr hsep x)

theorem round4_refinement_square_cutoffs
    (s : Finset E) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ dist a b) :
    (∀ c : s, ContDiff ℝ ∞ (round4RefinementSquareCutoff E s r c)) ∧
    (∀ c : s, tsupport (round4RefinementSquareCutoff E s r c) ⊆ closedBall c.val (2*r)) ∧
    (∀ x : E, (activeCutoffIndices (round4RefinementSquareCutoff E s r) x).card ≤
      5^Module.finrank ℝ E) ∧
    (∀ (c : s) (j : ℕ) (x : E),
      ‖iteratedFDeriv ℝ j (round4RefinementSquareCutoff E s r c) x‖ ≤
        round4RefinementSquareProfile E r hr j) := by
  let b := fun z : s => actualRefinementBump E r z.val
  have hbm (z : s) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b z) :=
    (actualRefinementBump_contDiff E r z.val).contMDiff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact (tensorLocalNormalizedCutoff_contMDiff b hbm c).contDiff
  · intro c
    exact (tensorLocalNormalizedCutoff_tsupport_subset b c).trans
      (by rw [actualRefinementBump_tsupport E r hr c.val])
  · intro x
    exact (tensorLocalNormalizedCutoff_card_le b x).trans
      (round4_refinement_raw_local_multiplicity E s r hr hsep x)
  · intro c j x
    have h := (Classical.choose_spec (exists_tensorLocalNormalizedCutoff_derivative_bounds.{u,u,u}
      (E := E) (X := E) (round4RefinementRawJetProfile E r)
      (round4RefinementRawJetProfile_nonneg E hr) (5^Module.finrank ℝ E))).2
      s b id univ isOpen_univ
      (fun z => (actualRefinementBump_contDiff E r z.val).contDiffOn) continuous_id.continuousOn
      (fun y _ => round4_refinement_raw_local_multiplicity E s r hr hsep y)
      (fun z y _ _ k => ?_) c j x (mem_univ x)
    · exact h
    · change ‖iteratedFDeriv ℝ k (actualRefinementBump E r z.val) y‖ ≤
        actualRefinementBumpJetCost E k / r^k
      apply (le_div_iff₀ (pow_pos hr k)).mpr
      simpa only [mul_comm] using actualRefinementBump_weighted_jet E r hr z.val y k

theorem round4_refinement_square_partition_near
    (s : Finset E) (r : ℝ) (hr : 0 < r) (K : Set E)
    (hcover : ∀ x ∈ K, ∃ c ∈ s, dist x c ≤ r) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧
      ∀ x ∈ W, ∑ c : s, round4RefinementSquareCutoff E s r c x ^ 2 = 1 := by
  apply tensorLocalNormalizedCutoff_partition_near
    (fun z : s => actualRefinementBump E r z.val)
    (fun z => (actualRefinementBump_contDiff E r z.val).contMDiff) K
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcover x hx
  exact ⟨⟨c,hc⟩, actualRefinementBump_one E r hr c x hxc⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_refinement_square_cutoffs
#print axioms GlobalEmbedding.Continuation.round4_refinement_square_partition_near
