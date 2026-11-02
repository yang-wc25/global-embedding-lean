import Smoothing.ParameterGeometryJets

/-!
# Joint derivatives of the actual first and second spatial derivatives

Reuse the existing native contraction proofs in ParameterGeometryJets.
The new consumer preserves the base-two weighted Core convention and
produces both profiles together, including zero-dimensional model spaces.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep Es Y : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The base-two original map budget yields both required slow profiles
without an extra inverse power of ell for the first or second spatial jet. -/
theorem actual_spatial_first_second_slow_jets
    (f : Ep × Es → Y) (O S : Set (Ep × Es)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) (j : ℕ) (ell M : ℝ) (hell : 0 ≤ ell)
    (hb : ∀ k ≤ j, ∀ b ≤ 2, ∀ z ∈ S,
      ell^k * ‖iteratedFDeriv ℝ (k+b) f z‖ ≤ M) :
    (ContDiffOn ℝ ∞ (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ M) ∧
    (ContDiffOn ℝ ∞ (fun w : Ep × Es =>
        fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
        (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ M) := by
  have hs := incrementsJointSpatialJets_bridge f O hO hf
  refine ⟨⟨hs.2.1,?_⟩,⟨hs.2.2,?_⟩⟩
  · intro k hk z hz
    exact (mul_le_mul_of_nonneg_left
      (spatial_first_jet_le hO hf (hSO hz) k)
      (pow_nonneg hell k)).trans (hb k hk 1 (by decide) z hz)
  · intro k hk z hz
    exact (mul_le_mul_of_nonneg_left
      (spatial_second_jet_le hO hf (hSO hz) k)
      (pow_nonneg hell k)).trans (hb k hk 2 le_rfl z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_spatial_first_second_slow_jets
