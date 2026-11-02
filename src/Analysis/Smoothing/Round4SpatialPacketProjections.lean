import Smoothing.ParameterGeometryJets

/-! Contractions of the same native spatial packet, with norm at most one. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
section ProductContractions
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem round4_first_joint_jet_le_product {f : E → F} {g : E → G} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f z‖ ≤ ‖iteratedFDeriv ℝ k (fun y => (f y,g y)) z‖ := by
  rw [iteratedFDeriv_prodMk hf hg (by simp), ContinuousMultilinearMap.opNorm_prod]
  exact le_max_left _ _

theorem round4_second_joint_jet_le_product {f : E → F} {g : E → G} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (k : ℕ) :
    ‖iteratedFDeriv ℝ k g z‖ ≤ ‖iteratedFDeriv ℝ k (fun y => (f y,g y)) z‖ := by
  rw [iteratedFDeriv_prodMk hf hg (by simp), ContinuousMultilinearMap.opNorm_prod]
  exact le_max_right _ _
end ProductContractions

variable {Ep Es Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem round4_spatial_first_jet_le_packet
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤
      ‖iteratedFDeriv ℝ k (spatialNativeJet f) z‖ := by
  have hs := incrementsJointSpatialJets_bridge f O hO hf
  have h0 := hf.contDiffAt (hO.mem_nhds hz)
  have h1 := hs.2.1.contDiffAt (hO.mem_nhds hz)
  have h2 := hs.2.2.contDiffAt (hO.mem_nhds hz)
  exact (round4_first_joint_jet_le_product h1 h2 k).trans
    (round4_second_joint_jet_le_product h0 (h1.prodMk h2) k)

theorem round4_spatial_second_jet_le_packet
    {f : Ep × Es → Y} {O : Set (Ep × Es)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤
      ‖iteratedFDeriv ℝ k (spatialNativeJet f) z‖ := by
  have hs := incrementsJointSpatialJets_bridge f O hO hf
  have h0 := hf.contDiffAt (hO.mem_nhds hz)
  have h1 := hs.2.1.contDiffAt (hO.mem_nhds hz)
  have h2 := hs.2.2.contDiffAt (hO.mem_nhds hz)
  exact (round4_second_joint_jet_le_product h1 h2 k).trans
    (round4_second_joint_jet_le_product h0 (h1.prodMk h2) k)

/-- Both actual fields follow from the genuine spatial packet, without
assuming any pure parameter derivative of the underlying map. -/
theorem round4_spatial_packet_first_hessian_slow_jets
    (f : Ep × Es → Y) (O S : Set (Ep × Es)) (hO : IsOpen O) (hSO : S ⊆ O)
    (hf : ContDiffOn ℝ ∞ f O) (j : ℕ) (ell R : ℝ) (hell : 0 ≤ ell)
    (hjets : ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (spatialNativeJet f) z‖ ≤ R) :
    (ContDiffOn ℝ ∞ (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun w : Ep × Es => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ R) ∧
    (ContDiffOn ℝ ∞ (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun w : Ep × Es => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ R) := by
  have hs := incrementsJointSpatialJets_bridge f O hO hf
  refine ⟨⟨hs.2.1, ?_⟩, ⟨hs.2.2, ?_⟩⟩
  · intro k hk z hz
    exact (mul_le_mul_of_nonneg_left (round4_spatial_first_jet_le_packet hO hf (hSO hz) k)
      (pow_nonneg hell k)).trans (hjets k hk z hz)
  · intro k hk z hz
    exact (mul_le_mul_of_nonneg_left (round4_spatial_second_jet_le_packet hO hf (hSO hz) k)
      (pow_nonneg hell k)).trans (hjets k hk z hz)

#print axioms round4_spatial_packet_first_hessian_slow_jets
end GlobalEmbedding.Continuation
