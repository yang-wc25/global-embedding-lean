import Smoothing.ParameterGeometryModel

/-!
# The actual geometric input and its B/T derivative producer

Only derivatives through k+2 of the cutoff and chart transition occur. The
unknown map and smoothing scale do not appear anywhere in this producer.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace
attribute [local instance] spatialTransferInputNormedAddCommGroup spatialTransferInputNormedSpace

/-- Actual spatial derivatives of the cutoff square and spatial transition component. -/
def spatialTransferInputField (w : Ep × Es → ℝ) (v : Ep × Es → Es)
    (z : Ep × Es) : SpatialTransferInput Es :=
  (spatialNativeJet w z,
    fderiv ℝ (fun x => v (z.1,x)) z.2,
    fderiv ℝ (fderiv ℝ (fun x => v (z.1,x))) z.2)

theorem spatialTransferInputField_contDiffOn {w : Ep × Es → ℝ} {v : Ep × Es → Es}
    {O : Set (Ep × Es)} (hO : IsOpen O)
    (hw : ContDiffOn ℝ ∞ w O) (hv : ContDiffOn ℝ ∞ v O) :
    ContDiffOn ℝ ∞ (spatialTransferInputField w v) O := by
  have hj := incrementsJointSpatialJets_bridge v O hO hv
  exact (spatialNativeJet_contDiffOn hO hw).prodMk (hj.2.1.prodMk hj.2.2)

/-- Finite geometric input profile; at zero it uses only W(0..2), T(1..2). -/
def parameterGeometryInputBound (W T : ℕ → ℝ) (k : ℕ) : ℝ :=
  W k + (W (k+1) + W (k+2)) + (T (k+1) + T (k+2))

theorem parameterGeometryInputBound_nonneg {W T : ℕ → ℝ}
    (hW : ∀ k, 0 ≤ W k) (hT : ∀ k, 0 ≤ T k) (k : ℕ) :
    0 ≤ parameterGeometryInputBound W T k := by
  exact add_nonneg (add_nonneg (hW k) (add_nonneg (hW (k+1)) (hW (k+2))))
    (add_nonneg (hT (k+1)) (hT (k+2)))

/-- The full actual geometric input jet follows from original full geometric
jets through k+2, with a constant and radius independent of chart count. -/
theorem spatialTransferInputField_jet_le {w : Ep × Es → ℝ} {v : Ep × Es → Es}
    {O : Set (Ep × Es)} (hO : IsOpen O)
    (hw : ContDiffOn ℝ ∞ w O) (hv : ContDiffOn ℝ ∞ v O)
    (W T : ℕ → ℝ) (hW : ∀ a, 0 ≤ W a) (hT : ∀ a, 0 ≤ T a)
    {z : Ep × Es} (hz : z ∈ O) (k : ℕ)
    (hwBound : ∀ a ≤ k+2, ‖iteratedFDeriv ℝ a w z‖ ≤ W a)
    (hvBound : ∀ a, 1 ≤ a → a ≤ k+2 → ‖iteratedFDeriv ℝ a v z‖ ≤ T a) :
    ‖iteratedFDeriv ℝ k (spatialTransferInputField w v) z‖ ≤ parameterGeometryInputBound W T k := by
  have hwj := incrementsJointSpatialJets_bridge w O hO hw
  have hvj := incrementsJointSpatialJets_bridge v O hO hv
  have hw0 := hw.contDiffAt (hO.mem_nhds hz)
  have hw1 := hwj.2.1.contDiffAt (hO.mem_nhds hz)
  have hw2 := hwj.2.2.contDiffAt (hO.mem_nhds hz)
  have hv1 := hvj.2.1.contDiffAt (hO.mem_nhds hz)
  have hv2 := hvj.2.2.contDiffAt (hO.mem_nhds hz)
  have h1w := (spatial_first_jet_le hO hw hz k).trans (hwBound (k+1) (by omega))
  have h2w := (spatial_second_jet_le hO hw hz k).trans (hwBound (k+2) le_rfl)
  have h1v := (spatial_first_jet_le hO hv hz k).trans (hvBound (k+1) (by omega) (by omega))
  have h2v := (spatial_second_jet_le hO hv hz k).trans (hvBound (k+2) (by omega) le_rfl)
  have hwp : ‖iteratedFDeriv ℝ k (spatialNativeJet w) z‖ ≤ W k + (W (k+1)+W (k+2)) :=
    parameter_prod_jet_le hw0 (hw1.prodMk hw2) k (hW k) (add_nonneg (hW _) (hW _))
      (hwBound k (by omega)) (parameter_prod_jet_le hw1 hw2 k (hW _) (hW _) h1w h2w)
  exact parameter_prod_jet_le (spatialNativeJet_contDiffOn hO hw |>.contDiffAt (hO.mem_nhds hz))
    (hv1.prodMk hv2) k (add_nonneg (hW _) (add_nonneg (hW _) (hW _)))
    (add_nonneg (hT _) (hT _)) hwp (parameter_prod_jet_le hv1 hv2 k (hT _) (hT _) h1v h2v)

/-- Extracting the actual source component of a product transition cannot
increase any native joint derivative. -/
theorem parameter_source_component_jet_le {t : Ep × Es → Ep × Es}
    {O : Set (Ep × Es)} (hO : IsOpen O) (ht : ContDiffOn ℝ ∞ t O)
    {z : Ep × Es} (hz : z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => (t y).2) z‖ ≤ ‖iteratedFDeriv ℝ k t z‖ := by
  have h := (ContinuousLinearMap.snd ℝ Ep Es).norm_iteratedFDeriv_comp_left
    (ht.contDiffAt (hO.mem_nhds hz)) (n := k) (by simp)
  apply h.trans
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ Ep Es)
      (norm_nonneg (iteratedFDeriv ℝ k t z)))

#print axioms spatialTransferInputField_contDiffOn
#print axioms spatialTransferInputField_jet_le
#print axioms parameter_source_component_jet_le
end
end GlobalEmbedding.Continuation
