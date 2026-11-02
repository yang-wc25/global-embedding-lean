import Smoothing.ParameterJetIdentities
import Smoothing.ParameterNativePackets
import GlobalEmbedding.Offline.BufferedSmoothingJets

/-!
# Joint derivative bounds for true spatial-jet transfer

Native Leibniz and composition act on the actual spatial jet, with geometry
carried by the coefficient field. These constants have no atlas-count or
field argument. This module does not assume the desired error estimate.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

/-- Geometric transfer coefficient at one additional joint derivative order. -/
def parameterJetTransferCore (C T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l *
    ((j-l).factorial : ℝ) * bufferedTransitionPrefix T (j-l) ^ (j-l)

/-- The constant uses actual support multiplicity, not total chart count. -/
def parameterJetTransferConstant (C T : ℕ → ℝ) (D J : ℕ) : ℝ :=
  (D : ℝ) * ∑ j ∈ Finset.range (J+1), parameterJetTransferCore C T j

theorem parameterJetTransferCore_nonneg {C T : ℕ → ℝ}
    (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (j : ℕ) :
    0 ≤ parameterJetTransferCore C T j := by
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hC l)) (by positivity))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT _)) _)

theorem parameterJetTransferConstant_nonneg {C T : ℕ → ℝ}
    (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D J : ℕ) :
    0 ≤ parameterJetTransferConstant C T D J :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ =>
    parameterJetTransferCore_nonneg hC hT j)

theorem parameterJetTransferConstant_mono {C T : ℕ → ℝ}
    (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ) {j J : ℕ} (hj : j ≤ J) :
    parameterJetTransferConstant C T D j ≤ parameterJetTransferConstant C T D J := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hj 1)
  · intro k _ _
    exact parameterJetTransferCore_nonneg hC hT k

section Transfer
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Derive the native joint bound from the genuine operator and transition
jets, using exactly j additional derivatives of the outer field. -/
theorem parameter_operator_transfer_jet_le (C T : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k)
    {L : E → F →L[ℝ] G} {t : E → E} {v : E → F} {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hL : ContDiffOn ℝ ∞ L U) (ht : ContDiffOn ℝ ∞ t U)
    (hv : ContDiffOn ℝ ∞ v V) (hmap : MapsTo t U V)
    {x : E} (hx : x ∈ U) (j : ℕ) (R : ℝ)
    (hcoeff : ∀ k ≤ j, ‖iteratedFDeriv ℝ k L x‖ ≤ C k)
    (htransition : ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k t x‖ ≤ T k)
    (houter : ∀ k ≤ j, ‖iteratedFDeriv ℝ k v (t x)‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun z => L z (v (t z))) x‖ ≤
      parameterJetTransferCore C T j * R := by
  have hvcomp := hv.comp ht hmap
  have hprod := norm_iteratedFDerivWithin_clm_apply hL hvcomp hU.uniqueDiffOn hx
    (n := j) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at hprod
  apply hprod.trans
  calc
    ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l L x‖ *
        ‖iteratedFDeriv ℝ (j-l) (v ∘ t) x‖ ≤
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * C l *
        (((j-l).factorial : ℝ) * R * bufferedTransitionPrefix T (j-l) ^ (j-l)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlj : l ≤ j := by simpa using hl
      apply mul_le_mul (mul_le_mul_of_nonneg_left (hcoeff l hlj) (by positivity))
        (buffered_composition_jet_le T hT hU hV ht hv hmap hx (j-l) R
          (fun k hk => houter k (hk.trans (Nat.sub_le _ _)))
          (fun k hk hkj => htransition k hk (hkj.trans (Nat.sub_le _ _))))
        (norm_nonneg _) (mul_nonneg (by positivity) (hC l))
    _ = parameterJetTransferCore C T j * R := by
      unfold parameterJetTransferCore
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- True zero germs eliminate inactive summands before multiplicity is used. -/
theorem parameter_finite_sum_jet_le {ι : Type*} [Fintype ι]
    (f : ι → E → F) (x : E) (S : Finset ι) (D j : ℕ) (R : ℝ)
    (hD : S.card ≤ D) (hR : 0 ≤ R)
    (hreg : ∀ i ∈ S, ContDiffAt ℝ ∞ (f i) x)
    (hzero : ∀ i ∉ S, f i =ᶠ[𝓝 x] (fun _ => 0))
    (hbound : ∀ i ∈ S, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, f i y) x‖ ≤ (D : ℝ) * R := by
  classical
  have hall (i : ι) : ContDiffAt ℝ ∞ (f i) x := by
    by_cases hi : i ∈ S
    · exact hreg i hi
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero i hi)
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hall i).of_le (by simp))]
  have hinactive (i : ι) (hi : i ∉ S) : iteratedFDeriv ℝ j (f i) x = 0 := by
    simpa using ((hzero i hi).iteratedFDeriv ℝ j).eq_of_nhds
  have hfiltered : (∑ i, iteratedFDeriv ℝ j (f i) x) =
      ∑ i ∈ S, iteratedFDeriv ℝ j (f i) x :=
    (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hinactive i hi)).symm
  rw [hfiltered]
  calc
    ‖∑ i ∈ S, iteratedFDeriv ℝ j (f i) x‖ ≤
        ∑ i ∈ S, ‖iteratedFDeriv ℝ j (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, R := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * R := by simp
    _ ≤ (D : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hR

end Transfer

section ActualSpatialTransfer
variable {Ep Es Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

/-- Additional joint derivatives of the actual localized map's spatial two-jet.
Both the derivative field and its geometric coefficient were derived above. -/
theorem parameter_spatial_transfer_jet_le (C T : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k)
    {w : Ep × Es → ℝ} {a : Ep → Ep} {b : Es → Es} {u : Ep × Es → Y}
    {Op : Set Ep} {Os : Set Es} {V : Set (Ep × Es)}
    (hOp : IsOpen Op) (hOs : IsOpen Os) (hV : IsOpen V)
    (hw : ContDiffOn ℝ ∞ w (Op ×ˢ Os)) (hu : ContDiffOn ℝ ∞ u V)
    (ha : ContDiffOn ℝ ∞ a Op) (hb : ContDiffOn ℝ ∞ b Os)
    (hmap : ∀ p ∈ Op, ∀ x ∈ Os, (a p,b x) ∈ V)
    {z : Ep × Es} (hz : z ∈ Op ×ˢ Os) (j : ℕ) (R : ℝ)
    (hcoeff : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (spatialTransferField (Y := Y) w b) z‖ ≤ C k)
    (htransition : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (fun y : Ep × Es => (a y.1,b y.2)) z‖ ≤ T k)
    (houter : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (spatialNativeJet u) (a z.1,b z.2)‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (spatialNativeJet (fun y => w y • u (a y.1,b y.2))) z‖ ≤
      parameterJetTransferCore C T j * R := by
  have heq : spatialNativeJet (fun y => w y • u (a y.1,b y.2)) =ᶠ[𝓝 z]
      (fun y => spatialTransferField w b y (spatialNativeJet u (a y.1,b y.2))) := by
    filter_upwards [(hOp.prod hOs).mem_nhds hz] with y hy
    exact spatialNativeJet_transfer hOp hOs hV hw hu ha hb hmap hy
  rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
  exact parameter_operator_transfer_jet_le C T hC hT (hOp.prod hOs) hV
    (spatialTransferField_contDiffOn hOp hOs hw hb)
    ((ha.comp contDiffOn_fst (fun _ h => h.1)).prodMk
      (hb.comp contDiffOn_snd (fun _ h => h.2)))
    (spatialNativeJet_contDiffOn hV hu) (fun y hy => hmap y.1 hy.1 y.2 hy.2)
    hz j R hcoeff htransition houter

end ActualSpatialTransfer

#print axioms parameter_spatial_transfer_jet_le
#print axioms parameter_operator_transfer_jet_le
#print axioms parameter_finite_sum_jet_le

end
end GlobalEmbedding.Continuation
