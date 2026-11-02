import Probes.ActualJointChartTransfer
import Smoothing.ParameterGeometryJets
import Smoothing.WeightedActualGram

/-!
# Genuine tensor pullback through joint parameter-dependent charts

The transported tensor is the original bilinear form evaluated twice on the
actual spatial derivative of the transition. Both frame changes are present.
Its fast weighted jets are produced from the transition's slow profile and
the tensor's original fast jets, with no atlas-count or scale dependence in
the constant and no replacement of the tensor by its component values alone.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

section Composition
variable {X A B C : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem actual_clm_comp_uniform_slow_jets
    (f : X → B →L[ℝ] C) (g : X → A →L[ℝ] B)
    (O : Set X) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (j : ℕ) (tau Mf Mg : ℝ) (htau : 0 ≤ tau) (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (x : X) (hx : x ∈ O)
    (hfj : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i f x‖ ≤ Mf)
    (hgj : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i g x‖ ≤ Mg) :
    ContDiffOn ℝ ∞ (fun z => (f z).comp (g z)) O ∧
      ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i (fun z => (f z).comp (g z)) x‖ ≤
        2^j * Mf * Mg := by
  refine ⟨hf.clm_comp hg,?_⟩
  intro i hi
  have hb := slow_bilinear_jet_bound (ContinuousLinearMap.compL ℝ A B C)
    (ContinuousLinearMap.norm_compL_le ℝ A B C) O hO f g hf hg
    i tau Mf Mg htau hMf x hx
    (fun k hk => hfj k (hk.trans hi)) (fun k hk => hgj k (hk.trans hi))
  apply hb.trans
  gcongr
  norm_num
end Composition

section Bilinear
variable {X Es Et Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

-- Name the native operator instances to keep repeated nested synthesis bounded.
private noncomputable local instance tensorTransferETSemi :
    SeminormedAddCommGroup (Et →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance tensorTransferETNormed :
    NormedAddCommGroup (Et →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance tensorTransferETSpace :
    NormedSpace ℝ (Et →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance tensorTransferSTSemi :
    SeminormedAddCommGroup (Es →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance tensorTransferSTNormed :
    NormedAddCommGroup (Es →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance tensorTransferSTSpace :
    NormedSpace ℝ (Es →L[ℝ] Et →L[ℝ] Z) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance tensorTransferTSSemi :
    SeminormedAddCommGroup (Et →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance tensorTransferTSNormed :
    NormedAddCommGroup (Et →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance tensorTransferTSSpace :
    NormedSpace ℝ (Et →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance tensorTransferSSSemi :
    SeminormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance tensorTransferSSNormed :
    NormedAddCommGroup (Es →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance tensorTransferSSSpace :
    NormedSpace ℝ (Es →L[ℝ] Es →L[ℝ] Z) := ContinuousLinearMap.toNormedSpace

/-- Two actual frame insertions cost two native product estimates. -/
theorem actual_bilinear_pullback_slow_jets
    (B : X → Et →L[ℝ] Et →L[ℝ] Z) (L : X → Es →L[ℝ] Et)
    (O : Set X) (hO : IsOpen O) (hB : ContDiffOn ℝ ∞ B O) (hL : ContDiffOn ℝ ∞ L O)
    (j : ℕ) (tau MB ML : ℝ) (htau : 0 ≤ tau) (hMB : 0 ≤ MB) (hML : 0 ≤ ML)
    (x : X) (hx : x ∈ O)
    (hBj : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i B x‖ ≤ MB)
    (hLj : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i L x‖ ≤ ML) :
    ContDiffOn ℝ ∞ (fun z => (B z).bilinearComp (L z) (L z)) O ∧
    tau^j * ‖iteratedFDeriv ℝ j (fun z => (B z).bilinearComp (L z) (L z)) x‖ ≤
      2^(j+j) * MB * ML^2 := by
  let B1 : X → Es →L[ℝ] Et →L[ℝ] Z := fun z => (B z).comp (L z)
  let flip1 : (Es →L[ℝ] Et →L[ℝ] Z) ≃ₗᵢ[ℝ] (Et →L[ℝ] Es →L[ℝ] Z) :=
    ContinuousLinearMap.flipₗᵢ ℝ Es Et Z
  let B2 : X → Es →L[ℝ] Es →L[ℝ] Z := fun z => (flip1 (B1 z)).comp (L z)
  let flip2 : (Es →L[ℝ] Es →L[ℝ] Z) ≃ₗᵢ[ℝ] (Es →L[ℝ] Es →L[ℝ] Z) :=
    ContinuousLinearMap.flipₗᵢ ℝ Es Es Z
  obtain ⟨hB1,h1⟩ := actual_clm_comp_uniform_slow_jets B L O hO hB hL
    j tau MB ML htau hMB hML x hx hBj hLj
  have hF1 : ContDiffOn ℝ ∞ (flip1 ∘ B1) O := flip1.contDiff.comp_contDiffOn hB1
  have hF1b : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i (flip1 ∘ B1) x‖ ≤ 2^j * MB * ML := by
    intro i hi
    rw [flip1.norm_iteratedFDeriv_comp_left]
    exact h1 i hi
  obtain ⟨hB2,h2⟩ := actual_clm_comp_uniform_slow_jets (flip1 ∘ B1) L O hO hF1 hL
    j tau (2^j * MB * ML) ML htau (by positivity) hML x hx hF1b hLj
  have heq : (fun z => (B z).bilinearComp (L z) (L z)) = flip2 ∘ B2 := rfl
  rw [heq]
  refine ⟨flip2.contDiff.comp_contDiffOn hB2,?_⟩
  rw [flip2.norm_iteratedFDeriv_comp_left]
  apply (h2 j le_rfl).trans_eq
  rw [pow_add]
  ring

end Bilinear

def actualFastChartTransferPrefix (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), actualFastChartTransferCost T i

theorem actualFastChartTransferPrefix_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFastChartTransferPrefix T j :=
  Finset.sum_nonneg (fun i _ => actualFastChartTransferCost_nonneg T hT i)

theorem actualFastChartTransferCost_le_prefix (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i)
    {i j : ℕ} (hij : i ≤ j) :
    actualFastChartTransferCost T i ≤ actualFastChartTransferPrefix T j :=
  Finset.single_le_sum (fun k _ => actualFastChartTransferCost_nonneg T hT k) (by simpa using hij)

/-- Explicit two-frame transfer constant in the original tensor operator norm. -/
def actualFastTensorChartTransferCost (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  2^(j+j) * actualFastChartTransferPrefix T j * bufferedTransitionPrefix T (j+1)^2

section JointCharts
variable {Ep Es Eq Et Z : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [NormedAddCommGroup Et] [NormedSpace ℝ Et]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The true spatial Jacobian of the actual joint transition. -/
def actualJointSpatialJacobian (phi : Ep × Es → Eq × Et) (z : Ep × Es) : Es →L[ℝ] Et :=
  fderiv ℝ (fun x => (phi (z.1,x)).2) z.2

/-- The spatial frame's fast jets follow from one higher slow transition jet. -/
theorem actual_joint_spatial_jacobian_fast_jets
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (phi : Ep × Es → Eq × Et) (U : Set (Ep × Es)) (hU : IsOpen U)
    (hphi : ContDiffOn ℝ ∞ phi U) (x : Ep × Es) (hx : x ∈ U)
    (tau ell : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell^(i-1) * ‖iteratedFDeriv ℝ i phi x‖ ≤ T i) :
    ContDiffOn ℝ ∞ (actualJointSpatialJacobian phi) U ∧
      ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i (actualJointSpatialJacobian phi) x‖ ≤
        bufferedTransitionPrefix T (j+1) := by
  let P : (Eq × Et) →L[ℝ] Et := ContinuousLinearMap.snd ℝ Eq Et
  have hell : 0 ≤ ell := htau.le.trans htaul
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ Eq Et
  have hs : ContDiffOn ℝ ∞ (P ∘ phi) U := P.contDiff.comp_contDiffOn hphi
  refine ⟨(incrementsJointSpatialJets_bridge (P ∘ phi) U hU hs).2.1,?_⟩
  intro i hi
  have hfirst := spatial_first_jet_le hU hs hx i
  have hpost := P.norm_iteratedFDeriv_comp_left (hphi.contDiffAt (hU.mem_nhds hx))
    (n := i+1) (by simp)
  have hnorm : ‖iteratedFDeriv ℝ i (actualJointSpatialJacobian phi) x‖ ≤
      ‖iteratedFDeriv ℝ (i+1) phi x‖ := by
    apply hfirst.trans (hpost.trans _)
    exact mul_le_of_le_one_left (norm_nonneg _) hP
  have hsum : T (i+1) ≤ ∑ k ∈ Finset.range (j+2), T k :=
    Finset.single_le_sum (fun k _ => hT k) (by simpa using Nat.add_le_add_right hi 1)
  calc
    tau^i * ‖iteratedFDeriv ℝ i (actualJointSpatialJacobian phi) x‖ ≤
        ell^i * ‖iteratedFDeriv ℝ (i+1) phi x‖ :=
      mul_le_mul (pow_le_pow_left₀ htau.le htaul _) hnorm (norm_nonneg _) (pow_nonneg hell i)
    _ ≤ T (i+1) := by simpa only [Nat.add_sub_cancel] using hphijet (i+1) (by omega) (by omega)
    _ ≤ bufferedTransitionPrefix T (j+1) := by unfold bufferedTransitionPrefix; linarith

/-- Genuine tensor pullback with both spatial frame factors and all joint
derivatives. The constant is fixed before every map, atlas and scale. -/
theorem actual_fast_joint_tensor_chart_transfer
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (phi : Ep × Es → Eq × Et) (B : Eq × Et → Et →L[ℝ] Et →L[ℝ] Z)
    (U : Set (Ep × Es)) (V : Set (Eq × Et)) (hU : IsOpen U) (hV : IsOpen V)
    (hphi : ContDiffOn ℝ ∞ phi U) (hB : ContDiffOn ℝ ∞ B V)
    (hmap : MapsTo phi U V) (x : Ep × Es) (hx : x ∈ U)
    (tau ell K : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hK : 0 ≤ K)
    (hBjet : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i B (phi x)‖ ≤ K)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j+1 →
      ell^(i-1) * ‖iteratedFDeriv ℝ i phi x‖ ≤ T i) :
    ContDiffOn ℝ ∞ (fun z => (B (phi z)).bilinearComp
      (actualJointSpatialJacobian phi z) (actualJointSpatialJacobian phi z)) U ∧
    tau^j * ‖iteratedFDeriv ℝ j (fun z => (B (phi z)).bilinearComp
      (actualJointSpatialJacobian phi z) (actualJointSpatialJacobian phi z)) x‖ ≤
        actualFastTensorChartTransferCost T j * K := by
  obtain ⟨hL,hLj⟩ := actual_joint_spatial_jacobian_fast_jets T hT j phi U hU hphi x hx
    tau ell htau htaul hphijet
  have hBj : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i (B ∘ phi) x‖ ≤
      actualFastChartTransferPrefix T j * K := by
    intro i hi
    have h := actual_fast_joint_chart_transfer T hT i phi B U V hU hV hphi hB hmap x hx
      tau ell K htau htaul (fun k hk => hBjet k (hk.trans hi))
      (fun k hk hki => hphijet k hk (by omega))
    exact h.trans (mul_le_mul_of_nonneg_right (actualFastChartTransferCost_le_prefix T hT hi) hK)
  obtain ⟨hc,hb⟩ := actual_bilinear_pullback_slow_jets (B ∘ phi) (actualJointSpatialJacobian phi)
    U hU (hB.comp hphi hmap) hL j tau (actualFastChartTransferPrefix T j * K)
    (bufferedTransitionPrefix T (j+1)) htau.le
    (mul_nonneg (actualFastChartTransferPrefix_nonneg T hT j) hK)
    (zero_le_one.trans (one_le_bufferedTransitionPrefix hT (j+1))) x hx hBj hLj
  refine ⟨hc,hb.trans_eq ?_⟩
  unfold actualFastTensorChartTransferCost
  ring

end JointCharts
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_bilinear_pullback_slow_jets
#print axioms GlobalEmbedding.Continuation.actual_joint_spatial_jacobian_fast_jets
#print axioms GlobalEmbedding.Continuation.actual_fast_joint_tensor_chart_transfer
