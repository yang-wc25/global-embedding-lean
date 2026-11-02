import Probes.ActualPhaseEuclideanTransport

/-!
# One quantitative adapted chart in the original native Euclidean model

The direction is chosen from the original spatial differential, not supplied.
The actual chart and its inverse preserve parameters and realize the original
phase as coordinate zero. The chart is chosen using only C1/C2 data and works
for every higher observation order. All norm conversion factors are explicit.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [CompleteSpace Ep]
  {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Y" => Ep × (ℝ × EuclideanSpace ℝ (Fin m))
local notation "X" => Ep × D

private def nativeConjugatedPhaseChart (C J : X ≃L[ℝ] Y)
    (b : OpenPartialHomeomorph Y Y) : OpenPartialHomeomorph X X where
  toFun := fun x => J.symm (b (C x))
  invFun := fun y => C.symm (b.symm (J y))
  source := C ⁻¹' b.source
  target := J ⁻¹' b.target
  map_source' := by intro x hx; change J (J.symm (b (C x))) ∈ b.target; simpa using b.map_source hx
  map_target' := by intro y hy; change C (C.symm (b.symm (J y))) ∈ b.source; simpa using b.map_target hy
  left_inv' := by intro x hx; simp only [J.apply_symm_apply,b.left_inv hx,C.symm_apply_apply]
  right_inv' := by intro y hy; simp only [C.apply_symm_apply,b.right_inv hy,J.symm_apply_apply]
  open_source := b.open_source.preimage C.continuous
  open_target := b.open_target.preimage J.continuous
  continuousOn_toFun := J.symm.continuous.comp_continuousOn
    (b.continuousOn.comp C.continuous.continuousOn (fun _ hx => hx))
  continuousOn_invFun := C.symm.continuous.comp_continuousOn
    (b.symm.continuousOn.comp J.continuous.continuousOn (fun _ hy => hy))

omit [CompleteSpace Ep] in
private theorem oriented_phase_scaled_jet
    (R : D ≃ₗᵢ[ℝ] D) (psi : X → ℝ) (ell : ℝ) (hell : 0 ≤ ell) (i : ℕ) (y : Y) :
    (ell/2)^i * ‖iteratedFDeriv ℝ (i+1)
      (psi ∘ (actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm) y‖ ≤
      2*(ell^i * ‖iteratedFDeriv ℝ (i+1) psi
        ((actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm y)‖) := by
  let C := actualJointEuclideanPhaseEquiv (Ep := Ep) R
  have hn := actual_linear_equiv_precomposition_jet_bound C.symm psi (i+1) y
  have hn2 : ‖iteratedFDeriv ℝ (i+1) (psi ∘ C.symm) y‖ ≤
      ‖iteratedFDeriv ℝ (i+1) psi (C.symm y)‖*2^(i+1) := by
    apply hn.trans
    gcongr
    exact actualJointEuclideanPhaseEquiv_symm_norm R
  have hpow : (ell/2)^i*2^i = ell^i := by rw [← mul_pow]; congr 1; ring
  calc
    _ ≤ (ell/2)^i*(‖iteratedFDeriv ℝ (i+1) psi (C.symm y)‖*2^(i+1)) :=
      mul_le_mul_of_nonneg_left hn2 (pow_nonneg (div_nonneg hell (by norm_num)) i)
    _ = 2*((ell/2)^i*2^i)*‖iteratedFDeriv ℝ (i+1) psi (C.symm y)‖ := by rw [pow_succ]; ring
    _ = _ := by rw [hpow]; ring

def actualEuclideanPhaseRadius (mu M ell : ℝ) : ℝ :=
  (ell/2)/(4*actualPhaseInverseConstant mu (2*M)*(1+2*M))

def actualEuclideanPhaseInverseJetCost (mu M Mj : ℝ) (j : ℕ) : ℝ :=
  2^(j+1)*actualInverseChartMajorant
    (slowInverseMajorant (2*actualPhaseInverseConstant mu (2*M)) (2*Mj) j) j

theorem actual_exists_native_euclidean_quantitative_phase_chart_pointwise_forward
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M ell) ⊆ a.source ∧
      a.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M ell)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ i, 1 ≤ i → ∀ x ∈ a.source,
        ‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(i+2)*‖iteratedFDeriv ℝ (i+1) psi x‖) ∧
      (∀ x ∈ a.source, ‖fderiv ℝ a x‖ ≤ 2*(1+2*M)) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
          weight^i*‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(j+2)*Mj) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  let d := (fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)
  have hd : d ≠ 0 := norm_pos_iff.mp (hmu.trans_le hspatial)
  obtain ⟨R,hR⟩ := actual_exists_phase_orientation m d hd
  let C := actualJointEuclideanPhaseEquiv (Ep := Ep) R
  let J := actualJointEuclideanPhaseEquiv (Ep := Ep) (LinearIsometryEquiv.refl ℝ D)
  let Psi : Y → ℝ := psi ∘ C.symm
  have hhalf : 0 < ell/2 := by positivity
  have hmap : MapsTo C.symm (ball (C z0) (ell/2)) (ball z0 ell) :=
    fun y hy => actualJointEuclideanPhaseEquiv_inverse_ball R z0 ell y hy
  have hPsi : ContDiffOn ℝ ∞ Psi (ball (C z0) (ell/2)) :=
    hpsi.comp C.symm.contDiff.contDiffOn hmap
  have hPfirst : ∀ y ∈ ball (C z0) (ell/2), ‖fderiv ℝ Psi y‖ ≤ 2*M := by
    intro y hy
    have hn := oriented_phase_scaled_jet R psi ell hell.le 0 y
    simp only [pow_zero,one_mul] at hn
    change ‖iteratedFDeriv ℝ 1 Psi y‖ ≤ 2*‖iteratedFDeriv ℝ 1 psi (C.symm y)‖ at hn
    rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (hfirst (C.symm y) (hmap hy)) (by norm_num))
  have hPsecond : ∀ y ∈ ball (C z0) (ell/2), (ell/2)*‖iteratedFDeriv ℝ 2 Psi y‖ ≤ 2*M := by
    intro y hy
    have hn := oriented_phase_scaled_jet R psi ell hell.le 1 y
    simp only [pow_one] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (hsecond (C.symm y) (hmap hy)) (by norm_num))
  have haxis : mu ≤ |fderiv ℝ Psi (C z0) (0,(1,0))| := by
    have hp := ((hpsi.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hell))).differentiableAt
      (by simp)).hasFDerivAt
    have hc : HasFDerivAt Psi ((fderiv ℝ psi z0).comp (C.symm : Y →L[ℝ] X)) (C z0) := by
      have hp' : HasFDerivAt psi (fderiv ℝ psi z0) (C.symm (C z0)) := by
        simpa only [C.symm_apply_apply] using hp
      exact hp'.comp (C z0) C.symm.hasFDerivAt
    rw [hc.fderiv]
    have he : C.symm (0,(1,0)) = (0,R (EuclideanSpace.single 0 1)) := by
      refine Prod.ext rfl ?_
      rw [actualJointEuclideanPhaseEquiv_symm_snd,actualEuclideanPhaseEquiv_symm_axis]
    change mu ≤ |fderiv ℝ psi z0 (C.symm (0,(1,0)))|
    rw [he]
    change mu ≤ |d (R (EuclideanSpace.single 0 1))|
    rw [hR,abs_of_nonneg (norm_nonneg _)]
    exact hspatial
  obtain ⟨b,hbs,hbf,hb,hbi,hbid,hbt,_hbfirst,hbj⟩ :=
    actual_exists_uniform_quantitative_phase_chart_all_scales mu (2*M) hmu (by positivity)
      Psi (C z0) (ell/2) hhalf hPsi haxis hPfirst hPsecond
  let a := nativeConjugatedPhaseChart C J b
  let r := actualEuclideanPhaseRadius mu M ell
  have hB : 1 ≤ actualPhaseInverseConstant mu (2*M) :=
    actualPhaseInverseConstant_one_le hmu (by positivity)
  have hrle : r ≤ ell/2 := by
    have hdpos : 0 < 4*actualPhaseInverseConstant mu (2*M)*(1+2*M) := by positivity
    apply (div_le_iff₀ hdpos).mpr
    have hd1 : 1 ≤ 4*actualPhaseInverseConstant mu (2*M)*(1+2*M) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd1 hhalf.le]
  have hasource (x : X) : x ∈ a.source ↔ C x ∈ ball (C z0) r := by
    change C x ∈ b.source ↔ _
    rw [hbs]
    rfl
  have hinner : ball z0 r ⊆ a.source := by
    intro x hx
    rw [hasource,mem_ball,dist_eq_norm]
    have hn := C.toContinuousLinearMap.le_of_opNorm_le (actualJointEuclideanPhaseEquiv_norm R) (x-z0)
    change ‖C (x-z0)‖ ≤ 1*‖x-z0‖ at hn
    rw [map_sub,one_mul] at hn
    exact hn.trans_lt (by simpa only [mem_ball,dist_eq_norm] using hx)
  have houter : a.source ⊆ ball z0 ell := by
    intro x hx
    have hcball := (ball_subset_ball hrle) ((hasource x).mp hx)
    have hi := hmap hcball
    simpa only [C.symm_apply_apply] using hi
  have hAs : ContDiffOn ℝ ∞ a a.source :=
    J.symm.contDiff.comp_contDiffOn (hb.comp C.contDiff.contDiffOn (fun _ hx => hx))
  have hAis : ContDiffOn ℝ ∞ a.symm a.target :=
    C.symm.contDiff.comp_contDiffOn (hbi.comp J.contDiff.contDiffOn (fun _ hx => hx))
  have hforwardNorm : ∀ x ∈ a.source, ‖fderiv ℝ a x‖ ≤ 2*(1+2*M) := by
    intro x hx
    have hCx : C x ∈ ball (C z0) (ell/2) := (ball_subset_ball hrle) ((hasource x).mp hx)
    have hDb : ‖fderiv ℝ b (C x)‖ ≤ 1+2*M := by
      rw [hbf,(actual_phase_coordinate_hasFDerivAt Psi (C x)
        ((hPsi.contDiffAt (isOpen_ball.mem_nhds hCx)).differentiableAt (by simp))).fderiv]
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      change ‖(v.1,(fderiv ℝ Psi (C x) v,v.2.2))‖ ≤ (1+2*M)*‖v‖
      rw [Prod.norm_def,Prod.norm_def]
      have hbase : ‖v‖ ≤ (1+2*M)*‖v‖ := by nlinarith [norm_nonneg v]
      have hdv := (fderiv ℝ Psi (C x)).le_opNorm v
      have hdM := hPfirst (C x) hCx
      have hdv' : ‖fderiv ℝ Psi (C x) v‖ ≤ (1+2*M)*‖v‖ :=
        hdv.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      exact max_le ((norm_fst_le v).trans hbase)
        (max_le hdv' (((norm_snd_le v.2).trans (norm_snd_le v)).trans hbase))
    have hpre := actual_linear_equiv_precomposition_jet_bound C b 1 x
    have hpost := actual_linear_equiv_postcomposition_jet_bound J.symm (b ∘ C) 1 x
    rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one,pow_one] at hpre
    rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at hpost
    change ‖fderiv ℝ a x‖ ≤ _ at hpost
    calc
      _ ≤ ‖(J.symm : Y →L[ℝ] X)‖*‖fderiv ℝ (b ∘ C) x‖ := hpost
      _ ≤ 2*(‖fderiv ℝ b (C x)‖*1) := by
        apply mul_le_mul (actualJointEuclideanPhaseEquiv_symm_norm (LinearIsometryEquiv.refl ℝ D))
          (hpre.trans (mul_le_mul_of_nonneg_left (actualJointEuclideanPhaseEquiv_norm R) (norm_nonneg _)))
          (norm_nonneg _) (by norm_num)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hDb (by norm_num : (0:ℝ) ≤ 2)
  have hforwardPointwise : ∀ i, 1 ≤ i → ∀ x ∈ a.source,
      ‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(i+2)*‖iteratedFDeriv ℝ (i+1) psi x‖ := by
    intro i hi x hx
    have hCx : C x ∈ ball (C z0) (ell/2) := (ball_subset_ball hrle) ((hasource x).mp hx)
    have hbjet : ‖iteratedFDeriv ℝ (i+1) b (C x)‖ = ‖iteratedFDeriv ℝ (i+1) Psi (C x)‖ := by
      rw [hbf,actual_phase_coordinate_higher_jet_norm Psi (C x)
        (hPsi.contDiffAt (isOpen_ball.mem_nhds hCx)) i hi]
    have hpre := actual_linear_equiv_precomposition_jet_bound C b (i+1) x
    have hpost := actual_linear_equiv_postcomposition_jet_bound J.symm (b ∘ C) (i+1) x
    have hpsipre := actual_linear_equiv_precomposition_jet_bound C.symm psi (i+1) (C x)
    rw [C.symm_apply_apply] at hpsipre
    calc
      _ ≤ ‖(J.symm : Y →L[ℝ] X)‖*‖iteratedFDeriv ℝ (i+1) (b ∘ C) x‖ := hpost
      _ ≤ 2*(‖iteratedFDeriv ℝ (i+1) b (C x)‖*1^(i+1)) := by
        apply mul_le_mul (actualJointEuclideanPhaseEquiv_symm_norm (LinearIsometryEquiv.refl ℝ D))
          (hpre.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (actualJointEuclideanPhaseEquiv_norm R) (i+1))
            (norm_nonneg _))) (norm_nonneg _) (by norm_num)
      _ = 2*‖iteratedFDeriv ℝ (i+1) Psi (C x)‖ := by rw [hbjet,one_pow,mul_one]
      _ ≤ 2*(‖iteratedFDeriv ℝ (i+1) psi x‖*2^(i+1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hpsipre.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (actualJointEuclideanPhaseEquiv_symm_norm R) (i+1))
          (norm_nonneg _))
      _ = _ := by rw [pow_succ]; ring
  have hforwardHigher : ∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
      (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
        weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
      ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
        weight^i*‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(j+2)*Mj := by
    intro j weight Mj hweight hMj hjet i hi hij x hx
    have hbnd := hforwardPointwise i hi x hx
    calc
      _ ≤ weight^i*(2^(i+2)*‖iteratedFDeriv ℝ (i+1) psi x‖) :=
        mul_le_mul_of_nonneg_left hbnd (pow_nonneg hweight.le i)
      _ = 2^(i+2)*(weight^i*‖iteratedFDeriv ℝ (i+1) psi x‖) := by ring
      _ ≤ 2^(i+2)*Mj := mul_le_mul_of_nonneg_left (hjet i hi hij x (houter hx)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hMj
  have hJzero (w : Y) : (J.symm w).2 0 = w.2.1 := actualEuclideanPhaseEquiv_symm_zero m w.2
  have hforward (x : X) : (a x).1 = x.1 ∧ (a x).2 0 = psi x := by
    change (J.symm (b (C x))).1 = x.1 ∧ (J.symm (b (C x))).2 0 = psi x
    rw [actualJointEuclideanPhaseEquiv_symm_fst,hJzero,hbf]
    change (C x).1 = x.1 ∧ psi (C.symm (C x)) = psi x
    rw [C.symm_apply_apply]
    exact ⟨rfl,rfl⟩
  refine ⟨a,hinner,houter,hAs,hAis,fun x _ => hforward x,?_,?_,hforwardPointwise,hforwardNorm,hforwardHigher,?_⟩
  · intro y hy
    have he := hforward (a.symm y)
    rw [a.right_inv hy] at he
    exact ⟨he.1.symm,he.2.symm⟩
  · intro y hy
    change J y ∈ b.target
    apply hbt
    have hn := J.toContinuousLinearMap.le_of_opNorm_le
      (actualJointEuclideanPhaseEquiv_norm (LinearIsometryEquiv.refl ℝ D)) (y-a z0)
    change ‖J (y-a z0)‖ ≤ 1*‖y-a z0‖ at hn
    rw [map_sub,one_mul] at hn
    have hc : J (a z0) = actualPhaseCoordinateMap Psi (C z0) := by
      change J (J.symm (b (C z0))) = _
      rw [J.apply_symm_apply,hbf]
    rw [hc] at hn
    rw [mem_closedBall,dist_eq_norm]
    rw [mem_closedBall,dist_eq_norm] at hy
    have hbnd : ‖J y-actualPhaseCoordinateMap Psi (C z0)‖ ≤
        actualEuclideanPhaseRadius mu M ell/(4*actualPhaseInverseConstant mu (2*M)) := hn.trans hy
    exact hbnd
  · intro j weight Mj hweight hMj hjet k hk hkj y hy
    have hPjet : ∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball (C z0) (ell/2),
        (weight/2)^i*‖iteratedFDeriv ℝ (i+1) Psi z‖ ≤ 2*Mj := by
      intro i hi hij z hz
      exact (oriented_phase_scaled_jet R psi weight hweight.le i z).trans
        (mul_le_mul_of_nonneg_left (hjet i hi hij (C.symm z) (hmap hz)) (by norm_num))
    have hbjet := hbj j (weight/2) (2*Mj) (by positivity) (by positivity) hPjet k hk hkj (J y) hy
    let G : X → Y := b.symm ∘ J
    have hn1 := actual_linear_equiv_postcomposition_jet_bound C.symm G k y
    have hn2 := actual_linear_equiv_precomposition_jet_bound J b.symm k y
    have hn : ‖iteratedFDeriv ℝ k a.symm y‖ ≤ 2*‖iteratedFDeriv ℝ k b.symm (J y)‖ := by
      apply hn1.trans
      calc
        _ ≤ 2*(‖iteratedFDeriv ℝ k b.symm (J y)‖*1^k) := by
          apply mul_le_mul (actualJointEuclideanPhaseEquiv_symm_norm R) _ (norm_nonneg _) (by norm_num)
          exact hn2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
            (actualJointEuclideanPhaseEquiv_norm (LinearIsometryEquiv.refl ℝ D)) k) (norm_nonneg _))
        _ = _ := by simp
    have hpow : weight^(k-1)*2 = 2^k*(weight/2)^(k-1) := by
      obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp only [Nat.succ_sub_one,pow_succ]
      have he : (2:ℝ)^s*(weight/2)^s = weight^s := by rw [← mul_pow]; congr 1; ring
      calc
        _ = 2*((2:ℝ)^s*(weight/2)^s) := by rw [he]; ring
        _ = _ := by ring
    calc
      _ ≤ weight^(k-1)*(2*‖iteratedFDeriv ℝ k b.symm (J y)‖) :=
        mul_le_mul_of_nonneg_left hn (pow_nonneg hweight.le _)
      _ = 2^k*((weight/2)^(k-1)*‖iteratedFDeriv ℝ k b.symm (J y)‖) := by rw [← mul_assoc,hpow]; ring
      _ ≤ 2^k*actualInverseChartMajorant
          (slowInverseMajorant (2*actualPhaseInverseConstant mu (2*M)) (2*Mj) j) j :=
        mul_le_mul_of_nonneg_left hbjet (by positivity)
      _ ≤ actualEuclideanPhaseInverseJetCost mu M Mj j := by
        apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hkj)
        exact zero_le_one.trans (actualInverseChartMajorant_one_le
          (slowInverseMajorant_nonneg (by positivity) (by positivity) j) j)


theorem actual_exists_native_euclidean_quantitative_phase_chart_full_jets
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M ell) ⊆ a.source ∧
      a.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M ell)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ x ∈ a.source, ‖fderiv ℝ a x‖ ≤ 2*(1+2*M)) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ i, 1 ≤ i → i ≤ j → ∀ x ∈ a.source,
          weight^i*‖iteratedFDeriv ℝ (i+1) a x‖ ≤ 2^(j+2)*Mj) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨a,hi,ho,hs,his,hp,hpi,ht,_hpoint,hfirst,hforward,hinverse⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_pointwise_forward mu M hmu hM
      psi z0 ell hell hpsi hspatial hfirst hsecond
  exact ⟨a,hi,ho,hs,his,hp,hpi,ht,hfirst,hforward,hinverse⟩

/-- The first forward bound and all inverse jets of the same chart. -/
theorem actual_exists_native_euclidean_quantitative_phase_chart_with_forward_bound
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M ell) ⊆ a.source ∧
      a.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M ell)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ x ∈ a.source, ‖fderiv ℝ a x‖ ≤ 2*(1+2*M)) ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨a,hi,ho,hs,his,hf,hb,ht,hfwd,_hforward,hj⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_full_jets mu M hmu hM
      psi z0 ell hell hpsi hspatial hfirst hsecond
  exact ⟨a,hi,ho,hs,his,hf,hb,ht,hfwd,hj⟩

/-- Every later weight is estimated on the same chosen chart. -/
theorem actual_exists_native_euclidean_quantitative_phase_chart_all_scales
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M ell) ⊆ a.source ∧
      a.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M ell)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ (j : ℕ) (weight Mj : ℝ), 0 < weight → 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          weight^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨a,hi,ho,hs,his,hf,hb,ht,_hfwd,hj⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_with_forward_bound mu M hmu hM
      psi z0 ell hell hpsi hspatial hfirst hsecond
  exact ⟨a,hi,ho,hs,his,hf,hb,ht,hj⟩

/-- Construction-scale specialization, preserving the original interface. -/
theorem actual_exists_native_euclidean_quantitative_phase_chart
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (psi : X → ℝ) (z0 : X) (ell : ℝ) (hell : 0 < ell)
    (hpsi : ContDiffOn ℝ ∞ psi (ball z0 ell))
    (hspatial : mu ≤ ‖(fderiv ℝ psi z0).comp (ContinuousLinearMap.inr ℝ Ep D)‖)
    (hfirst : ∀ z ∈ ball z0 ell, ‖fderiv ℝ psi z‖ ≤ M)
    (hsecond : ∀ z ∈ ball z0 ell, ell*‖iteratedFDeriv ℝ 2 psi z‖ ≤ M) :
    ∃ a : OpenPartialHomeomorph X X,
      ball z0 (actualEuclideanPhaseRadius mu M ell) ⊆ a.source ∧
      a.source ⊆ ball z0 ell ∧
      ContDiffOn ℝ ∞ a a.source ∧ ContDiffOn ℝ ∞ a.symm a.target ∧
      (∀ z ∈ a.source, (a z).1 = z.1 ∧ (a z).2 0 = psi z) ∧
      (∀ z ∈ a.target, (a.symm z).1 = z.1 ∧ psi (a.symm z) = z.2 0) ∧
      closedBall (a z0) ((actualEuclideanPhaseRadius mu M ell)/
        (4*actualPhaseInverseConstant mu (2*M))) ⊆ a.target ∧
      (∀ (j : ℕ) (Mj : ℝ), 0 ≤ Mj →
        (∀ i, 1 ≤ i → i ≤ j → ∀ z ∈ ball z0 ell,
          ell^i*‖iteratedFDeriv ℝ (i+1) psi z‖ ≤ Mj) →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ y ∈ a.target,
          ell^(k-1)*‖iteratedFDeriv ℝ k a.symm y‖ ≤
            actualEuclideanPhaseInverseJetCost mu M Mj j) := by
  obtain ⟨a,hi,ho,hs,his,hf,hb,ht,hj⟩ :=
    actual_exists_native_euclidean_quantitative_phase_chart_all_scales mu M hmu hM
      psi z0 ell hell hpsi hspatial hfirst hsecond
  exact ⟨a,hi,ho,hs,his,hf,hb,ht,
    fun j Mj hMj hjet => hj j ell Mj hell hMj hjet⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart_all_scales

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart_with_forward_bound

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart_full_jets

#print axioms GlobalEmbedding.Continuation.actual_exists_native_euclidean_quantitative_phase_chart_pointwise_forward
