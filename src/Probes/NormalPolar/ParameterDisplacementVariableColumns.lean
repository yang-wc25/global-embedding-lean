import Smoothing.WeightedActualGram
import Smoothing.ParameterTransferBounds

/-! A genuine variable parameter in a finite linear column expansion. The
scalar factors are differentiated with their original slow profiles; the
fast column derivatives retain the same tau weights. -/

noncomputable section
open Set Function
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem actual_variable_columns_weighted_jets
    {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ℕ}
    (j : ℕ) (u : Y → Fin p → ℝ) (column : Fin p → Y → V)
    (Omega S : Set Y) (hOmega : IsOpen Omega) (hS : S ⊆ Omega)
    (hu : ContDiffOn ℝ ∞ u Omega) (hcolumn : ∀ q, ContDiffOn ℝ ∞ (column q) Omega)
    (tau ell Ku Kv : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv)
    (hub : ∀ k ≤ j, ∀ y ∈ S, ell^k*‖iteratedFDeriv ℝ k u y‖ ≤ Ku)
    (hcb : ∀ q k, k ≤ j → ∀ y ∈ S, tau^k*‖iteratedFDeriv ℝ k (column q) y‖ ≤ Kv) :
    ContDiffOn ℝ ∞ (fun y => ∑ q, u y q • column q y) Omega ∧
      ∀ k ≤ j, ∀ y ∈ S,
        tau^k*‖iteratedFDeriv ℝ k (fun y => ∑ q, u y q • column q y) y‖ ≤
          ((p : ℝ)*2^j*Ku)*Kv := by
  let proj : Fin p → (Fin p → ℝ) →L[ℝ] ℝ := fun q => ContinuousLinearMap.proj q
  have hpn (q : Fin p) : ‖proj q‖ ≤ 1 := by
    apply (proj q).opNorm_le_bound zero_le_one
    intro v
    simpa only [proj,ContinuousLinearMap.proj_apply,one_mul] using norm_le_pi_norm v q
  have hup (q : Fin p) : ContDiffOn ℝ ∞ (fun y => u y q) Omega :=
    (proj q).contDiff.comp_contDiffOn hu
  have hterm (q : Fin p) : ContDiffOn ℝ ∞ (fun y => u y q • column q y) Omega :=
    (hup q).smul (hcolumn q)
  have hmul : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := V)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
    intro a v
    simp [norm_smul]
  have hupb (q : Fin p) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S) :
      tau^k*‖iteratedFDeriv ℝ k (fun y => u y q) y‖ ≤ Ku := by
    have hp := (proj q).norm_iteratedFDeriv_comp_left
      (hu.contDiffAt (hOmega.mem_nhds (hS hy))) (n := k) (by simp)
    have hn : ‖iteratedFDeriv ℝ k (fun y => u y q) y‖ ≤ ‖iteratedFDeriv ℝ k u y‖ :=
      hp.trans (mul_le_of_le_one_left (norm_nonneg _) (hpn q))
    calc
      _ ≤ tau^k*‖iteratedFDeriv ℝ k u y‖ := mul_le_mul_of_nonneg_left hn (pow_nonneg htau.le k)
      _ ≤ ell^k*‖iteratedFDeriv ℝ k u y‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ htau.le htaul k) (norm_nonneg _)
      _ ≤ Ku := hub k hk y hy
  have htb (q : Fin p) (k : ℕ) (hk : k ≤ j) (y : Y) (hy : y ∈ S) :
      tau^k*‖iteratedFDeriv ℝ k (fun y => u y q • column q y) y‖ ≤ 2^j*Ku*Kv := by
    have hh := slow_bilinear_jet_bound (ContinuousLinearMap.lsmul ℝ ℝ (E := V)) hmul
      Omega hOmega (fun y => u y q) (column q) (hup q) (hcolumn q) k tau Ku Kv htau.le hKu y (hS hy)
      (fun a ha => hupb q a (ha.trans hk) y hy)
      (fun a ha => hcb q a (ha.trans hk) y hy)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk) hKu) hKv)
  refine ⟨ContDiffOn.sum (fun q _ => hterm q),?_⟩
  intro k hk y hy
  rw [iteratedFDeriv_fun_sum_apply
    (fun q _ => ((hterm q).contDiffAt (hOmega.mem_nhds (hS hy))).of_le (by simp))]
  calc
    _ ≤ tau^k * ∑ q, ‖iteratedFDeriv ℝ k (fun y => u y q • column q y) y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg htau.le k)
    _ = ∑ q, tau^k * ‖iteratedFDeriv ℝ k (fun y => u y q • column q y) y‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ _q : Fin p, 2^j*Ku*Kv := Finset.sum_le_sum (fun q _ => htb q k hk y hy)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_variable_columns_weighted_jets
