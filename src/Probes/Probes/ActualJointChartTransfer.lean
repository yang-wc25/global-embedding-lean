import GlobalEmbedding.Offline.BufferedSmoothingJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Fast weighted vector jets through actual joint chart transitions

The transition may mix all parameter and spatial coordinates. Its positive
order jets have the slow scale ell^(i-1). Rescaling both source and target by
the fast scale tau proves the native composition bound without an additional
ell^(-j) loss. All fields, domains and scales follow the explicit profile-only
constant. No chart representatives or derivatives are supplied as substitutes
for the actual composition.
-/

noncomputable section
open GlobalEmbedding.Offline Function Set Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The native dilation identity is local to the actual open domain. -/
theorem actual_iteratedFDeriv_dilation
    (f : X → Y) (O : Set X) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (a : ℝ) (x : X) (hx : a • x ∈ O) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => f (a • y)) x =
      a^j • iteratedFDeriv ℝ j f (a • x) := by
  let L : X →L[ℝ] X := a • ContinuousLinearMap.id ℝ X
  have hxL : L x ∈ O := hx
  have hpre : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hO.uniqueDiffOn hpre.uniqueDiffOn
    hxL (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hpre hxL,
    iteratedFDerivWithin_of_isOpen j hO hxL] at h
  change iteratedFDeriv ℝ j (f ∘ L) x = _
  rw [h]
  ext v
  simpa [L,ContinuousMultilinearMap.compContinuousLinearMap_apply] using
    (iteratedFDeriv ℝ j f (a • x)).map_smul_univ (fun _ : Fin j => a) v

/-- An explicit constant has no field, chart-count, domain or scale argument. -/
def actualFastChartTransferCost (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * bufferedTransitionPrefix T j ^ j

theorem actualFastChartTransferCost_nonneg (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ) :
    0 ≤ actualFastChartTransferCost T j :=
  mul_nonneg (by positivity)
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hT j)) j)

/-- Native weighted vector composition, including all joint parameter directions.
Only the true transition's positive-order jets enter. -/
theorem actual_fast_joint_chart_transfer
    (T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (j : ℕ)
    (phi : X → Y) (f : Y → Z) (U : Set X) (V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V)
    (hphi : ContDiffOn ℝ ∞ phi U) (hf : ContDiffOn ℝ ∞ f V)
    (hmap : MapsTo phi U V) (x : X) (hx : x ∈ U)
    (tau ell K : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell)
    (hfjet : ∀ i ≤ j, tau^i * ‖iteratedFDeriv ℝ i f (phi x)‖ ≤ K)
    (hphijet : ∀ i, 1 ≤ i → i ≤ j →
      ell^(i-1) * ‖iteratedFDeriv ℝ i phi x‖ ≤ T i) :
    tau^j * ‖iteratedFDeriv ℝ j (f ∘ phi) x‖ ≤ actualFastChartTransferCost T j * K := by
  let LX : X →L[ℝ] X := tau • ContinuousLinearMap.id ℝ X
  let LY : Y →L[ℝ] Y := tau • ContinuousLinearMap.id ℝ Y
  let U' := LX ⁻¹' U
  let V' := LY ⁻¹' V
  let phi' : X → Y := fun y => tau⁻¹ • phi (tau • y)
  let f' : Y → Z := fun y => f (tau • y)
  let x' := tau⁻¹ • x
  have htau0 := htau.ne'
  have hU' : IsOpen U' := hU.preimage LX.continuous
  have hV' : IsOpen V' := hV.preimage LY.continuous
  have hxx : tau • x' = x := smul_inv_smul₀ htau0 x
  have hx' : x' ∈ U' := by
    change tau • x' ∈ U
    rw [hxx]
    exact hx
  have hphiscaled : ContDiffOn ℝ ∞ (fun y : X => phi (tau • y)) U' :=
    hphi.comp_continuousLinearMap LX
  have hphi' : ContDiffOn ℝ ∞ phi' U' := hphiscaled.const_smul tau⁻¹
  have hf' : ContDiffOn ℝ ∞ f' V' := hf.comp_continuousLinearMap LY
  have hmap' : MapsTo phi' U' V' := by
    intro y hy
    change tau • (tau⁻¹ • phi (tau • y)) ∈ V
    rw [smul_inv_smul₀ htau0]
    exact hmap hy
  have hphix : tau • phi' x' = phi x := by
    dsimp only [phi']
    rw [smul_inv_smul₀ htau0,hxx]
  have hout (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i f' V' (phi' x')‖ ≤ K := by
    rw [iteratedFDerivWithin_of_isOpen i hV' (hmap' hx')]
    change ‖iteratedFDeriv ℝ i (fun y => f (tau • y)) (phi' x')‖ ≤ K
    rw [actual_iteratedFDeriv_dilation f V hV hf tau (phi' x') (by rw [hphix]; exact hmap hx) i,
      norm_smul,Real.norm_eq_abs,abs_pow,abs_of_pos htau,hphix]
    exact hfjet i hi
  have hin (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i phi' U' x'‖ ≤ bufferedTransitionPrefix T j ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hU' hx']
    have hscaled := (hphiscaled.contDiffAt (hU'.mem_nhds hx')).of_le
      (by simp : (i : ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ i (fun y : X => tau⁻¹ • phi (tau • y)) x'‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hscaled,
      actual_iteratedFDeriv_dilation phi U hU hphi tau x' (by rw [hxx]; exact hx) i,
      norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr htau),abs_pow,abs_of_pos htau,hxx]
    have hpow : tau⁻¹ * tau^i = tau^(i-1) := by
      obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      simp only [Nat.succ_sub_one,pow_succ]
      field_simp [htau0]
    have hsum : T i ≤ ∑ l ∈ Finset.range (j+1), T l :=
      Finset.single_le_sum (fun l _ => hT l) (by simpa using hij)
    have hTQ : T i ≤ bufferedTransitionPrefix T j := by
      unfold bufferedTransitionPrefix
      linarith
    calc
      tau⁻¹ * (tau^i * ‖iteratedFDeriv ℝ i phi x‖) =
          tau^(i-1) * ‖iteratedFDeriv ℝ i phi x‖ := by rw [← mul_assoc,hpow]
      _ ≤ ell^(i-1) * ‖iteratedFDeriv ℝ i phi x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ htau.le htaul _) (norm_nonneg _)
      _ ≤ T i := hphijet i hi hij
      _ ≤ bufferedTransitionPrefix T j ^ i := hTQ.trans
        (le_self_pow₀ (one_le_bufferedTransitionPrefix hT j) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le hf' hphi' (n := j) (by simp)
    hV'.uniqueDiffOn hU'.uniqueDiffOn hmap' hx' hout hin
  rw [iteratedFDerivWithin_of_isOpen j hU' hx'] at hcomp
  have heq : f' ∘ phi' = fun y => (f ∘ phi) (tau • y) := by
    funext y
    simp only [Function.comp_def,f',phi',smul_inv_smul₀ htau0]
  rw [heq,actual_iteratedFDeriv_dilation (f ∘ phi) U hU (hf.comp hphi hmap)
    tau x' (by rw [hxx]; exact hx) j,norm_smul,Real.norm_eq_abs,abs_pow,abs_of_pos htau,hxx] at hcomp
  exact hcomp.trans_eq (by unfold actualFastChartTransferCost; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_iteratedFDeriv_dilation
#print axioms GlobalEmbedding.Continuation.actual_fast_joint_chart_transfer
