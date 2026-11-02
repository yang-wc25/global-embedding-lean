import Smoothing.ParameterRound2UniformMeanReserve

/-!
# Two-parameter stability of finite substitutions on a common genuine reserve

The space is only an additive real module equipped with its original seminorms;
no Banach or finite-dimensional model of tensor fields is introduced. A fixed
finite threshold guarantees that every iterate stays in the same C0 reserve.
The actual tame operator difference then propagates the quadratic probe
parameter difference, with finite derivative loss and no Hessian assumption.
The canonical original mean operator is instantiated in the downstream adapter.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation

variable {V P : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def round4ProbeReserveProfile (B0 Pb : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,s => B0 s
  | i+1,s => B0 s+Pb s+max 0 (C s (round4ProbeReserveProfile B0 Pb C loss i (s+loss)))

def round4ProbeReserveThreshold (B0 Pb : ℕ → ℝ) (C : ℕ → ℝ → ℝ)
    (rho : ℝ) (q loss : ℕ) : ℝ :=
  min 1 (rho/(4*(1+∑ i ∈ Finset.range q,
    max 0 (C 0 (round4ProbeReserveProfile B0 Pb C loss i loss)))))

def round4ProbeReserveIterate (p : ℕ → Seminorm ℝ V) (H : V) (rho : ℝ)
    (T : {A : V // p 0 (A-H) < rho} → V) (probe : P → V) : ℕ → P → V
  | 0 => fun _ => H
  | i+1 => fun u => H-probe u-
      if h : p 0 (round4ProbeReserveIterate p H rho T probe i u-H) < rho then
        T ⟨round4ProbeReserveIterate p H rho T probe i u,h⟩ else 0

theorem round4ProbeReserveThreshold_pos (B0 Pb : ℕ → ℝ) (C : ℕ → ℝ → ℝ)
    {rho : ℝ} (hrho : 0 < rho) (q loss : ℕ) :
    0 < round4ProbeReserveThreshold B0 Pb C rho q loss ∧
      round4ProbeReserveThreshold B0 Pb C rho q loss ≤ 1 := by
  refine ⟨lt_min zero_lt_one ?_,min_le_left _ _⟩
  apply div_pos hrho
  have hs : 0 ≤ ∑ i ∈ Finset.range q,
      max 0 (C 0 (round4ProbeReserveProfile B0 Pb C loss i loss)) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  positivity

def round4ProbeDifferenceProfile (Pd : ℕ → ℝ) (Cd : ℕ → ℕ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,_ => 0
  | i+1,s => Pd s+Cd i s*round4ProbeDifferenceProfile Pd Cd loss i (s+loss)

theorem round4ProbeDifferenceProfile_nonneg (Pd : ℕ → ℝ) (Cd : ℕ → ℕ → ℝ) (loss : ℕ)
    (hPd : ∀ s, 0 ≤ Pd s) (hCd : ∀ i s, 0 ≤ Cd i s) (i s : ℕ) :
    0 ≤ round4ProbeDifferenceProfile Pd Cd loss i s := by
  induction i generalizing s with
  | zero => exact le_rfl
  | succ i ih => exact add_nonneg (hPd s) (mul_nonneg (hCd i s) (ih (s+loss)))

theorem round4_probe_common_reserve_profiles
    (p : ℕ → Seminorm ℝ V) (H : V) (rho : ℝ) (hrho : 0 < rho)
    (B0 Pb : ℕ → ℝ) (Csize : ℕ → ℝ → ℝ) (q loss : ℕ)
    (U : Set P) (probe : P → V)
    (hH : ∀ s, p s H ≤ B0 s)
    (hPb : ∀ u ∈ U, ∀ s, p s (probe u) ≤ Pb s) (hPb0 : Pb 0 ≤ rho/4)
    (epsilon : ℝ) (he : 0 < epsilon)
    (he0 : epsilon < round4ProbeReserveThreshold B0 Pb Csize rho q loss)
    (T : {A : V // p 0 (A-H) < rho} → V)
    (hsize : ∀ s R (A : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p s (T A) ≤ epsilon*Csize s R) :
    let A := round4ProbeReserveIterate p H rho T probe
    let R := round4ProbeReserveProfile B0 Pb Csize loss
    (∀ i ≤ q, ∀ u ∈ U, p 0 (A i u-H) < rho) ∧
      (∀ i ≤ q, ∀ u ∈ U, ∀ s, p s (A i u) ≤ R i s) := by
  intro A R
  let Csum := 1+∑ i ∈ Finset.range q, max 0 (Csize 0 (R i loss))
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range q, max 0 (Csize 0 (R i loss)) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hsum : 0 < Csum := by dsimp only [Csum]; linarith
  have he1 : epsilon ≤ 1 := he0.le.trans (min_le_left _ _)
  have heSmall : epsilon*Csum < rho/4 := by
    have hh : epsilon < rho/(4*Csum) := he0.trans_le (min_le_right _ _)
    apply (mul_lt_mul_iff_right₀ (by norm_num : (0:ℝ)<4)).mp
    have hm := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hsum)).mp hh
    nlinarith
  have hall : ∀ i ≤ q, ∀ u ∈ U, p 0 (A i u-H) < rho ∧ ∀ s, p s (A i u) ≤ R i s := by
    intro i
    induction i with
    | zero =>
      intro hi u hu
      constructor
      · simpa [A,round4ProbeReserveIterate] using hrho
      · exact hH
    | succ i ih =>
      intro hi u hu
      obtain ⟨hdom,hprof⟩ := ih (by omega) u hu
      let Ai : {A : V // p 0 (A-H) < rho} := ⟨A i u,hdom⟩
      have hstep : A (i+1) u = H-probe u-T Ai := by
        change H-probe u-(if h : p 0 (A i u-H)<rho then T ⟨A i u,h⟩ else 0) = _
        simp only [dite_eq_left hdom]
        rfl
      have hT (s : ℕ) := hsize s (R i (s+loss)) Ai (hprof (s+loss))
      have hc : max 0 (Csize 0 (R i loss)) ≤ Csum := by
        have hmem : i ∈ Finset.range q := Finset.mem_range.mpr (by omega)
        have hsone : max 0 (Csize 0 (R i loss)) ≤
            ∑ a ∈ Finset.range q, max 0 (Csize 0 (R a loss)) :=
          Finset.single_le_sum (f := fun a => max 0 (Csize 0 (R a loss)))
            (fun _ _ => le_max_left _ _) hmem
        exact hsone.trans (by dsimp only [Csum]; linarith)
      constructor
      · rw [hstep]
        have heq : H-probe u-T Ai-H = -(probe u)-T Ai := by abel
        rw [heq]
        calc
          _ ≤ p 0 (probe u)+p 0 (T Ai) := by simpa only [map_neg_eq_map] using map_sub_le_add (p 0) (-probe u) (T Ai)
          _ ≤ Pb 0+epsilon*Csize 0 (R i loss) := add_le_add (hPb u hu 0) (by simpa using hT 0)
          _ ≤ Pb 0+epsilon*max 0 (Csize 0 (R i loss)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right _ _) he.le)
          _ ≤ rho/4+epsilon*Csum := add_le_add hPb0 (mul_le_mul_of_nonneg_left hc he.le)
          _ < rho := by linarith
      · intro s
        rw [hstep]
        calc
          _ ≤ p s H+p s (probe u)+p s (T Ai) :=
            (map_sub_le_add _ _ _).trans (add_le_add (map_sub_le_add _ _ _) le_rfl)
          _ ≤ B0 s+Pb s+epsilon*Csize s (R i (s+loss)) :=
            add_le_add (add_le_add (hH s) (hPb u hu s)) (hT s)
          _ ≤ B0 s+Pb s+epsilon*max 0 (Csize s (R i (s+loss))) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right _ _) he.le)
          _ ≤ B0 s+Pb s+max 0 (Csize s (R i (s+loss))) :=
            add_le_add le_rfl (by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right he1 (le_max_left 0 _))
          _ = R (i+1) s := rfl
  exact ⟨fun i hi u hu => (hall i hi u hu).1,fun i hi u hu => (hall i hi u hu).2⟩


/-- A genuine quadratic probe difference propagates through every finite
substitution using the same common reserve and the operator's tame difference.
No response or Hessian of the resulting iterates is assumed. -/
theorem round4_probe_finite_tame_parameter_difference
    (p : ℕ → Seminorm ℝ V) (H : V) (rho : ℝ) (hrho : 0 < rho)
    (B0 Pb Pd : ℕ → ℝ) (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ)
    (U : Set P) (probe : P → V)
    (hH : ∀ s, p s H ≤ B0 s)
    (hPb : ∀ u ∈ U, ∀ s, p s (probe u) ≤ Pb s) (hPb0 : Pb 0 ≤ rho/4)
    (hPd : ∀ s, 0 ≤ Pd s)
    (hPdiff : ∀ u ∈ U, ∀ v ∈ U, ∀ s,
      p s (probe u-probe v) ≤ Pd s*(‖u‖+‖v‖)*‖u-v‖)
    (epsilon : ℝ) (he : 0 < epsilon)
    (he0 : epsilon < round4ProbeReserveThreshold B0 Pb Csize rho q loss)
    (T : {A : V // p 0 (A-H) < rho} → V)
    (hsize : ∀ s R (A : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p s (T A) ≤ epsilon*Csize s R)
    (hdiff : ∀ s R (A B : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p (s+loss) B.val ≤ R →
      p s (T A-T B) ≤ epsilon*Cdiff s R*p (s+loss) (A.val-B.val)) :
    let A := round4ProbeReserveIterate p H rho T probe
    let R := round4ProbeReserveProfile B0 Pb Csize loss
    let Cd := fun i s => max 0 (Cdiff s (R i (s+loss)))
    let Dp := round4ProbeDifferenceProfile Pd Cd loss
    (∀ i ≤ q, ∀ u ∈ U, p 0 (A i u-H) < rho) ∧
      (∀ i ≤ q, ∀ u ∈ U, ∀ s, p s (A i u) ≤ R i s) ∧
      (∀ i ≤ q, ∀ u ∈ U, ∀ v ∈ U, ∀ s,
        p s (A i u-A i v) ≤ Dp i s*(‖u‖+‖v‖)*‖u-v‖) := by
  intro A R Cd Dp
  obtain ⟨hres,hprof⟩ := round4_probe_common_reserve_profiles p H rho hrho B0 Pb Csize q loss
    U probe hH hPb hPb0 epsilon he he0 T hsize
  have he1 : epsilon ≤ 1 := he0.le.trans (min_le_left _ _)
  have hCd (i s : ℕ) : 0 ≤ Cd i s := le_max_left _ _
  have hDp (i s : ℕ) : 0 ≤ Dp i s :=
    round4ProbeDifferenceProfile_nonneg Pd Cd loss hPd hCd i s
  refine ⟨hres,hprof,?_⟩
  intro i
  induction i with
  | zero =>
    intro hi u hu v hv s
    simp [A,round4ProbeReserveIterate,Dp,round4ProbeDifferenceProfile]
  | succ i ih =>
    intro hi u hu v hv s
    have hiq : i ≤ q := by omega
    let Au : {A : V // p 0 (A-H) < rho} := ⟨A i u,hres i hiq u hu⟩
    let Av : {A : V // p 0 (A-H) < rho} := ⟨A i v,hres i hiq v hv⟩
    have hsu : A (i+1) u = H-probe u-T Au := by
      change H-probe u-(if h : p 0 (A i u-H)<rho then T ⟨A i u,h⟩ else 0) = _
      split_ifs with h
      · rfl
      · exact False.elim (h (hres i hiq u hu))
    have hsv : A (i+1) v = H-probe v-T Av := by
      change H-probe v-(if h : p 0 (A i v-H)<rho then T ⟨A i v,h⟩ else 0) = _
      split_ifs with h
      · rfl
      · exact False.elim (h (hres i hiq v hv))
    have ht := hdiff s (R i (s+loss)) Au Av (hprof i hiq u hu (s+loss))
      (hprof i hiq v hv (s+loss))
    have hbT : p s (T Au-T Av) ≤ Cd i s*Dp i (s+loss)*(‖u‖+‖v‖)*‖u-v‖ := by
      calc
        _ ≤ epsilon*Cdiff s (R i (s+loss))*p (s+loss) (A i u-A i v) := ht
        _ ≤ epsilon*Cd i s*p (s+loss) (A i u-A i v) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right _ _) he.le) (apply_nonneg _ _)
        _ ≤ epsilon*Cd i s*(Dp i (s+loss)*(‖u‖+‖v‖)*‖u-v‖) :=
          mul_le_mul_of_nonneg_left (ih hiq u hu v hv (s+loss)) (mul_nonneg he.le (hCd i s))
        _ = epsilon*(Cd i s*Dp i (s+loss)*(‖u‖+‖v‖)*‖u-v‖) := by ring
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right he1
            (mul_nonneg (mul_nonneg (mul_nonneg (hCd i s) (hDp i (s+loss)))
              (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))
    have heq : A (i+1) u-A (i+1) v = -(probe u-probe v)-(T Au-T Av) := by
      rw [hsu,hsv]
      abel
    rw [heq]
    calc
      _ ≤ p s (probe u-probe v)+p s (T Au-T Av) := by
        simpa only [map_neg_eq_map] using map_sub_le_add (p s) (-(probe u-probe v)) (T Au-T Av)
      _ ≤ Pd s*(‖u‖+‖v‖)*‖u-v‖+Cd i s*Dp i (s+loss)*(‖u‖+‖v‖)*‖u-v‖ :=
        add_le_add (hPdiff u hu v hv s) hbT
      _ = _ := by dsimp only [Dp,round4ProbeDifferenceProfile]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_probe_common_reserve_profiles

#print axioms GlobalEmbedding.Continuation.round4_probe_finite_tame_parameter_difference
