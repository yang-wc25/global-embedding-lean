import Smoothing.ParameterRound2MeanReserve

/-! Finite mean inversion with derivative loss after the accepted reserve.
The entrance threshold is obtained from the original finite backward
reserve theorem. It is chosen before T and before the later observation
order. A finite profile then controls every later order; differences give
the q+1 power without an infinite contraction or an extra smallness gate. -/

noncomputable section
open GlobalEmbedding.Paper Set Function
namespace GlobalEmbedding.Continuation

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def parameterRound2_finiteMeanProfile (p : ℕ → Seminorm ℝ V) (H : V)
    (C : ℕ → ℝ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,s => p s H
  | i+1,s => p s H + max 0 (C s (parameterRound2_finiteMeanProfile p H C loss i (s+loss)))

def parameterRound2_finiteMeanErrorCost (C0 : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,s => C0 s
  | i+1,s => C i s * parameterRound2_finiteMeanErrorCost C0 C loss i (s+loss)

theorem parameterRound2_finiteMeanErrorCost_nonneg
    (C0 : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (loss : ℕ)
    (hC0 : ∀ s, 0 ≤ C0 s) (hC : ∀ i s, 0 ≤ C i s) (i s : ℕ) :
    0 ≤ parameterRound2_finiteMeanErrorCost C0 C loss i s := by
  induction i generalizing s with
  | zero => exact hC0 s
  | succ i ih => exact mul_nonneg (hC i s) (ih (s+loss))

theorem parameterRound2_finite_mean_reserve_and_residual
    (p : ℕ → Seminorm ℝ V) (hp : ∀ s t, s ≤ t → ∀ A, p s A ≤ p t A)
    (H : V) (rho : ℝ) (hrho : 0 < rho)
    (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧
    ∀ T : ℝ → {A : V // p 0 (A-H) < rho} → V,
      (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
        (A : {A : V // p 0 (A-H) < rho}),
        p (s+loss) A.val ≤ R → p s (T epsilon A) ≤ epsilon*Csize s R) →
      (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
        (A B : {A : V // p 0 (A-H) < rho}),
        p (s+loss) A.val ≤ R → p (s+loss) B.val ≤ R →
        p s (T epsilon A-T epsilon B) ≤
          epsilon*Cdiff s R*p (s+loss) (A.val-B.val)) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
      let A := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
      let R := parameterRound2_finiteMeanProfile p H Csize loss
      let C0 := fun s => max 0 (Csize s (p (s+loss) H))
      let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
      (∀ i ≤ q, p 0 (A i-H) ≤ rho/2) ∧
      (∀ i ≤ q, ∀ s, p s (A i) ≤ R i s) ∧
      ∃ hdom : p 0 (A q-H) < rho, ∀ j,
        p j (A q + T epsilon ⟨A q,hdom⟩-H) ≤
          epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss q j := by
  obtain ⟨epsilon0,he0,he01,hreserve⟩ := mean_iteration_finite_reserve p hp H rho hrho Csize q loss hq
  refine ⟨epsilon0,he0,he01,?_⟩
  intro T hsize hdiff epsilon he he0lt A R C0 Cd
  have he1 : epsilon ≤ 1 := he0lt.le.trans he01
  have hres := (hreserve T hsize epsilon he he0lt).1
  have hdom (i : ℕ) (hi : i ≤ q) : p 0 (A i-H) < rho :=
    lt_of_le_of_lt (hres i hi).1 (by linarith)
  have hstep (i : ℕ) (hi : i ≤ q) : A (i+1) = H-T epsilon ⟨A i,hdom i hi⟩ := by
    change (meanReserveStep (p 0) H rho (T epsilon))^[i+1] H = _
    rw [Function.iterate_succ_apply']
    change meanReserveStep (p 0) H rho (T epsilon) (A i) = _
    simp only [meanReserveStep,dite_eq_left (hdom i hi)]
  have hprofile : ∀ i ≤ q, ∀ s, p s (A i) ≤ R i s := by
    intro i
    induction i with
    | zero => intro hi s; exact le_rfl
    | succ i ih =>
      intro hi s
      have hiq : i ≤ q := by omega
      have hh := hsize epsilon he he1 s (R i (s+loss)) ⟨A i,hdom i hiq⟩ (ih hiq (s+loss))
      rw [hstep i hiq]
      calc
        _ ≤ p s H+p s (T epsilon ⟨A i,hdom i hiq⟩) := map_sub_le_add _ _ _
        _ ≤ p s H+epsilon*Csize s (R i (s+loss)) := add_le_add le_rfl hh
        _ ≤ p s H+epsilon*max 0 (Csize s (R i (s+loss))) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_max_right _ _) he.le)
        _ ≤ p s H+max 0 (Csize s (R i (s+loss))) :=
          add_le_add le_rfl (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right he1 (le_max_left 0 _))
        _ = R (i+1) s := rfl
  have hCd (i s : ℕ) : 0 ≤ Cd i s := le_max_left _ _
  have hC0 (s : ℕ) : 0 ≤ C0 s := le_max_left _ _
  have hdelta : ∀ i ≤ q, ∀ s,
      p s (A (i+1)-A i) ≤ epsilon^(i+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss i s := by
    intro i
    induction i with
    | zero =>
      intro hi s
      have heq : A (0+1)-A 0 = -(T epsilon ⟨A 0,hdom 0 (by omega)⟩) := by
        rw [hstep 0 (by omega)]
        change H-T epsilon ⟨A 0,hdom 0 (by omega)⟩-H = _
        abel
      rw [heq,map_neg_eq_map]
      have hh := hsize epsilon he he1 s (p (s+loss) H)
        ⟨A 0,hdom 0 (by omega)⟩ le_rfl
      simpa only [parameterRound2_finiteMeanErrorCost,Nat.zero_add,pow_one,C0] using
        hh.trans (mul_le_mul_of_nonneg_left (le_max_right 0 _) he.le)
    | succ i ih =>
      intro hi s
      have hiq : i ≤ q := by omega
      have hisq : i+1 ≤ q := hi
      let A0 : {K : V // p 0 (K-H) < rho} := ⟨A i,hdom i hiq⟩
      let A1 : {K : V // p 0 (K-H) < rho} := ⟨A (i+1),hdom (i+1) hisq⟩
      let M := max (R i (s+loss)) (R (i+1) (s+loss))
      have h0 : p (s+loss) A0.val ≤ M := (hprofile i hiq (s+loss)).trans (le_max_left _ _)
      have h1 : p (s+loss) A1.val ≤ M := (hprofile (i+1) hisq (s+loss)).trans (le_max_right _ _)
      have hh := hdiff epsilon he he1 s M A1 A0 h1 h0
      have heq : A (i+1+1)-A (i+1) = -(T epsilon A1-T epsilon A0) := by
        calc
          _ = (H-T epsilon A1)-A (i+1) :=
            congrArg (fun x => x-A (i+1)) (hstep (i+1) hisq)
          _ = (H-T epsilon A1)-(H-T epsilon A0) :=
            congrArg (fun x => (H-T epsilon A1)-x) (hstep i hiq)
          _ = _ := by abel
      change p s (A (i+1+1)-A (i+1)) ≤ _
      rw [heq,map_neg_eq_map]
      calc
        _ ≤ epsilon*Cdiff s M*p (s+loss) (A (i+1)-A i) := hh
        _ ≤ epsilon*Cd i s*p (s+loss) (A (i+1)-A i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right 0 _) he.le) (apply_nonneg _ _)
        _ ≤ (epsilon*Cd i s)*(epsilon^(i+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss i (s+loss)) :=
          mul_le_mul_of_nonneg_left (ih hiq (s+loss)) (mul_nonneg he.le (hCd i s))
        _ = _ := by rw [parameterRound2_finiteMeanErrorCost,pow_succ]; ring
  refine ⟨fun i hi => (hres i hi).1,hprofile,hdom q le_rfl,?_⟩
  intro j
  have heq : A q+T epsilon ⟨A q,hdom q le_rfl⟩-H = -(A (q+1)-A q) := by
    rw [hstep q le_rfl]
    abel
  rw [heq,map_neg_eq_map]
  exact hdelta q le_rfl j

def parameterRound2_finiteMeanThreshold
    (p : ℕ → Seminorm ℝ V) (hp : ∀ s t, s ≤ t → ∀ A, p s A ≤ p t A)
    (H : V) (rho : ℝ) (hrho : 0 < rho)
    (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) : ℝ :=
  Classical.choose (parameterRound2_finite_mean_reserve_and_residual p hp H rho hrho Csize Cdiff q loss hq)

theorem parameterRound2_finiteMeanThreshold_pos
    (p : ℕ → Seminorm ℝ V) (hp : ∀ s t, s ≤ t → ∀ A, p s A ≤ p t A)
    (H : V) (rho : ℝ) (hrho : 0 < rho)
    (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) :
    0 < parameterRound2_finiteMeanThreshold p hp H rho hrho Csize Cdiff q loss hq ∧
    parameterRound2_finiteMeanThreshold p hp H rho hrho Csize Cdiff q loss hq ≤ 1 := by
  exact ⟨(Classical.choose_spec (parameterRound2_finite_mean_reserve_and_residual p hp H rho hrho Csize Cdiff q loss hq)).1,
    (Classical.choose_spec (parameterRound2_finite_mean_reserve_and_residual p hp H rho hrho Csize Cdiff q loss hq)).2.1⟩

theorem parameterRound2_finite_mean_at_threshold
    (p : ℕ → Seminorm ℝ V) (hp : ∀ s t, s ≤ t → ∀ A, p s A ≤ p t A)
    (H : V) (rho : ℝ) (hrho : 0 < rho)
    (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ) (hq : 1 ≤ q) :
    ∀ T : ℝ → {A : V // p 0 (A-H) < rho} → V,
      (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
        (A : {A : V // p 0 (A-H) < rho}),
        p (s+loss) A.val ≤ R → p s (T epsilon A) ≤ epsilon*Csize s R) →
      (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
        (A B : {A : V // p 0 (A-H) < rho}),
        p (s+loss) A.val ≤ R → p (s+loss) B.val ≤ R →
        p s (T epsilon A-T epsilon B) ≤
          epsilon*Cdiff s R*p (s+loss) (A.val-B.val)) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < parameterRound2_finiteMeanThreshold p hp H rho hrho Csize Cdiff q loss hq →
      let A := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
      let R := parameterRound2_finiteMeanProfile p H Csize loss
      let C0 := fun s => max 0 (Csize s (p (s+loss) H))
      let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
      (∀ i ≤ q, p 0 (A i-H) ≤ rho/2) ∧
      (∀ i ≤ q, ∀ s, p s (A i) ≤ R i s) ∧
      ∃ hdom : p 0 (A q-H) < rho, ∀ j,
        p j (A q + T epsilon ⟨A q,hdom⟩-H) ≤
          epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss q j := by
  exact (Classical.choose_spec (parameterRound2_finite_mean_reserve_and_residual p hp H rho hrho Csize Cdiff q loss hq)).2.2

#print axioms parameterRound2_finite_mean_at_threshold

#print axioms parameterRound2_finite_mean_reserve_and_residual
end GlobalEmbedding.Continuation
