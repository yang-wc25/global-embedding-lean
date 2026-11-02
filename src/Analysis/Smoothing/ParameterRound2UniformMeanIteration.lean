import Smoothing.ParameterRound2UniformMeanReserve

/-! The actual finite reserve step has a q+1 residual with constants fixed
from the numerical input bounds before H and before the seminorm family.
The same derivative loss is retained, with no monotonicity assumption on costs. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
namespace GlobalEmbedding.Continuation
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem parameterRound2_uniform_mean_finite_residual
    (B : ℕ → ℝ) (Csize Cdiff : ℕ → ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (q loss : ℕ) (p : ℕ → Seminorm ℝ V) (H : V) (hH : ∀ s, p s H ≤ B s)
    (T : ℝ → {A : V // p 0 (A-H) < rho} → V)
    (hsize : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (A : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p s (T epsilon A) ≤ epsilon*Csize s R)
    (hdiff : ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (A B : {A : V // p 0 (A-H) < rho}),
      p (s+loss) A.val ≤ R → p (s+loss) B.val ≤ R →
      p s (T epsilon A-T epsilon B) ≤ epsilon*Cdiff s R*p (s+loss) (A.val-B.val))
    (epsilon : ℝ) (he : 0 < epsilon)
    (he0 : epsilon < parameterRound2_uniformMeanThreshold B Csize rho q loss) :
    let A := fun i : ℕ => (meanReserveStep (p 0) H rho (T epsilon))^[i] H
    let R := parameterRound2_uniformMeanProfile B Csize loss
    let C0 := fun s => max 0 (Csize s (B (s+loss)))
    let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
    (∀ i ≤ q, p 0 (A i-H) ≤ rho/2) ∧
    (∀ i ≤ q, ∀ s, p s (A i) ≤ R i s) ∧
    ∃ hdom : p 0 (A q-H) < rho, ∀ j,
      p j (A q+T epsilon ⟨A q,hdom⟩-H) ≤
        epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss q j := by
  intro A R C0 Cd
  have he1 : epsilon ≤ 1 := he0.le.trans
    (parameterRound2_uniformMeanThreshold_pos B Csize rho hrho q loss).2
  have hh := parameterRound2_uniform_mean_reserve_profile B Csize rho hrho q loss p H hH T hsize epsilon he he0
  have hres : ∀ i ≤ q, p 0 (A i-H) ≤ rho/2 := hh.1
  have hprofile : ∀ i ≤ q, ∀ s, p s (A i) ≤ R i s := hh.2
  have hdom (i : ℕ) (hi : i ≤ q) : p 0 (A i-H) < rho :=
    lt_of_le_of_lt (hres i hi) (by linarith)
  have hstep (i : ℕ) (hi : i ≤ q) : A (i+1) = H-T epsilon ⟨A i,hdom i hi⟩ := by
    change (meanReserveStep (p 0) H rho (T epsilon))^[i+1] H = _
    rw [Function.iterate_succ_apply']
    change meanReserveStep (p 0) H rho (T epsilon) (A i) = _
    simp only [meanReserveStep,dite_eq_left (hdom i hi)]
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
      have hh := hsize epsilon he he1 s (B (s+loss))
        ⟨A 0,hdom 0 (by omega)⟩ (hH (s+loss))
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
  refine ⟨fun i hi => hres i hi,hprofile,hdom q le_rfl,?_⟩
  intro j
  have heq : A q+T epsilon ⟨A q,hdom q le_rfl⟩-H = -(A (q+1)-A q) := by
    rw [hstep q le_rfl]
    abel
  rw [heq,map_neg_eq_map]
  exact hdelta q le_rfl j

#print axioms parameterRound2_uniform_mean_finite_residual
end GlobalEmbedding.Continuation
