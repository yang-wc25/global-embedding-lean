import Smoothing.ParameterRound2FiniteMeanIteration

/-! A finite forced mean iteration with its genuine initial value H.
The forcing is small only in the original zero-order seminorm; its later
profiles may be arbitrary fixed bounds. A single numerical threshold is
chosen before the forcing, the operator, and all later observation orders.
The residual is derived from consecutive actual substitutions. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def round4ParameterProbeForcedIterate (H P : V) (T : V → V) : ℕ → V
  | 0 => H
  | i+1 => H-P-T (round4ParameterProbeForcedIterate H P T i)

def round4ParameterProbeForcedProfile (HBound B : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,s => HBound s
  | i+1,s => HBound s+B s+max 0 (C s (round4ParameterProbeForcedProfile HBound B C loss i (s+loss)))

def round4ParameterProbeForcedCap (HBound : ℕ → ℝ)
    (rho : ℝ) (B : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (q loss : ℕ) : ℝ :=
  min 1 (rho/(4*(1+∑ i : Fin (q+1),
    max 0 (C 0 (round4ParameterProbeForcedProfile HBound B C loss i loss)))))

theorem round4ParameterProbeForcedCap_pos (HBound : ℕ → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (B : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (q loss : ℕ) :
    0 < round4ParameterProbeForcedCap HBound rho B C q loss := by
  unfold round4ParameterProbeForcedCap
  have hsum : 0 ≤ ∑ i : Fin (q+1),
      max 0 (C 0 (round4ParameterProbeForcedProfile HBound B C loss i loss)) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  exact lt_min (by norm_num) (div_pos hrho (by positivity))

/-- The finite forward profile and the common low reserve belong to the same
literal substitution sequence, starting at H rather than H-P. -/
theorem round4ParameterProbe_forced_finite_reserve
    (p : ℕ → Seminorm ℝ V) (H : V) (HBound : ℕ → ℝ)
    (hH : ∀ s, p s H ≤ HBound s) (rho : ℝ) (hrho : 0 < rho)
    (B : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (q loss : ℕ)
    (P : V) (hP : ∀ s, p s P ≤ B s) (hP0 : p 0 P ≤ rho/4)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hecap : epsilon < round4ParameterProbeForcedCap HBound rho B C q loss)
    (T : V → V)
    (hsize : ∀ s R (K : V), p 0 (K-H) < rho → p (s+loss) K ≤ R →
      p s (T K) ≤ epsilon*C s R) :
    let A := round4ParameterProbeForcedIterate H P T
    let R := round4ParameterProbeForcedProfile HBound B C loss
    (∀ i ≤ q+1, p 0 (A i-H) ≤ rho/2 ∧ ∀ s, p s (A i) ≤ R i s) := by
  intro A R
  let M := ∑ i : Fin (q+1), max 0 (C 0 (R i loss))
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have he1 : epsilon ≤ 1 :=
    (hecap.trans_le (min_le_left _ _)).le
  have hsmall : epsilon*(4*(1+M)) < rho :=
    (lt_div_iff₀ (by positivity : 0 < 4*(1+M))).mp
      (hecap.trans_le (min_le_right _ _))
  have hlow (i : ℕ) (hi : i ≤ q) : epsilon*max 0 (C 0 (R i loss)) ≤ rho/4 := by
    have hle : max 0 (C 0 (R i loss)) ≤ M := by
      exact Finset.single_le_sum (s:=Finset.univ)
        (f:=fun k : Fin (q+1) => max 0 (C 0 (R k loss)))
        (fun k _ => le_max_left 0 (C 0 (R k loss)))
        (Finset.mem_univ (⟨i,by omega⟩ : Fin (q+1)))
    have hh := mul_le_mul_of_nonneg_left hle he.le
    nlinarith
  intro i
  induction i with
  | zero =>
    intro _
    constructor
    · change p 0 (H-H) ≤ rho/2
      simp only [sub_self,map_zero]
      positivity
    · intro s; exact hH s
  | succ i ih =>
    intro hi
    obtain ⟨hres,hprof⟩ := ih (by omega)
    have hdom : p 0 (A i-H) < rho := lt_of_le_of_lt hres (by linarith)
    have hscaled (s : ℕ) : p s (T (A i)) ≤ max 0 (C s (R i (s+loss))) := by
      calc
        _ ≤ epsilon*C s (R i (s+loss)) := hsize s _ (A i) hdom (hprof (s+loss))
        _ ≤ epsilon*max 0 (C s (R i (s+loss))) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) he.le
        _ ≤ max 0 (C s (R i (s+loss))) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 (le_max_left 0 _)
    constructor
    · have hid : A (i+1)-H = -(P+T (A i)) := by
        change (H-P-T (A i))-H = _
        abel
      rw [hid,map_neg_eq_map]
      have ht : p 0 (T (A i)) ≤ rho/4 := by
        calc
          _ ≤ epsilon*C 0 (R i loss) := by
            exact hsize 0 (R i loss) (A i) hdom (by simpa only [Nat.zero_add] using hprof loss)
          _ ≤ epsilon*max 0 (C 0 (R i loss)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) he.le
          _ ≤ rho/4 := hlow i (by omega)
      exact (map_add_le_add (p 0) P (T (A i))).trans (by linarith)
    · intro s
      change p s (H-P-T (A i)) ≤ HBound s+B s+max 0 (C s (R i (s+loss)))
      calc
        _ ≤ p s (H-P)+p s (T (A i)) := map_sub_le_add _ _ _
        _ ≤ (p s H+p s P)+max 0 (C s (R i (s+loss))) :=
          add_le_add (map_sub_le_add _ _ _) (hscaled s)
        _ ≤ _ := by linarith [hP s,hH s]

/-- Finite derivative-loss differences yield the required high power for the
actual forced residual. The forcing contributes to the initial difference;
it is never multiplied by an unjustified extra epsilon. -/
theorem round4ParameterProbe_forced_finite_residual
    (p : ℕ → Seminorm ℝ V) (H : V) (HBound : ℕ → ℝ)
    (hH : ∀ s, p s H ≤ HBound s) (rho : ℝ) (hrho : 0 < rho)
    (B : ℕ → ℝ) (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ)
    (P : V) (hP : ∀ s, p s P ≤ B s) (hP0 : p 0 P ≤ rho/4)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hecap : epsilon < round4ParameterProbeForcedCap HBound rho B Csize q loss)
    (T : V → V)
    (hsize : ∀ s R (K : V), p 0 (K-H) < rho → p (s+loss) K ≤ R →
      p s (T K) ≤ epsilon*Csize s R)
    (hdiff : ∀ s R (K L : V), p 0 (K-H) < rho → p 0 (L-H) < rho →
      p (s+loss) K ≤ R → p (s+loss) L ≤ R →
      p s (T K-T L) ≤ epsilon*Cdiff s R*p (s+loss) (K-L)) :
    let A := round4ParameterProbeForcedIterate H P T
    let R := round4ParameterProbeForcedProfile HBound B Csize loss
    let C0 := fun s => B s+max 0 (Csize s (HBound (s+loss)))
    let Cd := fun i s => max 0 (Cdiff s (max (R i (s+loss)) (R (i+1) (s+loss))))
    (∀ i ≤ q+1, p 0 (A i-H) ≤ rho/2 ∧ ∀ s, p s (A i) ≤ R i s) ∧
    ∀ s, p s (A (q+1)+P+T (A (q+1))-H) ≤
      epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd loss (q+1) s := by
  intro A R C0 Cd
  have hres := round4ParameterProbe_forced_finite_reserve p H HBound hH rho hrho B Csize q loss
    P hP hP0 epsilon he hecap T hsize
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  have hdom (i : ℕ) (hi : i ≤ q+1) : p 0 (A i-H) < rho :=
    lt_of_le_of_lt (hres i hi).1 (by linarith)
  have hCd (i s : ℕ) : 0 ≤ Cd i s := le_max_left _ _
  have hdelta : ∀ i ≤ q+1, ∀ s,
      p s (A (i+1)-A i) ≤ epsilon^i*parameterRound2_finiteMeanErrorCost C0 Cd loss i s := by
    intro i
    induction i with
    | zero =>
      intro _ s
      have hid : A 1-A 0 = -(P+T H) := by change (H-P-T H)-H = _; abel
      rw [hid,map_neg_eq_map]
      have hTH := hsize s (HBound (s+loss)) H (by simp; exact hrho) (hH (s+loss))
      have hT : p s (T H) ≤ max 0 (Csize s (HBound (s+loss))) := by
        calc
          _ ≤ epsilon*Csize s (HBound (s+loss)) := hTH
          _ ≤ epsilon*max 0 (Csize s (HBound (s+loss))) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) he.le
          _ ≤ max 0 (Csize s (HBound (s+loss))) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 (le_max_left 0 _)
      simpa only [pow_zero,one_mul,parameterRound2_finiteMeanErrorCost,C0] using
        (map_add_le_add (p s) P (T H)).trans (add_le_add (hP s) hT)
    | succ i ih =>
      intro hi s
      let M := max (R i (s+loss)) (R (i+1) (s+loss))
      have h0 : p (s+loss) (A i) ≤ M := (hres i (by omega)).2 (s+loss) |>.trans (le_max_left _ _)
      have h1 : p (s+loss) (A (i+1)) ≤ M :=
        (hres (i+1) hi).2 (s+loss) |>.trans (le_max_right _ _)
      have hh := hdiff s M (A (i+1)) (A i) (hdom (i+1) hi) (hdom i (by omega)) h1 h0
      have hid : A (i+1+1)-A (i+1) = -(T (A (i+1))-T (A i)) := by
        change (H-P-T (A (i+1)))-(H-P-T (A i)) = _
        abel
      rw [hid,map_neg_eq_map]
      calc
        _ ≤ epsilon*Cdiff s M*p (s+loss) (A (i+1)-A i) := hh
        _ ≤ epsilon*Cd i s*p (s+loss) (A (i+1)-A i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_right 0 _) he.le) (apply_nonneg _ _)
        _ ≤ (epsilon*Cd i s)*(epsilon^i*parameterRound2_finiteMeanErrorCost C0 Cd loss i (s+loss)) :=
          mul_le_mul_of_nonneg_left (ih (by omega) (s+loss)) (mul_nonneg he.le (hCd i s))
        _ = _ := by rw [parameterRound2_finiteMeanErrorCost,pow_succ]; ring
  refine ⟨hres,?_⟩
  intro s
  have hid : A (q+1)+P+T (A (q+1))-H = -(A (q+1+1)-A (q+1)) := by
    change A (q+1)+P+T (A (q+1))-H = -((H-P-T (A (q+1)))-A (q+1))
    abel
  rw [hid,map_neg_eq_map]
  exact hdelta (q+1) le_rfl s

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_forced_finite_reserve
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_forced_finite_residual
