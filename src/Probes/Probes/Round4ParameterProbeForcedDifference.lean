import Probes.Round4ParameterProbeForcedReserve

/-! Genuine two-input stability for the same forced finite mean iteration.
The common numerical cap first proves both reserves. No parameter regularity
is inferred from pointwise primitive supplies, and no derivative of the
nonlinear mean is assumed. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
namespace GlobalEmbedding.Continuation
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def round4ParameterProbeForcedDifferenceCost (ProbeDiff : ℕ → ℝ)
    (Cdiff : ℕ → ℝ → ℝ) (R : ℕ → ℕ → ℝ) (loss : ℕ) : ℕ → ℕ → ℝ
  | 0,_ => 0
  | i+1,s => max 0 (ProbeDiff s)+max 0 (Cdiff s (R i (s+loss)))*
      round4ParameterProbeForcedDifferenceCost ProbeDiff Cdiff R loss i (s+loss)

theorem round4ParameterProbeForcedDifferenceCost_nonneg (ProbeDiff : ℕ → ℝ)
    (Cdiff : ℕ → ℝ → ℝ) (R : ℕ → ℕ → ℝ) (loss i s : ℕ) :
    0 ≤ round4ParameterProbeForcedDifferenceCost ProbeDiff Cdiff R loss i s := by
  induction i generalizing s with
  | zero => exact le_rfl
  | succ i ih => exact add_nonneg (le_max_left _ _) (mul_nonneg (le_max_left _ _) (ih _))

/-- Both actual iterates use H at time zero and the same nonlinear operator.
The forcing difference is propagated through the finite derivative loss;
the resulting coefficient is independent of the two forcing fields. -/
theorem round4ParameterProbe_forced_finite_difference
    (p : ℕ → Seminorm ℝ V) (H : V) (HBound : ℕ → ℝ)
    (hH : ∀ s, p s H ≤ HBound s) (rho : ℝ) (hrho : 0 < rho)
    (B : ℕ → ℝ) (Csize Cdiff : ℕ → ℝ → ℝ) (q loss : ℕ)
    (P Q : V) (hP : ∀ s, p s P ≤ B s) (hQ : ∀ s, p s Q ≤ B s)
    (hP0 : p 0 P ≤ rho/4) (hQ0 : p 0 Q ≤ rho/4)
    (epsilon : ℝ) (he : 0 < epsilon)
    (hecap : epsilon < round4ParameterProbeForcedCap HBound rho B Csize q loss)
    (T : V → V)
    (hsize : ∀ s R (K : V), p 0 (K-H) < rho → p (s+loss) K ≤ R →
      p s (T K) ≤ epsilon*Csize s R)
    (hdiff : ∀ s R (K L : V), p 0 (K-H) < rho → p 0 (L-H) < rho →
      p (s+loss) K ≤ R → p (s+loss) L ≤ R →
      p s (T K-T L) ≤ epsilon*Cdiff s R*p (s+loss) (K-L))
    (ProbeDiff : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hPQ : ∀ s, p s (P-Q) ≤ D*ProbeDiff s) :
    let R := round4ParameterProbeForcedProfile HBound B Csize loss
    ∀ i ≤ q+1, ∀ s,
      p s (round4ParameterProbeForcedIterate H P T i-round4ParameterProbeForcedIterate H Q T i) ≤
        D*round4ParameterProbeForcedDifferenceCost ProbeDiff Cdiff R loss i s := by
  intro R
  let AP := round4ParameterProbeForcedIterate H P T
  let AQ := round4ParameterProbeForcedIterate H Q T
  have hp := round4ParameterProbe_forced_finite_reserve p H HBound hH rho hrho B Csize q loss
    P hP hP0 epsilon he hecap T hsize
  have hq := round4ParameterProbe_forced_finite_reserve p H HBound hH rho hrho B Csize q loss
    Q hQ hQ0 epsilon he hecap T hsize
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  intro i
  induction i with
  | zero => intro _ s; simp [round4ParameterProbeForcedIterate,round4ParameterProbeForcedDifferenceCost]
  | succ i ih =>
    intro hi s
    have hi' : i ≤ q+1 := by omega
    have hdomP : p 0 (AP i-H) < rho := lt_of_le_of_lt (hp i hi').1 (by linarith)
    have hdomQ : p 0 (AQ i-H) < rho := lt_of_le_of_lt (hq i hi').1 (by linarith)
    have hT := hdiff s (R i (s+loss)) (AP i) (AQ i) hdomP hdomQ
      ((hp i hi').2 (s+loss)) ((hq i hi').2 (s+loss))
    have hc : epsilon*Cdiff s (R i (s+loss)) ≤ max 0 (Cdiff s (R i (s+loss))) := by
      calc
        _ ≤ epsilon*max 0 (Cdiff s (R i (s+loss))) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) he.le
        _ ≤ max 0 (Cdiff s (R i (s+loss))) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 (le_max_left 0 _)
    have hid : AP (i+1)-AQ (i+1) = -((P-Q)+(T (AP i)-T (AQ i))) := by
      change (H-P-T (AP i))-(H-Q-T (AQ i)) = _
      abel
    change p s (AP (i+1)-AQ (i+1)) ≤ _
    rw [hid,map_neg_eq_map]
    calc
      _ ≤ p s (P-Q)+p s (T (AP i)-T (AQ i)) := map_add_le_add _ _ _
      _ ≤ D*ProbeDiff s+epsilon*Cdiff s (R i (s+loss))*p (s+loss) (AP i-AQ i) :=
        add_le_add (hPQ s) hT
      _ ≤ D*max 0 (ProbeDiff s)+max 0 (Cdiff s (R i (s+loss)))*p (s+loss) (AP i-AQ i) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hD)
          (mul_le_mul_of_nonneg_right hc (apply_nonneg _ _))
      _ ≤ D*max 0 (ProbeDiff s)+max 0 (Cdiff s (R i (s+loss)))*
          (D*round4ParameterProbeForcedDifferenceCost ProbeDiff Cdiff R loss i (s+loss)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih hi' (s+loss)) (le_max_left 0 _))
      _ = _ := by rw [round4ParameterProbeForcedDifferenceCost]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_forced_finite_difference
