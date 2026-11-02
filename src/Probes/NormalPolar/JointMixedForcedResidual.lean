import NormalPolar.JointBackgroundForcedGerm

/-! The true final forced mean residual on the whole physical parameter
space. The same canonical raw reserve supply gives both size and difference
bounds for one actual finite solver. Its literal whole-field substitution
sequence supplies all native raw profiles and a single error germ bounded
at every original joint observation order. No fixed-parameter witness is
differentiated, and no completed mean/error estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

private theorem jointMixed_scaled_forced_identity {G : Type*} [AddCommGroup G] [Module ℝ G]
    (delta : ℝ) (hdelta : delta ≠ 0) (K Q Mean H : G) :
    delta^2 • (K+(delta^2)⁻¹ • Q+(Mean-K)-H) = delta^2 • Mean+Q-delta^2 • H := by
  simp only [smul_add,smul_sub,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hdelta),one_smul]
  abel

private theorem jointMixed_scaled_seminorm_bound {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : Seminorm ℝ G) (delta : ℝ) (x : G) (A : ℝ) (h : p x ≤ A) :
    p (delta^2 • x) ≤ delta^2*A := by
  rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg delta)

universe uM uTr uP uΛ uΒ
variable {m d N count : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem jointMixed_canonical_forced_mean_residual
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (hS : ∀ i, IsCompact (S i))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S univ)
    (HBound : ℕ → ℝ)
    (hH : ∀ s, parameterRound2_originalTensorGermSeminorm A B S univ hS hSO ell s H ≤ HBound s)
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (hDinput : ∀ s, 0 ≤ Dinput s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (ProbeB : ℕ → ℝ) :
    let pj := parameterRound2_originalTensorGermSeminorm A B S univ hS hSO ell
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C q (q+4)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let C0 := fun s => ProbeB s+max 0 (C s (HBound (s+(q+4))))
    let Cd := fun i s => max 0 ((C s (max (R i (s+(q+4))) (R (i+1) (s+(q+4)))))*Dinput s)
    0 < cap ∧ ∀
      (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
      (primary : Λ → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell →
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ) (hdelta : delta ≠ 0)
      (meanProbe : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (Pforce : parameterRound2_originalTensorGermSpace A B S univ),
    Pforce.val = (delta^2)⁻¹ • meanProbe →
    (∀ s, pj s Pforce ≤ ProbeB s) → pj 0 Pforce ≤ rho/4 →
    ∃ K : ℕ → parameterRound2_originalTensorGermSpace A B S univ,
      (∀ i ≤ q+1, (K i).val = actualParameterBackgroundMeanIterate F hF g
        (q+2) (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0) ∧
      (∀ i ≤ q+1, pj 0 (K i-H) ≤ rho/2) ∧
      (∀ i ≤ q+1, ∀ s, pj s (K i) ≤ R i s) ∧
      (∀ i ≤ q+1, ∀ s, Nonempty (∀ idx : Fin A.count × Fin count,
        ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
          reserve (Bnd s (R i (s+(q+4)))) (Mg s) T
          (fun t => F ((B idx.2).symm t)) (fun t => hF ((B idx.2).symm t))
          (round3ParameterNativePrimary F
            (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (B idx.2))
          (fun t => (K i).val ((B idx.2).symm t))
          (fun t => (K i).val ((B idx.2).symm t))
          (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M)))
          (fun nu => round3ParameterNativeDomain (B idx.2) (primary nu))
          (A.chart idx.1)
          (actualRawObserverOpen (A.chart idx.1)
            (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M))))
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx) (epsilon*ell) ell 0)) ∧
      ∃ E : parameterRound2_originalTensorGermSpace A B S univ,
        E.val = delta^2 • round3ParameterPrimaryMean F hF g (K (q+1)).val (q+2) (epsilon*ell) +
          meanProbe - delta^2 • H.val ∧
        ∀ s, pj s E ≤ delta^2*(epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd (q+4) (q+1) s) := by
  intro pj C cap R C0 Cd
  refine ⟨round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C q (q+4),?_⟩
  intro F hF g hg primary supply epsilon he hecap delta hdelta meanProbe Pforce hPv hP hP0
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  have raw := round3Parameter_canonical_reserve_forget A B S pj H rho q Rsub Lprimary
    reserve Bnd Mg Dinput T F hF g primary ell supply
  obtain ⟨hsm,hsize,hdiff⟩ := round3Parameter_actual_raw_mean_local_estimates
    A B hA S univ hS hSO ell hell hell1 H rho q Rsub Lprimary hq reserve hc
    Bnd Mg Dinput hBnd hMg hDinput T hT F hF g hg primary raw
  let Top := round3ParameterMeanReserveOperator A B S univ pj H rho ell F hF g q hsm
  let Tmean : parameterRound2_originalTensorGermSpace A B S univ →
      parameterRound2_originalTensorGermSpace A B S univ := fun Q =>
    if hQ : pj 0 (Q-H) < rho then Top epsilon ⟨Q,hQ⟩ else 0
  have hTeq (Q : parameterRound2_originalTensorGermSpace A B S univ)
      (hQ : pj 0 (Q-H) < rho) : Tmean Q = Top epsilon ⟨Q,hQ⟩ := by
    exact dif_pos hQ
  have hsize' : ∀ s R0 (Q : parameterRound2_originalTensorGermSpace A B S univ),
      pj 0 (Q-H) < rho → pj (s+(q+4)) Q ≤ R0 → pj s (Tmean Q) ≤ epsilon*C s R0 := by
    intro s R0 Q hQ hQR
    rw [hTeq Q hQ]
    exact hsize epsilon he he1 s R0 ⟨Q,hQ⟩ hQR
  have hdiff' : ∀ s R0 (Q Q' : parameterRound2_originalTensorGermSpace A B S univ),
      pj 0 (Q-H) < rho → pj 0 (Q'-H) < rho →
      pj (s+(q+4)) Q ≤ R0 → pj (s+(q+4)) Q' ≤ R0 →
      pj s (Tmean Q-Tmean Q') ≤ epsilon*(C s R0*Dinput s)*pj (s+(q+4)) (Q-Q') := by
    intro s R0 Q Q' hQ hQ' hQR hQ'R
    rw [hTeq Q hQ,hTeq Q' hQ']
    exact hdiff epsilon he he1 s R0 ⟨Q,hQ⟩ ⟨Q',hQ'⟩ hQR hQ'R
  let K := round4ParameterProbeForcedIterate H Pforce Tmean
  have hres := round4ParameterProbe_forced_finite_residual pj H HBound hH rho hrho
    ProbeB C (fun s R0 => C s R0*Dinput s) q (q+4) Pforce hP hP0 epsilon he hecap Tmean hsize' hdiff'
  have hk := hres.1
  have hdom (i : ℕ) (hi : i ≤ q+1) : pj 0 (K i-H) < rho :=
    (hk i hi).1.trans_lt (by linarith)
  have hTv (i : ℕ) (hi : i ≤ q+1) : (Tmean (K i)).val =
      round3ParameterPrimaryMeanError F hF g (K i).val (q+2) (epsilon*ell) := by
    rw [hTeq (K i) (hdom i hi)]
    exact round3ParameterMeanReserveOperator_val A B S univ pj H rho ell F hF g q hsm
      epsilon ⟨K i,hdom i hi⟩ he he1
  have hvalue : ∀ i ≤ q+1, (K i).val = actualParameterBackgroundMeanIterate F hF g
      (q+2) (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi0 : i ≤ q+1 := by omega
      change (H-Pforce-Tmean (K i)).val = _
      change H.val-Pforce.val-(Tmean (K i)).val = _
      rw [hPv,hTv i hi0,ih hi0]
      rfl
  refine ⟨K,hvalue,fun i hi => (hk i hi).1,fun i hi => (hk i hi).2,?_,?_⟩
  · intro i hi s
    exact round3Parameter_canonical_final_raw A B S univ pj H rho q Rsub Lprimary
      reserve Bnd Mg Dinput T F hF g primary ell supply epsilon he he1 s
      (R i (s+(q+4))) (Bnd s (R i (s+(q+4)))) (Mg s) le_rfl le_rfl
      (K i) (hdom i hi) ((hk i hi).2 (s+(q+4)))
  · let E := delta^2 • (K (q+1)+Pforce+Tmean (K (q+1))-H)
    refine ⟨E,?_,?_⟩
    · change delta^2 • ((K (q+1)).val+Pforce.val+(Tmean (K (q+1))).val-H.val) = _
      rw [hPv,hTv (q+1) le_rfl]
      exact jointMixed_scaled_forced_identity delta hdelta (K (q+1)).val meanProbe
        (round3ParameterPrimaryMean F hF g (K (q+1)).val (q+2) (epsilon*ell)) H.val
    · intro s
      exact jointMixed_scaled_seminorm_bound (pj s) delta
        (K (q+1)+Pforce+Tmean (K (q+1))-H) _ (hres.2 s)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointMixed_canonical_forced_mean_residual
