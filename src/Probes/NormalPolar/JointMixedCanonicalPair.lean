import NormalPolar.JointMixedForcedResidual
import Probes.Round4ParameterProbeForcedDifference

/-! One canonical mean operator propagates a whole forcing family. The
actual two-input primitive supply is evaluated at the same two iterates;
the output retains the original native domains and sample sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m d N count p : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

private theorem jointMixed_canonical_pair_supply
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (pj : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S univ))
    (H : parameterRound2_originalTensorGermSpace A B S univ) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ)
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (s : ℕ) (R : ℝ)
    (K L : parameterRound2_originalTensorGermSpace A B S univ)
    (hK : pj 0 (K-H) < rho) (hL : pj 0 (L-H) < rho)
    (hKR : pj (s+(q+4)) K ≤ R) (hLR : pj (s+(q+4)) L ≤ R) :
    Nonempty (∀ idx : Fin A.count × Fin count,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
        reserve (Bnd s R) (Mg s) T
        (fun t => F ((B idx.2).symm t)) (fun t => hF ((B idx.2).symm t))
        (round3ParameterNativePrimary F
          (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (B idx.2))
        (fun t => K.val ((B idx.2).symm t)) (fun t => L.val ((B idx.2).symm t))
        (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M)))
        (fun nu => round3ParameterNativeDomain (B idx.2) (primary nu))
        (A.chart idx.1)
        (actualRawObserverOpen (A.chart idx.1)
          (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M))))
        ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx) (epsilon*ell) ell
        (Dinput s*pj (s+(q+4)) (K-L))) := by
  obtain ⟨out,hO⟩ := supply epsilon he he1 s R ⟨K,hK⟩ ⟨L,hL⟩ hKR hLR
  refine ⟨fun idx => ?_⟩
  have hh := out.raw idx
  rw [congrFun hO idx] at hh
  exact hh

theorem jointMixed_canonical_forced_pair_raw
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
    (hDinput : ∀ s, 0 ≤ Dinput s) (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (ProbeB ProbeDiff : ℕ → ℝ) :
    let pj := parameterRound2_originalTensorGermSeminorm A B S univ hS hSO ell
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C q (q+4)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let Cd := fun s bound => C s bound*Dinput s
    let Diff := round4ParameterProbeForcedDifferenceCost ProbeDiff Cd R (q+4)
    0 < cap ∧ ∀
      (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k)) (primary : Λ → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell →
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ)
      (Su : Set (Fin p → ℝ))
      (meanProbe : (Fin p → ℝ) → (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (Pforce : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace A B S univ),
    (∀ u ∈ Su, (Pforce u).val = (delta^2)⁻¹ • meanProbe u) →
    (∀ u ∈ Su, ∀ s, pj s (Pforce u) ≤ ProbeB s) →
    (∀ u ∈ Su, pj 0 (Pforce u) ≤ rho/4) →
    (∀ u ∈ Su, ∀ v ∈ Su, ∀ s,
      pj s (Pforce u-Pforce v) ≤ ((‖u‖+‖v‖)*‖u-v‖)*ProbeDiff s) →
    ∃ K : (Fin p → ℝ) → ℕ → parameterRound2_originalTensorGermSpace A B S univ,
      (∀ u ∈ Su, ∀ i ≤ q+1, (K u i).val = actualParameterBackgroundMeanIterate F hF g
        (q+2) (epsilon*ell) delta H.val meanProbe i u) ∧
      (∀ u ∈ Su, ∀ i ≤ q+1, pj 0 (K u i-H) ≤ rho/2) ∧
      (∀ u ∈ Su, ∀ i ≤ q+1, ∀ s, pj s (K u i) ≤ R i s) ∧
      (∀ u ∈ Su, ∀ v ∈ Su, ∀ i ≤ q+1, ∀ s,
        pj s (K u i-K v i) ≤ ((‖u‖+‖v‖)*‖u-v‖)*Diff i s) ∧
      ∀ u ∈ Su, ∀ v ∈ Su, ∀ i ≤ q+1, ∀ s,
        ∃ Delta : ℝ,
        Delta ≤ (Dinput s*Diff i (s+(q+4)))*(‖u‖+‖v‖)*‖u-v‖ ∧
        Nonempty (∀ idx : Fin A.count × Fin count,
          ParameterRound2GlobalMeanRawProfiles (Tr := Tr) (s+(q+4)) (q+2) s Rsub Lprimary
            reserve (Bnd s (R i (s+(q+4)))) (Mg s) T
            (fun t => F ((B idx.2).symm t)) (fun t => hF ((B idx.2).symm t))
            (round3ParameterNativePrimary F
              (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) (B idx.2))
            (fun t => (K u i).val ((B idx.2).symm t))
            (fun t => (K v i).val ((B idx.2).symm t))
            (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M)))
            (fun nu => round3ParameterNativeDomain (B idx.2) (primary nu))
            (A.chart idx.1)
            (actualRawObserverOpen (A.chart idx.1)
              (round3ParameterNativeDomain (B idx.2) (univ : Set (P × M))))
            ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx) (epsilon*ell) ell Delta) := by
  intro pj C cap R Cd Diff
  refine ⟨round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C q (q+4),?_⟩
  intro F hF g hg primary supply epsilon he hecap delta Su meanProbe Pforce hPv hP hP0 hPQ
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
      (hQ : pj 0 (Q-H) < rho) : Tmean Q = Top epsilon ⟨Q,hQ⟩ := dif_pos hQ
  have hsize' : ∀ s R0 (Q : parameterRound2_originalTensorGermSpace A B S univ),
      pj 0 (Q-H) < rho → pj (s+(q+4)) Q ≤ R0 → pj s (Tmean Q) ≤ epsilon*C s R0 := by
    intro s R0 Q hQ hQR
    rw [hTeq Q hQ]
    exact hsize epsilon he he1 s R0 ⟨Q,hQ⟩ hQR
  have hdiff' : ∀ s R0 (Q Q' : parameterRound2_originalTensorGermSpace A B S univ),
      pj 0 (Q-H) < rho → pj 0 (Q'-H) < rho →
      pj (s+(q+4)) Q ≤ R0 → pj (s+(q+4)) Q' ≤ R0 →
      pj s (Tmean Q-Tmean Q') ≤ epsilon*Cd s R0*pj (s+(q+4)) (Q-Q') := by
    intro s R0 Q Q' hQ hQ' hQR hQ'R
    rw [hTeq Q hQ,hTeq Q' hQ']
    exact hdiff epsilon he he1 s R0 ⟨Q,hQ⟩ ⟨Q',hQ'⟩ hQR hQ'R
  let K := fun u => round4ParameterProbeForcedIterate H (Pforce u) Tmean
  have hk (u : Fin p → ℝ) (hu : u ∈ Su) := round4ParameterProbe_forced_finite_reserve
    pj H HBound hH rho hrho ProbeB C q (q+4) (Pforce u) (hP u hu) (hP0 u hu)
      epsilon he hecap Tmean hsize'
  have hdom (u : Fin p → ℝ) (hu : u ∈ Su) (i : ℕ) (hi : i ≤ q+1) :
      pj 0 (K u i-H) < rho := (hk u hu i hi).1.trans_lt (by linarith)
  have hTv (u : Fin p → ℝ) (hu : u ∈ Su) (i : ℕ) (hi : i ≤ q+1) :
      (Tmean (K u i)).val = round3ParameterPrimaryMeanError F hF g (K u i).val (q+2) (epsilon*ell) := by
    rw [hTeq (K u i) (hdom u hu i hi)]
    exact round3ParameterMeanReserveOperator_val A B S univ pj H rho ell F hF g q hsm
      epsilon ⟨K u i,hdom u hu i hi⟩ he he1
  have hvalue (u : Fin p → ℝ) (hu : u ∈ Su) : ∀ i ≤ q+1,
      (K u i).val = actualParameterBackgroundMeanIterate F hF g
        (q+2) (epsilon*ell) delta H.val meanProbe i u := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi0 : i ≤ q+1 := by omega
      change H.val-(Pforce u).val-(Tmean (K u i)).val = _
      rw [hPv u hu,hTv u hu i hi0,ih hi0]
      rfl
  have hpair (u : Fin p → ℝ) (hu : u ∈ Su) (v : Fin p → ℝ) (hv : v ∈ Su) :
      ∀ i ≤ q+1, ∀ s,
        pj s (K u i-K v i) ≤ ((‖u‖+‖v‖)*‖u-v‖)*Diff i s :=
    round4ParameterProbe_forced_finite_difference pj H HBound hH rho hrho ProbeB C Cd q (q+4)
      (Pforce u) (Pforce v) (hP u hu) (hP v hv) (hP0 u hu) (hP0 v hv)
      epsilon he hecap Tmean hsize' hdiff' ProbeDiff ((‖u‖+‖v‖)*‖u-v‖)
      (by positivity) (hPQ u hu v hv)
  refine ⟨K,hvalue,fun u hu i hi => (hk u hu i hi).1,
    fun u hu i hi => (hk u hu i hi).2,hpair,?_⟩
  intro u hu v hv i hi s
  refine ⟨Dinput s*pj (s+(q+4)) (K u i-K v i),?_,?_⟩
  · calc
      _ ≤ Dinput s*(((‖u‖+‖v‖)*‖u-v‖)*Diff i (s+(q+4))) :=
        mul_le_mul_of_nonneg_left (hpair u hu v hv i hi (s+(q+4))) (hDinput s)
      _ = _ := by ring
  · exact jointMixed_canonical_pair_supply A B S pj H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell supply epsilon he he1 s (R i (s+(q+4)))
      (K u i) (K v i) (hdom u hu i hi) (hdom v hv i hi)
      ((hk u hu i hi).2 (s+(q+4))) ((hk v hv i hi).2 (s+(q+4)))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointMixed_canonical_forced_pair_raw
