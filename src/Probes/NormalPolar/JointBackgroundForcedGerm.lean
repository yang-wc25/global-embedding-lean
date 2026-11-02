import Smoothing.Round3ParameterCanonicalReserveForget
import Smoothing.Round3ParameterMeanLocalEstimates
import Probes.Round3ParameterCanonicalFinalRaw
import Probes.Round4ParameterProbeForcedReserve
import NormalPolar.ParameterDisplacementBackgroundParameterNaturality

/-!
# One global forced background and its actual joint primitive profiles

The forcing is a single tensor germ on the whole physical parameter space.
The mean operator is the original finite spatial solver. Its size and
difference estimates come from the canonical primitive reserve supply.
The actual iterates, all joint observation orders, and the final native raw
profiles refer to one sequence of whole tensor fields. No fixed-parameter
choice is differentiated, and no background output estimate is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
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

theorem jointBackground_canonical_forced_raw
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
    0 < cap ∧ ∀
      (F : P → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ l k, Round3ParameterChartPreserves (g.chart l k))
      (primary : Λ → Set (P × M)),
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S univ pj H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell →
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ)
      (meanProbe : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (Pforce : parameterRound2_originalTensorGermSpace A B S univ),
    Pforce.val = (delta^2)⁻¹ • meanProbe →
    (∀ s, pj s Pforce ≤ ProbeB s) → pj 0 Pforce ≤ rho/4 →
    ∃ K : ℕ → parameterRound2_originalTensorGermSpace A B S univ,
      (∀ i ≤ q+1, (K i).val = actualParameterBackgroundMeanIterate F hF g
        (q+2) (epsilon*ell) delta H.val (fun (_ : Fin 0 → ℝ) => meanProbe) i 0) ∧
      (∀ i ≤ q+1, pj 0 (K i-H) ≤ rho/2) ∧
      (∀ i ≤ q+1, ∀ s, pj s (K i) ≤ R i s) ∧
      ∀ i ≤ q+1, ∀ s, Nonempty (∀ idx : Fin A.count × Fin count,
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
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx) (epsilon*ell) ell 0) := by
  intro pj C cap R
  refine ⟨round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C q (q+4),?_⟩
  intro F hF g hg primary supply epsilon he hecap delta meanProbe Pforce hPv hP hP0
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
  have hsize' : ∀ s R0 (Q : parameterRound2_originalTensorGermSpace A B S univ),
      pj 0 (Q-H) < rho → pj (s+(q+4)) Q ≤ R0 → pj s (Tmean Q) ≤ epsilon*C s R0 := by
    intro s R0 Q hQ hQR
    dsimp only [Tmean]
    rw [dif_pos hQ]
    exact hsize epsilon he he1 s R0 ⟨Q,hQ⟩ hQR
  let K := round4ParameterProbeForcedIterate H Pforce Tmean
  have hk := round4ParameterProbe_forced_finite_reserve pj H HBound hH rho hrho
    ProbeB C q (q+4) Pforce hP hP0 epsilon he hecap Tmean hsize'
  have hdom (i : ℕ) (hi : i ≤ q+1) : pj 0 (K i-H) < rho :=
    (hk i hi).1.trans_lt (by linarith)
  have hTv (i : ℕ) (hi : i ≤ q+1) : (Tmean (K i)).val =
      round3ParameterPrimaryMeanError F hF g (K i).val (q+2) (epsilon*ell) := by
    dsimp only [Tmean]
    rw [dif_pos (hdom i hi)]
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
  refine ⟨K,hvalue,fun i hi => (hk i hi).1,fun i hi => (hk i hi).2,?_⟩
  intro i hi s
  exact round3Parameter_canonical_final_raw A B S univ pj H rho q Rsub Lprimary
    reserve Bnd Mg Dinput T F hF g primary ell supply epsilon he he1 s
    (R i (s+(q+4))) (Bnd s (R i (s+(q+4)))) (Mg s) le_rfl le_rfl
    (K i) (hdom i hi) ((hk i hi).2 (s+(q+4)))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.jointBackground_canonical_forced_raw
