import Smoothing.Round3ParameterMeanCost
import Smoothing.Round3ParameterMeanReserveSupply
import Smoothing.Round3ParameterMeanOperatorNorms

/-! The actual same global mean operator satisfies the original reserve
size and Lipschitz estimates.  Only concrete primitive profiles are supplied;
the operator estimates are derived in original full-joint seminorms.  The
chosen constant has explicit finite-prefix dependence and contains no atlas
count or phase/refinement count. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterMeanSizeCost
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (s : ℕ) (R : ℝ) : ℝ :=
  round3ParameterMeanNormCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc (hBnd s R) (hMg s) T hT

theorem round3Parameter_actual_raw_mean_local_estimates
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)) (primary : Λ → Set (P × M)) :
    let p := parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell
    let C := round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q Rsub Lprimary hq reserve hc Bnd Mg hBnd hMg T hT
    Round3ParameterMeanRawReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
      Bnd Mg Dinput T F hF g primary ell →
    ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W,
    let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p s (Top epsilon K) ≤ epsilon*C s R) ∧
    (∀ epsilon, 0 < epsilon → epsilon ≤ 1 → ∀ s R
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho}),
      p (s+(q+4)) K.val ≤ R → p (s+(q+4)) L.val ≤ R →
      p s (Top epsilon K-Top epsilon L) ≤ epsilon*(C s R*Dinput s)*p (s+(q+4)) (K.val-L.val)) := by
  intro p C hdata
  let Nrm := fun s (Q0 : (t : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)) =>
    paperAtlasWeighted 0 s ell (incrementsOriginalTensorCoordinates A B Q0)
      (incrementsOriginalDifferentiation A B) S
  have hRaw (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) (s : ℕ) (R : ℝ)
      (K L : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho})
      (hK : p (s+(q+4)) K.val ≤ R) (hL : p (s+(q+4)) L.val ≤ R) :
      let TA := round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell)
      let TB := round3ParameterPrimaryMeanError F hF g L.val.val (q+2) (epsilon*ell)
      (TA ∈ parameterRound2_originalTensorGermSpace A B S W ∧
        TB ∈ parameterRound2_originalTensorGermSpace A B S W) ∧
      (Nrm s TA ≠ ⊤ ∧ (Nrm s TA).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s TB ≠ ⊤ ∧ (Nrm s TB).toReal ≤ C s R*((epsilon*ell)/ell)) ∧
      (Nrm s (fun t x => TA t x-TB t x) ≠ ⊤ ∧
        (Nrm s (fun t x => TA t x-TB t x)).toReal ≤
          C s R*((epsilon*ell)/ell)*(Dinput s*p (s+(q+4)) (K.val-L.val))) := by
    obtain ⟨G,hG,hGW,hSG,⟨data⟩⟩ := hdata epsilon he he1 s R K L hK hL
    exact round3ParameterMeanNormCost_bound
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s)
      hc (hBnd s R) (hMg s) T hT P Λ Β c A B hA F hF g hg W primary S hSO
      K.val L.val G hG hGW hSG (epsilon*ell) ell (Dinput s*p (s+(q+4)) (K.val-L.val))
      (mul_pos he hell) (by simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hell.le) hell1
      (mul_nonneg (hDinput s) (apply_nonneg _ _)) data
  have hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
      ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
      round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
        parameterRound2_originalTensorGermSpace A B S W := by
    intro epsilon he he1 K
    exact (hRaw epsilon he he1 0 (p (0+(q+4)) K.val) K K le_rfl le_rfl).1.1
  refine ⟨hsm,?_⟩
  intro Top
  constructor
  · intro epsilon he he1 s R K hK
    exact round3Parameter_actual_germ_mean_operator_size A B S W hS hSO ell hell H rho
      F hF g q hsm epsilon he he1 K s (C s R)
      (hRaw epsilon he he1 s R K K hK hK).2.1.2
  · intro epsilon he he1 s R K L hK hL
    exact round3Parameter_actual_germ_mean_operator_difference A B S W hS hSO ell hell H rho
      F hF g q hsm epsilon he he1 K L s (q+4) (C s R) (Dinput s)
      (hRaw epsilon he he1 s R K L hK hL).2.2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_raw_mean_local_estimates
