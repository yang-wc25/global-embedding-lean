import Smoothing.Round3ParameterMeanRawRestricted
import Smoothing.ParameterRound2MeanRawGermCostIndex

/-! Restrict only the actual charts to a proved positivity domain.  The
resulting estimates are returned to the SAME unrestricted global mean and
the SAME original tensor seminorm.  The output operator never depends on a
choice of positivity neighborhood or an observation chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ
variable {m d N : ℕ} {M : Type uM} {Tr : Type uTr}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterMeanNormCost
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) : ℝ :=
  Classical.choose (round3Parameter_actual_raw_restricted_mean_norms_uniform.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
    (parameterRound2_numericProfilePrefix (j+1) T)
    (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT))

theorem round3ParameterMeanNormCost_nonneg
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    0 ≤ round3ParameterMeanNormCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T hT :=
  (Classical.choose_spec (round3Parameter_actual_raw_restricted_mean_norms_uniform.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
    (parameterRound2_numericProfilePrefix (j+1) T)
    (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT))).1

theorem round3ParameterMeanNormCost_bound
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    let C := round3ParameterMeanNormCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T hT
    ∀ (P : Type uP) (Λ : Type uΛ) (Β : Type uΒ) [TopologicalSpace P] [Fintype Λ] [Fintype Β],
    ∀ (c : ℕ) (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
    (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
    (W : Set (P × M)) (primary : Λ → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (input inputbar : parameterRound2_originalTensorGermSpace A B S W)
    (G : Set (P × M)) (hG : IsOpen G) (hGW : G ⊆ W)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
    (data : Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF
      (round3Parameter_restrictPrimaryFamily F g G hG) input.val inputbar.val
      n q j Rsub Lprimary reserve Bnd Mg T G primary S tau ell Delta),
    let TA := round3ParameterPrimaryMeanError F hF g input.val (q+2) tau
    let TB := round3ParameterPrimaryMeanError F hF g inputbar.val (q+2) tau
    let O := incrementsOriginalDifferentiation A B
    let WA := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TA) O S
    let WB := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TB) O S
    let WD := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x)) O S
    (TA ∈ parameterRound2_originalTensorGermSpace A B S W ∧
      TB ∈ parameterRound2_originalTensorGermSpace A B S W) ∧
    (WA ≠ ⊤ ∧ WA.toReal ≤ C*(tau/ell)) ∧
    (WB ≠ ⊤ ∧ WB.toReal ≤ C*(tau/ell)) ∧
    (WD ≠ ⊤ ∧ WD.toReal ≤ C*(tau/ell)*Delta) := by
  intro C P Λ Β _ _ _ c A B hA F hF g hg W primary S hSO input inputbar G hG hGW hSG
    tau ell Delta htau htaul hell1 hDelta data
  let data' : Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF
      (round3Parameter_restrictPrimaryFamily F g G hG) input.val inputbar.val
      n q j Rsub Lprimary reserve Bnd Mg (parameterRound2_numericProfilePrefix (j+1) T)
      G primary S tau ell Delta := {
    observationDomain := data.observationDomain
    target := data.target
    raw := fun i => { data.raw i with
      hphib := by
        intro nu beta k hk hkj z hz
        simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hkj] using
          (data.raw i).hphib nu beta k hk hkj z hz } }
  exact (Classical.choose_spec (round3Parameter_actual_raw_restricted_mean_norms_uniform.{uM,uTr,uP,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
    (parameterRound2_numericProfilePrefix (j+1) T)
    (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT))).2
    P Λ Β c A B hA F hF g hg W primary S hSO input inputbar G hG hGW hSG
    tau ell Delta htau htaul hell1 hDelta data'

theorem round3ParameterMeanNormCost_prefix_congr
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T T' : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hT' : ∀ k, 0 ≤ T' k)
    (heq : ∀ k, k ≤ j+1 → T k = T' k) :
    round3ParameterMeanNormCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T hT =
    round3ParameterMeanNormCost.{uM,uTr,uP,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T' hT' := by
  have ht := parameterRound2_numericProfilePrefix_congr (j+1) T T' heq
  unfold round3ParameterMeanNormCost
  congr 1
  rw [ht]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterMeanNormCost_bound
#print axioms GlobalEmbedding.Continuation.round3ParameterMeanNormCost_prefix_congr
