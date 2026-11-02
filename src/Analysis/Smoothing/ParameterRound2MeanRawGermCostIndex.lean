import Smoothing.ParameterRound2MeanRawNativeGermsIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

universe uM uTr uΛ uΒ

variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- Only the listed finite jet prefix is made available to a chosen analytic
constant. The arbitrary continuation beyond this order is identically zero. -/
def parameterRound2_numericProfilePrefix (r : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≤ r then T k else 0

theorem parameterRound2_numericProfilePrefix_nonneg (r : ℕ) (T : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (k : ℕ) : 0 ≤ parameterRound2_numericProfilePrefix r T k := by
  unfold parameterRound2_numericProfilePrefix
  split_ifs
  · exact hT k
  · exact le_rfl

theorem parameterRound2_numericProfilePrefix_congr (r : ℕ) (T T' : ℕ → ℝ)
    (h : ∀ k, k ≤ r → T k = T' k) :
    parameterRound2_numericProfilePrefix r T = parameterRound2_numericProfilePrefix r T' := by
  funext k
  unfold parameterRound2_numericProfilePrefix
  split_ifs with hk
  · exact h k hk
  · rfl

def parameterRound2_rawMeanIndexUniformCost
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k) : ℝ :=
  Classical.choose (parameterRound2_actual_raw_mean_original_germ_norms_uniform_index.{uM,uTr,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
    (parameterRound2_numericProfilePrefix (j+1) T) (parameterRound2_numericProfilePrefix j TP)
    (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg j TP hTP))

theorem parameterRound2_rawMeanIndexUniformCost_nonneg
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k):
    0 ≤ parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ} (m := m) (d := d) (N := N)
      (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP := by
  exact (Classical.choose_spec (parameterRound2_actual_raw_mean_original_germ_norms_uniform_index.{uM,uTr,uΛ,uΒ}
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
    (parameterRound2_numericProfilePrefix (j+1) T) (parameterRound2_numericProfilePrefix j TP)
    (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT)
    (parameterRound2_numericProfilePrefix_nonneg j TP hTP))).1

theorem parameterRound2_rawMeanIndexUniformCost_bound
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k):
    let C := parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ} (m := m) (d := d) (N := N)
      (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP
    ∀ {Λ : Type uΛ} {Β : Type uΒ} [Fintype Λ] [Fintype Β] {c : ℕ}
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,D) x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
    (Obs : Fin A.count × Fin c → Set X)
    (hObsSub : ∀ i, Obs i ⊆ (B i.2).source ×ˢ (A.chart i.1).target)
    (data : ∀ i : Fin A.count × Fin c,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary reserve Bnd Mg T
        F hF g input inputbar W primary (A.chart i.1)
        (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))
        tau ell Delta)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let TA := incrementsGlobalPrimaryMeanError F hF g input (q+2) tau
    let TB := incrementsGlobalPrimaryMeanError F hF g inputbar (q+2) tau
    let O := incrementsOriginalDifferentiation A B
    let WA := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TA) O S
    let WB := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TB) O S
    let WD := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x)) O S
    (∃ U : (Fin A.count × Fin c) → Set (Fin (m+1+d) → ℝ),
      (∀ i, IsOpen (U i) ∧ S i ⊆ U i ∧ U i ⊆ O i ∧
        ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B TA i) (U i) ∧
        ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B TB i) (U i))) ∧
    (WA ≠ ⊤ ∧ WA.toReal ≤ C*(tau/ell)) ∧
    (WB ≠ ⊤ ∧ WB.toReal ≤ C*(tau/ell)) ∧
    (WD ≠ ⊤ ∧ WD.toReal ≤ C*(tau/ell)*Delta) := by
  intro C Λ Β _ _ c A B hA hB F hF g input inputbar W primary S hSO
    tau ell Delta htau htaul hell1 hDelta Obs hObsSub data hParam
  let data' (i : Fin A.count × Fin c) :
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary reserve Bnd Mg
        (parameterRound2_numericProfilePrefix (j+1) T)
        F hF g input inputbar W primary (A.chart i.1) (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) ''
          ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)) tau ell Delta := {
    data i with
    hphib := by
      intro nu beta k hk hkj z hz
      simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hkj] using
        (data i).hphib nu beta k hk hkj z hz }
  have hout := (Classical.choose_spec
    (parameterRound2_actual_raw_mean_original_germ_norms_uniform_index.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg
      (parameterRound2_numericProfilePrefix (j+1) T) (parameterRound2_numericProfilePrefix j TP)
      (parameterRound2_numericProfilePrefix_nonneg (j+1) T hT)
      (parameterRound2_numericProfilePrefix_nonneg j TP hTP))).2 (Λ := Λ) (Β := Β) (c := c)
  exact hout A B hA hB F hF g input inputbar W primary S hSO tau ell Delta
    htau htaul hell1 hDelta Obs hObsSub data' (by
      intro i z hz k hk hkj
      simpa only [parameterRound2_numericProfilePrefix,ite_eq_left hkj] using hParam i z hz k hk hkj)

/-- The selected numerical mean constant is EXTENSIONALLY independent of
all observer transition values beyond j+1 and parameter values beyond j.
This is an equality of the actual selected cost, not just existence of another
constant for each continuation of the profiles. -/
theorem parameterRound2_rawMeanIndexUniformCost_prefix_congr
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP T' TP' : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hT' : ∀ k, 0 ≤ T' k) (hTP' : ∀ k, 0 ≤ TP' k)
    (hTeq : ∀ k, k ≤ j+1 → T k = T' k)
    (hTPeq : ∀ k, k ≤ j → TP k = TP' k) :
    parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP =
    parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T' TP' hT' hTP' := by
  have ht := parameterRound2_numericProfilePrefix_congr (j+1) T T' hTeq
  have htp := parameterRound2_numericProfilePrefix_congr j TP TP' hTPeq
  unfold parameterRound2_rawMeanIndexUniformCost
  congr 1
  rw [ht,htp]

#print axioms parameterRound2_rawMeanIndexUniformCost_bound
#print axioms parameterRound2_rawMeanIndexUniformCost_prefix_congr
end GlobalEmbedding.Continuation
