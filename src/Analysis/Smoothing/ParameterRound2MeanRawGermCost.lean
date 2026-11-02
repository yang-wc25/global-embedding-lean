import Smoothing.ParameterRound2MeanRawNativeGerms

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation

variable {m d N c : ℕ} {M Tr : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def parameterRound2_rawMeanOriginalGermNormCost
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k) : ℝ :=
  Classical.choose (parameterRound2_actual_raw_mean_original_germ_norms_uniform
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP)

theorem parameterRound2_rawMeanOriginalGermNormCost_nonneg
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k):
    0 ≤ parameterRound2_rawMeanOriginalGermNormCost (m := m) (d := d) (N := N) (c := c)
      (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP := by
  exact (Classical.choose_spec (parameterRound2_actual_raw_mean_original_germ_norms_uniform
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP)).1

theorem parameterRound2_rawMeanOriginalGermNormCost_bound
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k):
    let C := parameterRound2_rawMeanOriginalGermNormCost (m := m) (d := d) (N := N) (c := c)
      (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP
    ∀
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
  exact (Classical.choose_spec (parameterRound2_actual_raw_mean_original_germ_norms_uniform
    (m := m) (d := d) (N := N) (c := c) (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP)).2

#print axioms parameterRound2_rawMeanOriginalGermNormCost_bound
end GlobalEmbedding.Continuation
