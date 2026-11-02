import Smoothing.ParameterRound2MeanRawGermReserveSupply
import Smoothing.ParameterRound2MeanRawGermCost
import Smoothing.ParameterRound2TensorGermTransfer

/-! Actual local mean estimates on the ORIGINAL symmetric C0 reserve.
The size and Lipschitz constants are derived from concrete primitive profiles.
No estimate for T, the mean, or any finite residual is supplied. Every input
and difference size is the original weighted tensor seminorm. -/

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

theorem parameterRound2_actual_raw_restricted_mean_norm_bound
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph Ep Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (F : Ep → M → V) (hF : ∀ t, ContMDiff 𝓘(ℝ,D) 𝓘(ℝ,V) ∞ (F t))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,D)) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : parameterRound2_originalTensorGermSpace A B S W)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (hSG : ∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G)
    (primary : Λ → Set (Ep × M))
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
    (Obs : Fin A.count × Fin c → Set X)
    (hObsSub : ∀ i, Obs i ⊆ (B i.2).source ×ˢ (A.chart i.1).target)
    (data : ∀ i : Fin A.count × Fin c,
      ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n (q+2) j Rsub Lprimary reserve Bnd Mg T
        F hF (parameterRound2_restrictPrimaryFamily F g G hG) input.val inputbar.val G primary (A.chart i.1)
        (Obs i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i))
        tau ell Delta)
    (hParam : ∀ i : Fin A.count × Fin c, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k) :
    let C := parameterRound2_rawMeanOriginalGermNormCost (m := m) (d := d) (N := N) (c := c)
      (M := M) (Tr := Tr) (Λ := Λ) (Β := Β)
      n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP
    let TA := incrementsGlobalPrimaryMeanError F hF g input.val (q+2) tau
    let TB := incrementsGlobalPrimaryMeanError F hF g inputbar.val (q+2) tau
    let O := incrementsOriginalDifferentiation A B
    let WA := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TA) O S
    let WB := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B TB) O S
    let WD := paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x)) O S
    (TA ∈ parameterRound2_originalTensorGermSpace A B S W ∧
      TB ∈ parameterRound2_originalTensorGermSpace A B S W) ∧
    (WA ≠ ⊤ ∧ WA.toReal ≤ C*(tau/ell)) ∧
    (WB ≠ ⊤ ∧ WB.toReal ≤ C*(tau/ell)) ∧
    (WD ≠ ⊤ ∧ WD.toReal ≤ C*(tau/ell)*Delta) := by
  intro C TA TB O WA WB WD
  let gG := parameterRound2_restrictPrimaryFamily F g G hG
  have hh := parameterRound2_rawMeanOriginalGermNormCost_bound
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T TP hT hTP
    A B hA hB F hF gG input.val inputbar.val G primary S hSO
    tau ell Delta htau htaul hell1 hDelta Obs hObsSub data hParam
  obtain ⟨U,hU⟩ := hh.1
  have hma := parameterRound2_restrictPrimary_meanError_germ_mem A B S W hSO F hF g
    input (q+2) tau G hG hSG
    (fun i => ⟨U i,(hU i).1,(hU i).2.1,(hU i).2.2.2.1⟩)
  have hmb := parameterRound2_restrictPrimary_meanError_germ_mem A B S W hSO F hF g
    inputbar (q+2) tau G hG hSG
    (fun i => ⟨U i,(hU i).1,(hU i).2.1,(hU i).2.2.2.2⟩)
  have heA := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO
    (incrementsGlobalPrimaryMeanError F hF gG input.val (q+2) tau) TA G hG hSG
    (parameterRound2_restrictPrimary_meanError F hF g G hG input.val (q+2) tau) 0 j ell
  have heB := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO
    (incrementsGlobalPrimaryMeanError F hF gG inputbar.val (q+2) tau) TB G hG hSG
    (parameterRound2_restrictPrimary_meanError F hF g G hG inputbar.val (q+2) tau) 0 j ell
  have heD := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO
    (fun t x => incrementsGlobalPrimaryMeanError F hF gG input.val (q+2) tau t x-
      incrementsGlobalPrimaryMeanError F hF gG inputbar.val (q+2) tau t x)
    (fun t x => TA t x-TB t x) G hG hSG
    (fun z hz => congrArg₂ (fun a b => a-b)
      (parameterRound2_restrictPrimary_meanError F hF g G hG input.val (q+2) tau z hz)
      (parameterRound2_restrictPrimary_meanError F hF g G hG inputbar.val (q+2) tau z hz)) 0 j ell
  refine ⟨⟨hma,hmb⟩,?_,?_,?_⟩
  · simpa only [heA] using hh.2.1
  · simpa only [heB] using hh.2.2.1
  · simpa only [heD] using hh.2.2.2

#print axioms parameterRound2_actual_raw_restricted_mean_norm_bound
end GlobalEmbedding.Continuation
