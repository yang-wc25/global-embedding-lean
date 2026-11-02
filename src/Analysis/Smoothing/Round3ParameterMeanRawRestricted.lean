import Smoothing.Round3ParameterMeanRawNorms
import Smoothing.Round3ParameterPrimaryRestrictionMean
import Smoothing.ParameterRound2TensorGermTransfer

/-! Restrict only the actual charts to a proved positivity domain.  The
resulting estimates are returned to the SAME unrestricted global mean and
the SAME original tensor seminorm.  The output operator never depends on a
choice of positivity neighborhood or an observation chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_raw_restricted_mean_norms_uniform
    (n q j Rsub Lprimary : ℕ) (hq : 1 ≤ q) (horder : j+2+(q+2) ≤ n)
    (reserve Bnd Mg : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P Λ Β : Type*) [TopologicalSpace P] [Fintype Λ] [Fintype Β],
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
  obtain ⟨C,hC,hraw⟩ := round3Parameter_actual_raw_mean_original_norms_uniform
    (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
    n q j Rsub Lprimary hq horder reserve Bnd Mg hc hBnd hMg T hT
  refine ⟨C,hC,?_⟩
  intro P Λ Β _ _ _ c A B hA F hF g hg W primary S hSO input inputbar G hG hGW hSG
    tau ell Delta htau htaul hell1 hDelta data TA TB O WA WB WD
  let gG := round3Parameter_restrictPrimaryFamily F g G hG
  let K : parameterRound2_originalTensorGermSpace A B S G :=
    ⟨input.val,input.property.1,fun z hz => input.property.2 z (hGW hz)⟩
  let L : parameterRound2_originalTensorGermSpace A B S G :=
    ⟨inputbar.val,inputbar.property.1,fun z hz => inputbar.property.2 z (hGW hz)⟩
  have hgG : ∀ ν β, Round3ParameterChartPreserves (gG.chart ν β) := by
    intro ν β z hz
    exact hg ν β z hz.1
  have hh := hraw P Λ Β c A B hA F hF gG hgG G primary S K L tau ell Delta
    htau htaul hell1 hDelta data
  have heA := round3Parameter_restrictPrimary_meanError F hF g G hG input.val (q+2) tau
  have heB := round3Parameter_restrictPrimary_meanError F hF g G hG inputbar.val (q+2) tau
  have heD : ∀ z ∈ G,
      round3ParameterPrimaryMeanError F hF gG input.val (q+2) tau z.1 z.2 -
        round3ParameterPrimaryMeanError F hF gG inputbar.val (q+2) tau z.1 z.2 =
      TA z.1 z.2-TB z.1 z.2 := by
    intro z hz
    rw [heA z hz,heB z hz]
  have hma : TA ∈ parameterRound2_originalTensorGermSpace A B S W := by
    constructor
    · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO _ _ hh.1.1.1 G hG hSG heA
    · intro z hz
      exact (round3ParameterPrimaryMean_symmetric F hF g input.val (q+2) tau z.1 z.2).sub
        (input.property.2 z hz)
  have hmb : TB ∈ parameterRound2_originalTensorGermSpace A B S W := by
    constructor
    · exact parameterRound2_tensor_coordinate_germ_transfer A B S hSO _ _ hh.1.2.1 G hG hSG heB
    · intro z hz
      exact (round3ParameterPrimaryMean_symmetric F hF g inputbar.val (q+2) tau z.1 z.2).sub
        (inputbar.property.2 z hz)
  have hnA := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO _ _ G hG hSG heA 0 j ell
  have hnB := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO _ _ G hG hSG heB 0 j ell
  have hnD := parameterRound2_originalTensor_weighted_eq_of_sample_germ A B S hSO
    (fun t x => round3ParameterPrimaryMeanError F hF gG input.val (q+2) tau t x-
      round3ParameterPrimaryMeanError F hF gG inputbar.val (q+2) tau t x)
    (fun t x => TA t x-TB t x) G hG hSG heD 0 j ell
  refine ⟨⟨hma,hmb⟩,?_,?_,?_⟩
  · exact (congrArg (fun w : ℝ≥0∞ => w ≠ ⊤ ∧ w.toReal ≤ C*(tau/ell)) hnA).mp hh.2.1
  · exact (congrArg (fun w : ℝ≥0∞ => w ≠ ⊤ ∧ w.toReal ≤ C*(tau/ell)) hnB).mp hh.2.2.1
  · exact (congrArg (fun w : ℝ≥0∞ => w ≠ ⊤ ∧ w.toReal ≤ C*(tau/ell)*Delta) hnD).mp hh.2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_raw_restricted_mean_norms_uniform
