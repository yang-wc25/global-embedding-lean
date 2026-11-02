import Smoothing.Round3ParameterMeanRawAtlas
import Smoothing.Round3ParameterMeanCoordinates
import Smoothing.Round3ParameterMeanNorms
import Smoothing.ParameterRound2TensorGermSpace
import Probes.Round3ParameterMeanSymmetry

/-! Actual raw mean estimates for one global tensor on arbitrary P.  The
constant is chosen before P, all finite phase and refinement types, and the
parameter atlas count.  The coefficient bound is consumed in the genuine
parameter chart, then returned to the unchanged original differentiation
domain.  Size and difference estimates are proved, not supplied. -/

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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_raw_mean_original_norms_uniform
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
    (input inputbar : parameterRound2_originalTensorGermSpace A B S W)
    (tau ell Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1) (hDelta : 0 ≤ Delta)
    (data : Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF g input.val inputbar.val
      n q j Rsub Lprimary reserve Bnd Mg T W primary S tau ell Delta),
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
  obtain ⟨K,hK,hraw⟩ := parameterRound2_actual_raw_globalMean_array_uniform_index
    (I := 𝓙) (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N)
    n (q+2) j Rsub Lprimary horder reserve Bnd Mg hc hBnd hMg T hT
  let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) hK
  refine ⟨C,hC,?_⟩
  intro P Λ Β _ _ _ c A B hA F hF g hg W primary S input inputbar tau ell Delta htau htaul hell1 hDelta data
    TA TB O WA WB WD
  let a := parameterTensorModelEquiv (m+1) d
  let Obs := data.observationDomain
  let muA := fun (i : Fin A.count × Fin c) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) (fun t => input.val ((B i.2).symm t))
      (q+2) tau (A.chart i.1) z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  let muB := fun (i : Fin A.count × Fin c) (z : X) (k : Fin ((m+1)*(m+1))) =>
    parameterRound2_globalObservedMeanCoefficient
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2)) (fun t => inputbar.val ((B i.2).symm t))
      (q+2) tau (A.chart i.1) z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hh (i : Fin A.count × Fin c) := hraw
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2))
    (fun t => input.val ((B i.2).symm t)) (fun t => inputbar.val ((B i.2).symm t))
    (round3ParameterNativeDomain (B i.2) W) (fun ν => round3ParameterNativeDomain (B i.2) (primary ν))
    (A.chart i.1) (Obs i) (a ⁻¹' S i) tau ell Delta (data.raw i)
  have hO (i) : IsOpen (Obs i) := (data.raw i).hO
  have hSO (i) : a ⁻¹' S i ⊆ Obs i := (data.raw i).hSO
  have hOsub (i) : Obs i ⊆ (B i.2).target ×ˢ (A.chart i.1).target := by
    intro z hz
    exact ⟨((data.raw i).hmapWO hz).1,data.target i z hz⟩
  have heA (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates A B TA i y = fun k => (muA i (a.symm y) k).re := by
    apply round3Parameter_original_meanError_coordinates A B hA F hF g hg input.val W primary
      q hq tau htau i (data.raw i).prim y
    · exact ⟨(hOsub i hy).2,(hOsub i hy).1⟩
    · exact (data.raw i).hmapWO hy
  have heB (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates A B TB i y = fun k => (muB i (a.symm y) k).re := by
    apply round3Parameter_original_meanError_coordinates A B hA F hF g hg inputbar.val W primary
      q hq tau htau i (data.raw i).primbar y
    · exact ⟨(hOsub i hy).2,(hOsub i hy).1⟩
    · exact (data.raw i).hmapWO hy
  have heD (i) (y) (hy : a.symm y ∈ Obs i) :
      incrementsOriginalTensorCoordinates A B (fun t x => TA t x-TB t x) i y =
        fun k => (muA i (a.symm y) k-muB i (a.symm y) k).re := by
    funext k
    change incrementsOriginalTensorCoordinates A B TA i y k -
      incrementsOriginalTensorCoordinates A B TB i y k = _
    rw [congrFun (heA i y hy) k,congrFun (heB i y hy) k,Complex.sub_re]
  have hell : 0 < ell := htau.trans_le htaul
  have hKA : 0 ≤ K*(tau/ell) := mul_nonneg hK (div_nonneg htau.le hell.le)
  have hKD : 0 ≤ K*(tau/ell)*Delta := mul_nonneg hKA hDelta
  have ha := round3Parameter_original_tensor_norm_of_complex_germs A B TA S Obs hO hOsub hSO muA
    (fun i k => ((hh i).1 (finProdFinEquiv.symm k)).1) heA j ell (K*(tau/ell)) hell hell1 hKA
    (fun i k r hr z hz => (hh i).2.1 (finProdFinEquiv.symm k) r hr z hz)
  have hb := round3Parameter_original_tensor_norm_of_complex_germs A B TB S Obs hO hOsub hSO muB
    (fun i k => ((hh i).1 (finProdFinEquiv.symm k)).2) heB j ell (K*(tau/ell)) hell hell1 hKA
    (fun i k r hr z hz => (hh i).2.2.1 (finProdFinEquiv.symm k) r hr z hz)
  have hd := round3Parameter_original_tensor_norm_of_complex_germs A B (fun t x => TA t x-TB t x)
    S Obs hO hOsub hSO (fun i z k => muA i z k-muB i z k)
    (fun i k => (((hh i).1 (finProdFinEquiv.symm k)).1).sub (((hh i).1 (finProdFinEquiv.symm k)).2))
    heD j ell (K*(tau/ell)*Delta) hell hell1 hKD
    (fun i k r hr z hz => (hh i).2.2.2 (finProdFinEquiv.symm k) r hr z hz)
  have hsample (i) : S i ⊆ a.symm ⁻¹' Obs i := by
    intro y hy
    apply hSO i
    change a (a.symm y) ∈ S i
    simpa using hy
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨ha.2.1,ha.2.2.trans_eq ?_⟩,
    ⟨hb.2.1,hb.2.2.trans_eq ?_⟩,⟨hd.2.1,hd.2.2.trans_eq ?_⟩⟩
  · intro i
    exact ⟨a.symm ⁻¹' Obs i,(hO i).preimage a.symm.continuous,hsample i,ha.1 i⟩
  · intro z hz
    exact (round3ParameterPrimaryMean_symmetric F hF g input.val (q+2) tau z.1 z.2).sub
      (input.property.2 z hz)
  · intro i
    exact ⟨a.symm ⁻¹' Obs i,(hO i).preimage a.symm.continuous,hsample i,hb.1 i⟩
  · intro z hz
    exact (round3ParameterPrimaryMean_symmetric F hF g inputbar.val (q+2) tau z.1 z.2).sub
      (inputbar.property.2 z hz)
  all_goals dsimp only [C]; ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_raw_mean_original_norms_uniform
