import Probes.Round3ParameterRawAtlasData
import Probes.Round3ParameterOriginalTensorNorm
import Probes.Round3ParameterMetricCoordinates
import Probes.Round3ParameterMeanSymmetry
import Probes.ActualSecondaryRawMetricDataAllIndex

/-! # The actual global metric remainder in original general-parameter norms

The estimate is derived from the actual primary, quadratic secondary and
mixed/self terms by the established raw consumer.  Every original parameter
chart observes the same physical U and the same native mean.  Constants are
chosen before parameter spaces, both atlas counts and all phase/refinement
index types.  No residual estimate is a premise. -/

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

theorem round3Parameter_actual_metric_remainder_original_norm_uniform
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P Label SubPrimary SubSecondary : Type*)
      [TopologicalSpace P] [Fintype Label] [DecidableEq Label]
      [Fintype SubPrimary] [Fintype SubSecondary], ∀ (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep) (hA : IsSmoothBufferedAtlas A)
      (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
      (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (P × M)) (primary : Label → Set (P × M))
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (ell delta tau Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
      (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
        nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
        W primary S ell delta tau Delta choice),
    let U := round3ParameterIncrementMap F hF g input (q+2) tau delta choice
    let Mean := round3ParameterPrimaryMean F hF g input (q+2) tau
    let Rest := incrementsOriginalMetricError (fun y : P × M => F y.1 y.2) U Mean delta
    Rest ∈ parameterRound2_originalTensorGermSpace A B S W ∧
    paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
    (paperAtlasWeighted 0 j tau (incrementsOriginalTensorCoordinates A B Rest)
      (incrementsOriginalDifferentiation A B) S).toReal ≤ C*(delta*(tau/ell)^q+delta^3/tau) := by
  obtain ⟨K,hK,hraw⟩ := actual_original_raw_metric_remainder_of_data_uniform_all_index
    (m := m) (N := N) («Ep» := Ep) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
  let C := (j+1)*linearModelFactor (parameterTensorModelEquiv (m+1) d).symm j*K
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) (linearModelFactor_nonneg _ _)) hK
  refine ⟨C,hC,?_⟩
  intro P Label SubPrimary SubSecondary _ _ _ _ _ c A B hA F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U Mean Rest
  let O := data.observationDomain
  let a := parameterTensorModelEquiv (m+1) d
  let S0 := fun i => a ⁻¹' S i
  let R0 := fun (i : Fin A.count × Fin c) =>
    actualOriginalMeanRemovedMetric (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun t => input ((B i.2).symm t)) (q+2) tau delta
      (round3ParameterNativeChoices choice (B i.2)) (A.chart i.1)
  have hh (i : Fin A.count × Fin c) := hraw Label SubPrimary SubSecondary
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2))
    (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
    (round3ParameterNativeDomain (B i.2) W) (fun ν => round3ParameterNativeDomain (B i.2) (primary ν))
    ell delta tau Delta hdelta hdeltatau (round3ParameterNativeChoices choice (B i.2)) (data.raw i.2)
    (A.chart i.1) (O i) (S0 i) (data.observation i)
  have hO (i) : IsOpen (O i) := (data.observation i).profiles.hO
  have hSO (i) : S0 i ⊆ O i := (data.observation i).profiles.hSO
  have hOsub (i) : O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target := by
    intro z hz
    exact ⟨((data.observation i).profiles.hmapWO hz).1,(data.observation i).target z hz⟩
  have heq (i) : EqOn (actualOriginalNativeTargetTensor A B Rest i) (R0 i) (O i) := by
    intro z hz
    exact round3Parameter_original_mean_removed_native F hF g hg input (q+2) tau delta choice hc
      A B hA i z (hOsub i hz)
  have hsm (i) : ContDiffOn ℝ ∞ (actualOriginalNativeTargetTensor A B Rest i) (O i) :=
    (hh i).1.congr (heq i)
  have hj : ∀ i, ∀ k ≤ j, ∀ z : X, a z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (actualOriginalNativeTargetTensor A B Rest i) z‖ ≤
        K*(delta*(tau/ell)^q+delta^3/tau) := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((hO i).mem_nhds (hSO i hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hh i).2 k hk z hz
  have hell : 0 < ell := htau.trans_le htaul
  obtain ⟨hreg,hfinite,hbound⟩ := round3Parameter_original_tensor_weighted_norm_from_native_germs
    A B S O hO hOsub hSO Rest j tau (K*(delta*(tau/ell)^q+delta^3/tau))
    htau (htaul.trans hell1) (by positivity) hsm hj
  refine ⟨?_,hfinite,hbound.trans_eq (by dsimp only [C]; ring)⟩
  constructor
  · intro i
    refine ⟨a.symm ⁻¹' O i,(hO i).preimage a.symm.continuous,?_,hreg i⟩
    intro y hy
    apply hSO i
    change a (a.symm y) ∈ S i
    simpa using hy
  · intro z hz
    exact ((inducedMetric_isPosSemidef (I := 𝓙) (fun x => F z.1 x+U (z.1,x)) z.2).isSymm.sub
      (inducedMetric_isPosSemidef (I := 𝓙) (F z.1) z.2).isSymm).sub
      ((round3ParameterPrimaryMean_symmetric F hF g input (q+2) tau z.1 z.2).smul (delta^2))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_metric_remainder_original_norm_uniform
