import Smoothing.ParameterRound2MeanRawProfiles
import Smoothing.ParameterRound2SplitGlobalMeanIndex
import Smoothing.ParameterRound2MeanPrimitives

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D


theorem parameterRound2_actual_raw_globalMean_uniform_index
    (n length j Rsub Lprimary : ℕ) (i i' : Fin (m+1)) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hTnonneg : ∀ k, 0 ≤ T k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β]
    (F : Ep → M → V)
    (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta),
    let meanA := fun z => parameterRound2_globalObservedMeanCoefficient F hF g input length tau e z i i'
    let meanB := fun z => parameterRound2_globalObservedMeanCoefficient F hF g inputbar length tau e z i i'
    (ContDiffOn ℝ ∞ meanA O ∧ ContDiffOn ℝ ∞ meanB O) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanA z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k meanB z‖ ≤ K*(tau/ell)) ∧
    (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun w => meanA w-meanB w) z‖ ≤ K*(tau/ell)*Delta) := by
  obtain ⟨K,hK,hout⟩ := parameterRound2_actual_primitive_globalMean_bounds_uniform_split_scale_index
    (I := I) (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N)
    n length j Rsub Lprimary i i' horder c Bnd Mg hc hBnd hMg T hTnonneg
  refine ⟨K,hK,?_⟩
  intro Λ Β _ _ F hF g input inputbar W primary e O S tau ell Delta data
  exact hout
    F hF g input inputbar W
    data.prim.hW data.prim.hCombinedSupport data.prim.hInverse e O S
    data.hO data.hSO data.hkappaO data.hmapWO data.Omega data.U
    data.Sloc data.hOmega data.hSOmega data.hkappa data.hmapW data.hU
    data.hOU data.hSloc data.hsource data.hphi data.hmap data.prim.hA
    data.prim.hB data.prim.hG data.prim.hJ data.prim.hT0 tau ell
    Delta data.htau data.htaul data.hell1 data.hDelta (parameterRound2_meanPrimitives_source F hF g input W primary data.prim length tau)
    (parameterRound2_meanPrimitives_source F hF g inputbar W primary data.primbar length tau) data.L data.A data.Abar data.hL data.hInput
    data.hInputbar data.hRep data.hRepbar data.hCut data.hEta data.hNormal
    data.hBR data.hReserve data.hBRb data.hLb data.hInputb data.hInputbarb
    data.hCutb data.hEtab data.hNormalb data.hDiff data.hAb data.hBb
    data.hGb data.hJb data.hTb data.hphib data.hRsub data.Lobs
    data.Aobs data.Abarobs data.hLobs data.hAobs data.hAbarobs data.hRepobs
    data.hRepbarobs data.hCutobs data.hNormalobs data.hPhaseobs data.hReserveobs data.hLobsb
    data.hAobsb data.hAbarobsb data.hCutobsb data.hNormalobsb data.hGradobsb data.hDiffobs
    data.hCover data.hPositiveCover data.hCount

#print axioms parameterRound2_actual_raw_globalMean_uniform_index
end GlobalEmbedding.Continuation
