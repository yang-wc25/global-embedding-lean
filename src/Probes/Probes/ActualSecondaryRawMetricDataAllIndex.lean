import Probes.ActualSecondaryRawMetricData
import Probes.ActualSecondaryRawMetricRemainderAllIndex

/-! Raw-data interfaces for the final atlas consumer. The records contain
only original profiles and actual chart/cutoff/sampling choices. The actual
map and the mean-removed metric tensor are defined without derivative order,
observation budgets or any desired error estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawDataTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawDataTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawDataTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

 theorem actual_original_raw_metric_remainder_of_data_uniform_all_index
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (Label SubPrimary SubSecondary : Type*)
      [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary], ∀
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
        reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
      (e : OpenPartialHomeomorph M D) (Omega S : Set X)
      (obs : ActualOriginalSecondaryObservationData raw Tobs Rsecondary e Omega S),
    ContDiffOn ℝ ∞ (actualOriginalMeanRemovedMetric F hF g input (q+2) tau delta choice e) Omega ∧
      ∀ k ≤ j, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k
        (actualOriginalMeanRemovedMetric F hF g input (q+2) tau delta choice e) z‖ ≤
          CR*(delta*(tau/ell)^q+delta^3/tau) := by
  obtain ⟨CR,hCR,hout⟩ := actual_original_raw_metric_remainder_uniform_all_index
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
  refine ⟨CR,hCR,?_⟩
  intro Label SubPrimary SubSecondary _ _ _ _ F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw e Omega S obs
  exact hout Label SubPrimary SubSecondary F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw.geometry
    raw.coordinate raw.chart raw.phase raw.host raw.hostInverse raw.hostSource raw.cutoffSupport raw.pairSupport
    raw.partition raw.cutoffSmooth raw.inverseSmooth raw.hostProfiles raw.cutoffJets raw.inverseJets
    e obs.forward obs.inverse Omega S obs.profiles obs.target obs.originalSmooth raw.primaryGeometry
    obs.transition obs.inverseTransition obs.domains obs.openDomains obs.domainsSubset obs.activeDomains obs.source
    obs.samples obs.transitionJets obs.localCount

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_raw_metric_remainder_of_data_uniform_all_index
