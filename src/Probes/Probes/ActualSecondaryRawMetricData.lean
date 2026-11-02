import Probes.ActualSecondaryRawMetricRemainder

/-! Raw-data interfaces for the final atlas consumer. The records contain
only original profiles and actual chart/cutoff/sampling choices. The actual
map and the mean-removed metric tensor are defined without derivative order,
observation budgets or any desired error estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
private local instance rawDataTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawDataTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawDataTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : IncrementsGlobalPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
  (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))

def actualOriginalIncrementMap (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m) : Ep × M → V :=
  fun y => delta • incrementsGlobalPrimaryWave F hF g input length tau y+
    actualOriginalSecondarySum F hF g input length tau delta choice y

def actualOriginalObservedMeanTensor (length : ℕ) (tau delta : ℝ) (e : OpenPartialHomeomorph M D) : X → Tensor :=
  fun z => delta^2 • actualRealTensorAssembly (fun i j =>
    (incrementsGlobalPrimaryMean F hF g input length tau z.1 (e.symm z.2)
      (incrementsGlobalObservationVector (I := 𝓙) e z.2 i)
      (incrementsGlobalObservationVector (I := 𝓙) e z.2 j) : ℂ))

def actualOriginalMeanRemovedMetric (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (e : OpenPartialHomeomorph M D) : X → Tensor :=
  fun z => actualFiniteMetricError (fun w : X => F w.1 (e.symm w.2))
    (fun w => actualOriginalIncrementMap F hF g input length tau delta choice (w.1,e.symm w.2))
    (fun _ => 0) delta z-actualOriginalObservedMeanTensor F hF g input length tau delta e z

structure ActualOriginalSecondaryRawData
    (nInput nSolve j q Rsub Lprimary : ℕ) (reserve Bnd Mg Kcut : ℝ) (T Tinv : ℕ → ℝ)
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M)) (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m) where
  geometry : ActualSecondarySignedRecord Label → SubSecondary → ActualSecondaryRawGeometry F hF nSolve (j+1) ell Mg W
  coordinate : ∀ r a, (geometry r a).c = (choice r a).c
  chart : ∀ r a, (geometry r a).chart = (choice r a).chart
  phase : ∀ r a, (geometry r a).phase = actualOriginalSecondaryPhase F g r.val
  host : ∀ r a, ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ (choice r a).host (choice r a).host.source
  hostInverse : ∀ r a, ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ (choice r a).host.symm (choice r a).host.target
  hostSource : ∀ r a, (geometry r a).chart.source ⊆ ((OpenPartialHomeomorph.refl Ep).prod (choice r a).host).source
  cutoffSupport : ∀ r a, tsupport (fun y : W => (choice r a).cutoff y.val) ∩
        Subtype.val ⁻¹' (incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
          incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)) ⊆
    Subtype.val ⁻¹' (geometry r a).support
  pairSupport : ∀ r a, (geometry r a).support ⊆ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩
    incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2)
  partition : ∀ r : ActualSecondarySignedRecord Label, ∀ y,
    y ∈ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.1) ∩ incrementsGlobalRelativeSupport W (g.cutoff r.val.1.2) →
      ∑ a, (choice r a).cutoff y = 1
  cutoffSmooth : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ContDiffOn ℝ ∞ ((choice r a).cutoff ∘ b.symm) (b.symm.trans (geometry r a).chart).source
  inverseSmooth : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    ContDiffOn ℝ ∞ (b.symm.trans (geometry r a).chart).symm (b.symm.trans (geometry r a).chart).target
  hostProfiles : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    let t := b.symm.trans (geometry r a).chart
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) nSolve Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary (choice r a).host t.source (t.symm '' (geometry r a).sample) tau ell Delta
  cutoffJets : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    let t := b.symm.trans (geometry r a).chart
    ∀ k ≤ nSolve, ∀ z ∈ (geometry r a).sample,
      ell^k*‖iteratedFDeriv ℝ k ((choice r a).cutoff ∘ b.symm) (t.symm z)‖ ≤ Kcut
  inverseJets : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod (choice r a).host
    let t := b.symm.trans (geometry r a).chart
    ∀ k, 1 ≤ k → k ≤ nSolve+1 → ∀ z ∈ (geometry r a).sample,
      ell^(k-1)*‖iteratedFDeriv ℝ k t.symm z‖ ≤ Tinv k
  primaryGeometry : ActualOriginalPrimaryPhysicalGeometry F hF g

variable {F hF g input inputbar}
  {nInput nSolve j q Rsub Lprimary : ℕ} {reserve Bnd Mg Kcut : ℝ} {T Tinv : ℕ → ℝ}
  {W : Set (Ep × M)} {primary : Label → Set (Ep × M)} {ell delta tau Delta : ℝ}
  {choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m}

structure ActualOriginalSecondaryObservationData
    (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve j q Rsub Lprimary
      reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
    (Tobs : ℕ → ℝ) (Rsecondary : ℕ) (e : OpenPartialHomeomorph M D) (Omega S : Set X) where
  forward : ContMDiffOn 𝓙 𝓘(ℝ,D) ∞ e e.source
  inverse : ContMDiffOn 𝓘(ℝ,D) 𝓙 ∞ e.symm e.target
  profiles : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) nInput (q+2) j Rsub Lprimary reserve Bnd Mg T
    F hF g input inputbar W primary e Omega S tau ell Delta
  target : ∀ z ∈ Omega, z.2 ∈ e.target
  originalSmooth : ContDiffOn ℝ ∞ (fun z : X => F z.1 (e.symm z.2)) Omega
  transition : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod e
    ContDiffOn ℝ ∞ (b.symm.trans (raw.geometry r a).chart) (b.symm.trans (raw.geometry r a).chart).source
  inverseTransition : ∀ r a,
    let b := (OpenPartialHomeomorph.refl Ep).prod e
    ContDiffOn ℝ ∞ (b.symm.trans (raw.geometry r a).chart).symm (b.symm.trans (raw.geometry r a).chart).target
  domains : ActualSecondarySignedRecord Label → SubSecondary → Set X
  openDomains : ∀ r a, IsOpen (domains r a)
  domainsSubset : ∀ r a, domains r a ⊆ Omega
  activeDomains : ∀ r a, S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' (raw.geometry r a).support ⊆ domains r a
  source : ∀ r a, MapsTo (fun z : X => (z.1,e.symm z.2)) (domains r a) (raw.geometry r a).chart.source
  samples : ∀ r a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' (raw.geometry r a).support →
    (raw.geometry r a).chart (z.1,e.symm z.2) ∈ (raw.geometry r a).sample
  transitionJets : ∀ r a z, z ∈ S ∩ (fun z : X => (z.1,e.symm z.2)) ⁻¹' (raw.geometry r a).support →
    ∀ k, 1 ≤ k → k ≤ j+2 → ell^(k-1)*‖iteratedFDeriv ℝ k
      ((raw.geometry r a).chart ∘ (fun z : X => (z.1,e.symm z.2))) z‖ ≤ Tobs k
  localCount : ∀ r : ActualSecondarySignedRecord Label, ∀ z ∈ S,
    (Finset.univ.filter (fun a => (z.1,e.symm z.2) ∈ (raw.geometry r a).support)).card ≤ Rsecondary

 theorem actual_original_raw_metric_remainder_of_data
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
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
  obtain ⟨CR,hCR,hout⟩ := actual_original_raw_metric_remainder
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr) (Label := Label) (SubPrimary := SubPrimary)
    (SubSecondary := SubSecondary) nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
  refine ⟨CR,hCR,?_⟩
  intro F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw e Omega S obs
  exact hout F hF g input inputbar W primary ell delta tau Delta hdelta hdeltatau choice raw.geometry
    raw.coordinate raw.chart raw.phase raw.host raw.hostInverse raw.hostSource raw.cutoffSupport raw.pairSupport
    raw.partition raw.cutoffSmooth raw.inverseSmooth raw.hostProfiles raw.cutoffJets raw.inverseJets
    e obs.forward obs.inverse Omega S obs.profiles obs.target obs.originalSmooth raw.primaryGeometry
    obs.transition obs.inverseTransition obs.domains obs.openDomains obs.domainsSubset obs.activeDomains obs.source
    obs.samples obs.transitionJets obs.localCount

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_raw_metric_remainder_of_data
