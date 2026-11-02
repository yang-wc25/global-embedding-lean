import Probes.Round3ParameterCanonicalRefinementSupply

/-! Fixed original observer profiles survive the actual repair rebind.
Current map, target tensor, normal and primary open domains may change.
Reference phase/cutoff geometry, all coordinate norm domains, and the actual
chart and eta FUNCTIONS remain the same. New chart domains need only retain
the true eta support; no compactness argument is repeated after SF is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

def round3ParameterStageData
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}) :
    IncrementsOriginalNativeData (m+1) d N M P :=
  { Ref with
    F := F
    H := H
    parameterOpen := V
    freeNormal := normal
    primaryDomain := domain
    tensorNeighborhood := neighborhood }

theorem round3Parameter_original_profiles_stage_rebase
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref)
    {Sub : Type*} [Fintype Sub]
    (g0 : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => Ref.F (p,x)))
    (Forward Inverse Meta : ℕ → ℝ)
    (hProfiles : Round3ParameterOriginalChartProfiles Ref g0 Forward Inverse Meta)
    (F : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
    (domain : Fin Ref.primaryCount → Set (P × M))
    (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm})
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Fin Ref.primaryCount) (Β := Sub)
      (fun p x => F (p,x)))
    (R : ℕ) (hg : Round3ParameterOriginalPrimaryGeometry
      (round3ParameterStageData Ref F H V normal domain neighborhood) g R)
    (hEta : g.eta = g0.eta)
    (hForward : ∀ nu a, ((g.chart nu a) : P × M → P × D) = g0.chart nu a)
    (hInverse : ∀ nu a, ((g.chart nu a).symm : P × D → P × M) = (g0.chart nu a).symm) :
    Round3ParameterOriginalChartProfiles
      (round3ParameterStageData Ref F H V normal domain neighborhood) g Forward Inverse Meta := by
  intro ell hell hell1 nu a i gN t etaN k z hz hEtaZ
  let g0N := round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g0 (Ref.parameterChart i.2)
  let q := (OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart i.1)
  let t0 := q.symm.trans (g0N.chart nu a)
  have hNF : ((gN.chart nu a) : Ep × M → X) = g0N.chart nu a := by
    funext y
    change round3ParameterChartPullback (Ref.parameterChart i.2) (g.chart nu a) y =
      round3ParameterChartPullback (Ref.parameterChart i.2) (g0.chart nu a) y
    simp only [round3ParameterChartPullback_apply]
    exact congrArg (fun v : P × D => ((Ref.parameterChart i.2) v.1,v.2))
      (congrFun (hForward nu a) ((Ref.parameterChart i.2).symm y.1,y.2))
  have hNI : ((gN.chart nu a).symm : X → Ep × M) = (g0N.chart nu a).symm := by
    funext y
    change (round3ParameterChartPullback (Ref.parameterChart i.2) (g.chart nu a)).symm y =
      (round3ParameterChartPullback (Ref.parameterChart i.2) (g0.chart nu a)).symm y
    simp only [round3ParameterChartPullback_symm_apply]
    exact congrArg (fun v : P × M => ((Ref.parameterChart i.2) v.1,v.2))
      (congrFun (hInverse nu a) ((Ref.parameterChart i.2).symm y.1,y.2))
  have hNE : gN.eta nu a = g0N.eta nu a := by
    funext y
    exact congrFun (congrFun (congrFun hEta nu) a) _
  have hTF : (t : X → X) = t0 := by
    funext y
    exact congrFun hNF (q.symm y)
  have hTI : (t.symm : X → X) = t0.symm := by
    funext y
    exact congrArg q (congrFun hNI y)
  have hEN : etaN = fun y : X => g0N.eta nu a ((g0N.chart nu a).symm y) := by
    funext y
    change gN.eta nu a ((gN.chart nu a).symm y) = _
    rw [hNE,hNI]
  have hz0 : parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas
      Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i := hz
  have hEta0 : ((Ref.parameterChart i.2).symm z.1,(Ref.atlas.chart i.1).symm z.2) ∈
      tsupport (g0.eta nu a) := by rwa [← hEta]
  have hh := hProfiles ell hell hell1 nu a i k z hz0 hEta0
  have hNativeEval := (actual_original_native_evaluation_iff Ref hd i z).mp hz0
  have hp : z.1 ∈ (Ref.parameterChart i.2).target := hd.parameter_norm_subset i.2 hNativeEval.2.1
  have hx : z.2 ∈ (Ref.atlas.chart i.1).target := hd.source_norm_subset i.1 hNativeEval.1
  have hsrc : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Ref.parameterChart i.2) (g.chart nu a)
      (hg.preserves nu a) (z.1,(Ref.atlas.chart i.1).symm z.2) hp).mpr
    exact hg.support nu a hEtaZ
  refine ⟨hsrc,t.map_source hsrc,?_⟩
  change ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Forward k ∧
    ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Inverse k ∧
    ell^k*‖iteratedFDeriv ℝ k etaN (t z)‖ ≤ Meta k
  simpa only [hTF,hTI,hEN] using hh.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_original_profiles_stage_rebase
