import Probes.ActualIncrementPrimaryGlobalPhysical
import Smoothing.ParameterRound2MeanRawProfiles
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M Ep Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Yobs" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance globalPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance globalPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_original_primary_physical_from_raw_uniform
    (n length j Rsub Lprimary : ℕ) (horder : j+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta)
    (slices : Λ → Β → Ep → OpenPartialHomeomorph M D)
    (hSlices : ∀ nu beta p, slices nu beta p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hSliceInverse : ∀ nu beta, g.inverse nu beta = fun p x => (slices nu beta p).symm x)
    (hSliceTarget : ∀ nu beta z, z ∈ (g.chart nu beta).target → z.2 ∈ (slices nu beta z.1).target)
    (hinj : ∀ nu beta z, z ∈ (g.chart nu beta).target →
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (g.inverse nu beta z.1 z.2)))
    (hGram : ∀ nu beta z, z ∈ (g.chart nu beta).target →
      let pairing := incrementsTransversePairing (F z.1) (hF z.1) (g.inverse nu beta z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
      (pairing.comp pairing.adjoint).IsInvertible)
    (hNormalKernel : ∀ nu beta z (hz : z ∈ (g.chart nu beta).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse nu beta z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse nu beta z.1) z.2 a.succ)
        ⟨g.normal nu (z.1,g.inverse nu beta z.1 z.2),g.normal_mem nu beta z hz⟩ = 0)
    (hadapt : ∀ nu beta z, z ∈ (g.chart nu beta).source → g.phase nu z = (g.chart nu beta z).2 0),
    let Fobs := fun z : X => F z.1 (e.symm z.2)
    let U := fun z : X => incrementsGlobalPrimaryWave F hF g input length tau (z.1,e.symm z.2)
    ContDiffOn ℝ ∞ U O ∧ ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U) O ∧
      ∀ delta : ℝ, ∀ r ≤ j, ∀ z ∈ S,
      tau^r*‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs (fun w => delta • U w)) z‖ ≤
        C * |delta| * (tau/ell)^length * tau := by
  have hBig : 0 ≤ Mg+Bnd := add_nonneg hMg hBnd
  obtain ⟨C,hC,hout⟩ := actual_original_global_primary_physical_jets_uniform
    (M := M) (Ep := Ep) (Eq := Ep) (T0 := Tr) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n length j Lprimary Rsub horder c Bnd (Mg+Bnd) hc hBnd hBig T hT
  refine ⟨C,hC,?_⟩
  intro F hF g input inputbar W primary e O S tau ell Delta data slices hSlices hSliceInverse
    hSliceTarget hinj hGram hNormalKernel hadapt Fobs U
  let kappa := fun z : X => (z.1,e.symm z.2)
  have hsub (nu : Λ) (beta : Β) :
      incrementsGlobalRelativeSupport W (fun z => g.eta nu beta z*g.cutoff nu z) ⊆
        incrementsGlobalRelativeSupport W (g.cutoff nu) := by
    rintro _ ⟨w,hw,rfl⟩
    exact ⟨w,tsupport_mul_subset_right hw,rfl⟩
  have hRsub (nu : Λ) (z : X) (hz : z ∈ S) :
      (Finset.univ.filter (fun beta => kappa z ∈ incrementsGlobalRelativeSupport W
        (fun w => g.eta nu beta w*g.cutoff nu w))).card ≤ Rsub := by
    by_cases hp : kappa z ∈ incrementsGlobalRelativeSupport W (g.cutoff nu)
    · exact data.hRsub nu z ⟨hz,hp⟩
    · have hempty : (Finset.univ.filter (fun beta => kappa z ∈ incrementsGlobalRelativeSupport W
          (fun w => g.eta nu beta w*g.cutoff nu w))) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro beta hb
        exact hp (hsub nu beta (Finset.mem_filter.mp hb).2)
      rw [hempty,Finset.card_empty]
      exact Nat.zero_le _
  exact hout F hF g input tau ell data.htau data.htaul data.hell1 W data.prim.hW primary
    data.prim.hPrimary data.prim.hPrimarySupport data.prim.hSourceW data.prim.hChart
    data.prim.hChartInv data.prim.hInverse data.prim.hCombinedSupport data.prim.hCut
    data.prim.hNormal data.prim.hArgument data.prim.hEta data.prim.hPositive
    data.prim.hG data.prim.hJ data.prim.hT0 data.prim.hA data.prim.hB data.prim.hSecond
    slices hSlices hSliceInverse hSliceTarget hinj hGram hNormalKernel
    data.Sloc data.hSloc data.L data.A data.hL data.hInput data.hRep
    (fun nu beta z hz => (data.hReserve nu beta z hz).1)
    data.hLb data.hInputb data.hCutb data.hEtab data.hNormalb
    (fun nu beta k hk z hz => (data.hAb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hBb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hBRb nu beta k hk z hz).trans (le_add_of_nonneg_left hMg))
    kappa id (fun z => rfl) O S data.hO data.hSO data.hkappaO data.hmapWO data.U data.hU
    (fun nu beta z hz => data.hOU nu beta
      ⟨data.hCover nu ⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    data.hsource (fun nu beta z hz => hadapt nu beta _ (data.hsource nu beta hz)) data.hphi
    (fun nu beta z hz => data.hmap nu beta ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    (fun nu beta z hz k hk hkj => data.hphib nu beta k hk hkj z ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    data.hCount hRsub

#print axioms actual_original_primary_physical_from_raw_uniform
end GlobalEmbedding.Continuation
