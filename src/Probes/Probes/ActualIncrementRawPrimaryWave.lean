import Smoothing.ParameterRound2MeanRawProfiles
import Probes.ActualIncrementSplitScaleGlobalWave
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

/-- The same raw packet that supplies the actual mean also produces the
actual global primary displacement through j+1. No source, solution or U1
budget is an input; only the literal adapted phase identity is used. -/
theorem actual_original_primary_wave_from_raw_uniform
    (n length j Rsub Lprimary : ℕ) (horder : j+2+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta)
    (hadapt : ∀ nu beta z, z ∈ (g.chart nu beta).source → g.phase nu z = (g.chart nu beta z).2 0),
    ContDiffOn ℝ ∞ (fun z : X => incrementsGlobalPrimaryWave F hF g input length tau (z.1,e.symm z.2)) O ∧
    ∀ delta : ℝ, ∀ k ≤ j+1, ∀ z ∈ S, tau^k*‖iteratedFDeriv ℝ k
      (fun w : X => delta • incrementsGlobalPrimaryWave F hF g input length tau (w.1,e.symm w.2)) z‖ ≤
        C * |delta| * tau := by
  have hBig : 0 ≤ Mg+Bnd := add_nonneg hMg hBnd
  obtain ⟨C,hC,hout⟩ := actual_original_global_primary_wave_split_scale_jets_uniform
    (I := I) (M := M) (Ep := Ep) (T0 := Tr) (Y := X) (m := m) (N := N) (Λ := Λ) (Β := Β)
    n length (j+1) Lprimary Rsub (by omega) c Bnd (Mg+Bnd) hc hBnd hBig T hT
  refine ⟨C,hC,?_⟩
  intro F hF g input inputbar W primary e O S tau ell Delta data hadapt
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
    data.Sloc data.hSloc data.L data.A data.hL data.hInput data.hRep
    (fun nu beta z hz => (data.hReserve nu beta z hz).1)
    data.hLb data.hInputb data.hCutb data.hEtab data.hNormalb
    (fun nu beta k hk z hz => (data.hAb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hBb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hGb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hJb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hTb nu beta k hk z hz).trans (le_add_of_nonneg_right hBnd))
    (fun nu beta k hk z hz => (data.hBRb nu beta k hk z hz).trans (le_add_of_nonneg_left hMg))
    kappa O S data.hO data.hSO data.hkappaO data.hmapWO data.U data.hU
    (fun nu beta z hz => data.hOU nu beta
      ⟨data.hCover nu ⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    data.hsource (fun nu beta z hz => hadapt nu beta _ (data.hsource nu beta hz)) data.hphi
    (fun nu beta z hz => data.hmap nu beta ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    (fun nu beta z hz k hk hkj => data.hphib nu beta k hk hkj z ⟨⟨hz.1,hsub nu beta hz.2⟩,hz.2⟩)
    data.hCount hRsub

#print axioms actual_original_primary_wave_from_raw_uniform
end GlobalEmbedding.Continuation
