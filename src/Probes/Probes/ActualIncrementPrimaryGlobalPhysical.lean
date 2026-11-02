import Probes.ActualIncrementPrimaryObservedJets
import Probes.ActualIncrementPrimaryPhysicalSum
import Probes.ActualIncrementSplitScaleGlobalWave

/-! Primitive original data produce the SAME global U1 linearized metric
residual. The actual local source, finite solution, free-normal reconstruction,
support, true two-frame coordinate transport and local multiplicities are
consumed internally. B uses its necessary shift1 scale; G/J need only actual
smoothness for this residual. No displacement or residual output budget is
postulated. All constants precede fields/scales and all original parameter
derivatives remain in the joint jets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M Ep Eq T0 : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Eq] [NormedSpace ℝ Eq]
  [NormedAddCommGroup T0] [NormedSpace ℝ T0]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Yobs" => Eq × D
local notation "𝓙" => 𝓘(ℝ,D)

private local instance globalPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance globalPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance globalPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_original_global_primary_physical_jets_uniform
    (n length j Lprimary Rsub : ℕ) (horder : j+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (tau ell : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (W : Set (Ep × M)) (hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (hPrimary : ∀ ν, IsOpen (primary ν))
    (hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod 𝓙) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
    (hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := 𝓙) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target) 
    (slices : Λ → Β → Ep → OpenPartialHomeomorph M D)
    (hSlices : ∀ ν β b, slices ν β b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hSliceInverse : ∀ ν β, g.inverse ν β = fun b x => (slices ν β b).symm x)
    (hSliceTarget : ∀ ν β z, z ∈ (g.chart ν β).target → z.2 ∈ (slices ν β z.1).target)
    (hinj : ∀ ν β z, z ∈ (g.chart ν β).target →
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (g.inverse ν β z.1 z.2)))
    (hGram : ∀ ν β z, z ∈ (g.chart ν β).target →
      let b := incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
      (b.comp b.adjoint).IsInvertible)
    (hNormalKernel : ∀ ν β z (hz : z ∈ (g.chart ν β).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
        ⟨g.normal ν (z.1,g.inverse ν β z.1 z.2),g.normal_mem ν β z hz⟩ = 0)
    (Sloc : Λ → Β → Set X) (hSloc : ∀ ν β, Sloc ν β ⊆ (g.chart ν β).target)
    (Lcoord : Λ → Β → X → T0 →L[ℝ] ℝ) (Acoord : Λ → Β → X → T0)
    (hLcoord : ∀ ν β, ContDiffOn ℝ ∞ (Lcoord ν β) (g.chart ν β).target)
    (hAcoord : ∀ ν β, ContDiffOn ℝ ∞ (Acoord ν β) (g.chart ν β).target)
    (hRep : ∀ ν β z, z ∈ (g.chart ν β).target →
      Lcoord ν β z (Acoord ν β z) = g.linearArgument ν z.1 (g.inverse ν β z.1 z.2)
        (input z.1 (g.inverse ν β z.1 z.2)))
    (hReserve : ∀ ν β z, z ∈ Sloc ν β → c ≤ Lcoord ν β z (Acoord ν β z))
    (hLcoordb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β,
      ell^k * ‖iteratedFDeriv ℝ k (Lcoord ν β) z‖ ≤ Bnd)
    (hAcoordb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β,
      ell^k * ‖iteratedFDeriv ℝ k (Acoord ν β) z‖ ≤ Bnd)
    (hCutb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => g.cutoff ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hEtab : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => g.eta ν β (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hNormalb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => g.normal ν (w.1,g.inverse ν β w.1 w.2)) z‖ ≤ Bnd)
    (hAb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hSecondb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (kappa : Yobs → Ep × M)
    (parameter : Eq → Ep) (hfirst : ∀ z, (kappa z).1 = parameter z.1) (Omega S : Set Yobs) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmapW : MapsTo kappa Omega W)
    (O : Λ → Β → Set Yobs) (hO : ∀ ν β, IsOpen (O ν β))
    (hactiveO : ∀ ν β, Omega ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ O ν β)
    (hsource : ∀ ν β, MapsTo kappa (O ν β) (g.chart ν β).source)
    (hadapt : ∀ ν β y, y ∈ O ν β → g.phase ν (kappa y) = (g.chart ν β (kappa y)).2 0)
    (htransition : ∀ ν β, ContDiffOn ℝ ∞ (g.chart ν β ∘ kappa) (O ν β))
    (hsample : ∀ ν β y, y ∈ S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) → g.chart ν β (kappa y) ∈ Sloc ν β)
    (htransitionb : ∀ ν β y, y ∈ S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) → ∀ k, 1 ≤ k → k ≤ j+1 →
        ell^(k-1) * ‖iteratedFDeriv ℝ k (g.chart ν β ∘ kappa) y‖ ≤ T k)
    (hLprimary : ∀ y ∈ S, (Finset.univ.filter (fun ν => kappa y ∈
      incrementsGlobalRelativeSupport W (g.cutoff ν))).card ≤ Lprimary)
    (hRsub : ∀ ν y, y ∈ S → (Finset.univ.filter (fun β => kappa y ∈
      incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z))).card ≤ Rsub),
    let Fobs := fun z : Yobs => F (kappa z).1 (kappa z).2
    let U := incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa
    ContDiffOn ℝ ∞ U Omega ∧ ContDiffOn ℝ ∞ (actualJointMetricLinearization Fobs U) Omega ∧
      ∀ delta : ℝ, ∀ r ≤ j, ∀ y ∈ S,
      tau^r*‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs (fun z => delta • U z)) y‖ ≤
        C*|delta| *(tau/ell)^length*tau := by
  obtain ⟨K,hK,hfree⟩ := actual_original_primary_free_jets_uniform
    (I := 𝓙) (M := M) (Ep := Ep) (T := T0) (m := m) (N := N) (Λ := Λ) (Β := Β) n c Bnd hc hBnd
  let Cw := actualPrimaryPhysicalCost m N n length j Mg K 0
  let Ct := actualFastTensorChartTransferPrefix T j
  have hCw : 0 ≤ Cw := actualPrimaryPhysicalCost_nonneg m N n length j hMg hK le_rfl
  have hCt : 0 ≤ Ct := actualFastTensorChartTransferPrefix_nonneg T hT j
  refine ⟨(Lprimary*Rsub : ℕ)*Ct*Cw,by positivity,?_⟩
  intro F hF g input tau ell htau htaul hell1 W hW primary hPrimary hPrimarySupport hSourceW
    hChart hChartInv hInverse hCombinedSupport hCut hNormal hArgument hEta hPositive
    hG hJ hT0 hA hB hSecond slices hSlices hSliceInverse hSliceTarget hinj hGram hNormalKernel
    Sloc hSloc Lcoord Acoord hLcoord hAcoord hRep hReserve hLcoordb hAcoordb hCutb hEtab hNormalb
    hAb hBb hSecondb kappa parameter hfirst Omega S hOmega hSOmega hkappa hmapW O hO hactiveO
    hsource hadapt htransition hsample htransitionb hLprimary hRsub Fobs U
  have hell : 0 < ell := htau.trans_le htaul
  have hregular := actual_global_primary_extension_regular F hF g input length tau W hW
    primary hPrimary hPrimarySupport hSourceW hChart hChartInv hInverse hCombinedSupport
    hCut hNormal hArgument hEta hPositive hG hJ hT0 hA hB hSecond
  have hnative (ν : Λ) (β : Β) :
      ContDiffOn ℝ ∞ (fun z : X => g.cutoff ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target ∧
      ContDiffOn ℝ ∞ (fun z : X => g.eta ν β (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target ∧
      ContDiffOn ℝ ∞ (fun z : X => g.normal ν (z.1,g.inverse ν β z.1 z.2)) (g.chart ν β).target := by
    have hm : MapsTo (g.chart ν β).symm (g.chart ν β).target (W ∩ primary ν) :=
      fun z hz => hSourceW ν β ((g.chart ν β).map_target hz)
    have hc := ((hCut ν).comp (hChartInv ν β) hm).contDiffOn
    have he := ((hEta ν β).comp (hChartInv ν β) (fun z hz => (hm hz).1)).contDiffOn
    have hn := ((hNormal ν).comp (hChartInv ν β) hm).contDiffOn
    exact ⟨hc.congr (fun z hz => congrArg (g.cutoff ν) (hInverse ν β z hz).symm),
      he.congr (fun z hz => congrArg (g.eta ν β) (hInverse ν β z hz).symm),
      hn.congr (fun z hz => congrArg (g.normal ν) (hInverse ν β z hz).symm)⟩
  have hfreeb (ν : Λ) (β : Β) := hfree F g input ν β (Sloc ν β) (hSloc ν β)
    (Lcoord ν β) (Acoord ν β) (hLcoord ν β) (hAcoord ν β) (hRep ν β)
    (hnative ν β).1 (hnative ν β).2.1 (hnative ν β).2.2 ell tau
    (htau.trans_le htaul) htau.le (hReserve ν β) (hLcoordb ν β) (hAcoordb ν β)
    (hCutb ν β) (hEtab ν β) (hNormalb ν β)
  have hlocal (ν : Λ) (β : Β) := actual_original_primary_local_physical_split_scale_jets
    F hF g input ν β n length j horder (slices ν β) (hSlices ν β) (hSliceInverse ν β)
    (hSliceTarget ν β) (hinj ν β) (hGram ν β) (hNormalKernel ν β) (Sloc ν β) (hSloc ν β)
    tau ell Mg K htau htaul hell1 hMg hK (hA ν β) (hB ν β) (hG ν β) (hJ ν β)
    (hT0 ν β) (hSecond ν β) (hregular ν β).1 (hAb ν β) (hBb ν β) (hSecondb ν β) (hfreeb ν β)
  let pieces := fun ν β y =>
    Real.cos (g.phase ν y/tau) • incrementsGlobalPrimaryExtension F hF g input length tau true ν β y -
      Real.sin (g.phase ν y/tau) • incrementsGlobalPrimaryExtension F hF g input length tau false ν β y
  let Kp := fun ν => incrementsGlobalRelativeSupport W (g.cutoff ν)
  let Ks := fun ν β => incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)
  have hsub : ∀ ν β, Ks ν β ⊆ Kp ν := by
    intro ν β
    dsimp only [Ks,Kp]
    rw [parameterRound2_global_relativeSupport_eq W hW,parameterRound2_global_relativeSupport_eq W hW]
    exact Set.inter_subset_inter_right W tsupport_mul_subset_right
  have hsupport : ∀ ν β, tsupport (fun y : W => pieces ν β y) ⊆ Subtype.val ⁻¹' Ks ν β := by
    intro ν β
    have hR := (hregular ν β).2.2.2.2.1
    have hI := (hregular ν β).2.2.2.2.2
    have hKs : IsClosed (Subtype.val ⁻¹' Ks ν β : Set W) := by
      dsimp only [Ks]
      rw [parameterRound2_global_relativeSupport_eq W hW]
      simpa only [Set.preimage_inter,Subtype.coe_preimage_self,Set.univ_inter] using
        (isClosed_tsupport (fun z => g.eta ν β z*g.cutoff ν z)).preimage continuous_subtype_val
    apply closure_minimal _ hKs
    intro z hz
    by_contra hn
    have hr : incrementsGlobalPrimaryExtension F hF g input length tau true ν β z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w : W =>
        incrementsGlobalPrimaryExtension F hF g input length tau true ν β w) (fun h => hn (hR h))
    have hi : incrementsGlobalPrimaryExtension F hF g input length tau false ν β z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun w : W =>
        incrementsGlobalPrimaryExtension F hF g input length tau false ν β w) (fun h => hn (hI h))
    apply hz
    simp only [pieces,hr,hi,smul_zero,sub_zero]
  have hreg : ∀ ν β, ContDiffOn ℝ ∞ (pieces ν β ∘ kappa) (O ν β) := by
    intro ν β
    let localWave := actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
    have hmap : MapsTo (g.chart ν β ∘ kappa) (O ν β) (g.chart ν β).target :=
      fun z hz => (g.chart ν β).map_source (hsource ν β hz)
    apply ((hlocal ν β).1.comp (htransition ν β) hmap).congr
    intro z hz
    simp only [pieces,incrementsGlobalPrimaryExtension,if_pos (hsource ν β hz),hadapt ν β z hz,
      actualSecondaryModulation,Function.comp_def]
  have hEreg : ∀ ν β, ContDiffOn ℝ ∞
      (actualJointMetricLinearization Fobs (pieces ν β ∘ kappa)) (O ν β) := by
    intro ν β
    let localWave := actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
    let Elocal := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ g.inverse ν β z.1)
      (fun x => localWave (z.1,x)) z.2
    have he := actual_original_primary_observed_physical_eq F hF g input ν β length tau
      (slices ν β) (hSlices ν β) (hSliceInverse ν β) (hSliceTarget ν β) (hInverse ν β)
      kappa parameter (O ν β) (hO ν β) (hsource ν β) (fun z _ => hfirst z)
      (hadapt ν β) (htransition ν β) (hlocal ν β).1
    have hr := actual_joint_native_tensor_pullback_contDiffOn (g.chart ν β ∘ kappa) Elocal
      (O ν β) (g.chart ν β).target (hO ν β) (htransition ν β) (hlocal ν β).2.1
      (fun z hz => (g.chart ν β).map_source (hsource ν β hz))
    exact hr.congr he
  let Budget := Ct*Cw*(tau/ell)^length*tau
  have hBudget : 0 ≤ Budget := by dsimp only [Budget]; positivity
  have hbound : ∀ ν β, ∀ r ≤ j, ∀ y ∈ S ∩ kappa ⁻¹' Ks ν β,
      tau^r * ‖iteratedFDeriv ℝ r (actualJointMetricLinearization Fobs (pieces ν β ∘ kappa)) y‖ ≤ Budget := by
    intro ν β r hr y hy
    have hh := actual_original_primary_observed_physical_jets F hF g input ν β n length j horder
      (slices ν β) (hSlices ν β) (hSliceInverse ν β) (hSliceTarget ν β) (hinj ν β)
      (hGram ν β) (hNormalKernel ν β) (Sloc ν β) (hSloc ν β) tau ell Mg K htau htaul hell1
      hMg hK (hA ν β) (hB ν β) (hG ν β) (hJ ν β) (hT0 ν β) (hSecond ν β) (hregular ν β).1
      (hAb ν β) (hBb ν β) (hSecondb ν β) (hfreeb ν β) (hInverse ν β) kappa parameter
      (O ν β) (hO ν β) (hsource ν β) (fun z _ => hfirst z) (hadapt ν β) (htransition ν β)
      T hT y (hactiveO ν β ⟨hSOmega hy.1,hy.2⟩) (hsample ν β y hy) (htransitionb ν β y hy)
    apply (hh.2 r hr).trans
    dsimp only [Budget,Cw,Ct]
    gcongr
    exact actualFastTensorChartTransferCost_le_prefix T hT hr
  have hsum := actual_primary_physical_sum_weighted_jets Fobs pieces Kp Ks hsub W hW hsupport
    kappa Omega S hOmega hSOmega hkappa hmapW O hO hactiveO hreg hEreg Lprimary Rsub j
    hLprimary hRsub tau Budget htau hBudget hbound
  have he := actual_original_primary_wave_eq_piece_sum F hF g input length tau
  have hactual : U = fun y => ∑ ν, ∑ β, pieces ν β (kappa y) := by
    dsimp only [U]
    rw [he]
    rfl
  rw [← hactual] at hsum
  refine ⟨hsum.1,hsum.2.1,?_⟩
  intro delta r hr y hy
  exact (hsum.2.2 delta r hr y hy).trans_eq (by dsimp only [Budget]; ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_global_primary_physical_jets_uniform
