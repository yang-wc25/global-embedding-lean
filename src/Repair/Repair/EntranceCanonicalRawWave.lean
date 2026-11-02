import Repair.IncrementCanonicalCostsOriginalFree
import Probes.ActualIncrementPrimaryObservation
import Probes.ActualIncrementSplitScaleOriginalPrimary
import Smoothing.ParameterRound2OriginalFreeIndex
import Probes.ActualJointTensorChartTransfer

/-! Split-scale extension of the literal original global U1 producer. The
value coefficient B and connection T0 use ell^(k+1), as required by slow
adapted coordinates; the final U1 constant is unchanged.
The literal original global U1 from primitive given fields in the genuinely
chosen adapted charts. Free amplitude, source, finite solution, reconstructed
wave, zero-extension support and observation bounds are all conclusions. The
constant precedes fields/scales and retains only the actual local primary and
subordinate counts. Quantitative adapted-chart profiles remain explicit original
geometric obligations; they are not inferred from qualitative compactness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
universe uCanonicalM

variable {E H M Ep T0 Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T0] [NormedSpace ℝ T0]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem repairEntranceCanonical_primary_wave_jets
    (n length j Lprimary Rsub : ℕ) (horder : j+1+length ≤ n)
    (c Bnd Mg : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (M : Type uCanonicalM) [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [BoundarylessManifold I M],
    ∀ {Λ Β : Type*} [Fintype Λ] [Fintype Β] (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
      (tau ell : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (W : Set (Ep × M)) (hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (hPrimary : ∀ ν, IsOpen (primary ν))
    (hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
    (hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
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
    (hGb : ∀ ν β k, k ≤ j → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ ν β k, k ≤ j → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hT0b : ∀ ν β k, k ≤ j → ∀ z ∈ Sloc ν β, ell^(k+1) * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hSecondb : ∀ ν β k, k ≤ n → ∀ z ∈ Sloc ν β, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (kappa : Y → Ep × M) (Omega S : Set Y) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmapW : MapsTo kappa Omega W)
    (O : Λ → Β → Set Y) (hO : ∀ ν β, IsOpen (O ν β))
    (hactiveO : ∀ ν β, Omega ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ O ν β)
    (hsource : ∀ ν β, MapsTo kappa (O ν β) (g.chart ν β).source)
    (hadapt : ∀ ν β y, y ∈ O ν β → g.phase ν (kappa y) = (g.chart ν β (kappa y)).2 0)
    (htransition : ∀ ν β, ContDiffOn ℝ ∞ (g.chart ν β ∘ kappa) (O ν β))
    (hsample : ∀ ν β y, y ∈ S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) → g.chart ν β (kappa y) ∈ Sloc ν β)
    (htransitionb : ∀ ν β y, y ∈ S ∩ kappa ⁻¹' incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) → ∀ k, 1 ≤ k → k ≤ j →
        ell^(k-1) * ‖iteratedFDeriv ℝ k (g.chart ν β ∘ kappa) y‖ ≤ T k)
    (hLprimary : ∀ y ∈ S, (Finset.univ.filter (fun ν => kappa y ∈
      incrementsGlobalRelativeSupport W (g.cutoff ν))).card ≤ Lprimary)
    (hRsub : ∀ ν y, y ∈ S → (Finset.univ.filter (fun β => kappa y ∈
      incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z))).card ≤ Rsub),
    ContDiffOn ℝ ∞ (incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa) Omega ∧
    ∀ delta : ℝ, ∀ r ≤ j, ∀ y ∈ S, tau^r * ‖iteratedFDeriv ℝ r
      (fun z => delta • incrementsGlobalPrimaryWave F hF g input length tau (kappa z)) y‖ ≤ C*|delta| *tau := by
  obtain ⟨K,hK,hfree⟩ := incrementCanonical_parameterRound2_original_primary_free_jets_uniform_index
    (I := I) (Ep := Ep) (T := T0) (m := m) (N := N) n c Bnd hc hBnd
  let Cw := actualPrimaryFullWaveCost m N n length j Mg K 0 1
  let Ct := actualFastChartTransferPrefix T j
  have hCw : 0 ≤ Cw := actualPrimaryFullWaveCost_nonneg m N n length j hMg hK le_rfl 1
  have hCt : 0 ≤ Ct := actualFastChartTransferPrefix_nonneg T hT j
  refine ⟨(Lprimary*Rsub : ℕ)*Ct*Cw,by positivity,?_⟩
  intro M _ _ _ _ Λ Β _ _ F hF g input tau ell htau htaul hell1 W hW primary hPrimary hPrimarySupport hSourceW
    hChart hChartInv hInverse hCombinedSupport hCut hNormal hArgument hEta hPositive
    hG hJ hT0 hA hB hSecond Sloc hSloc Lcoord Acoord hLcoord hAcoord hRep hReserve
    hLcoordb hAcoordb hCutb hEtab hNormalb hAb hBb hGb hJb hT0b hSecondb kappa
    Omega S hOmega hSOmega hkappa hmapW O hO hactiveO hsource hadapt htransition
    hsample htransitionb hLprimary hRsub
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
  have hfreeb (ν : Λ) (β : Β) := hfree M F g input ν β (Sloc ν β) (hSloc ν β)
    (Lcoord ν β) (Acoord ν β) (hLcoord ν β) (hAcoord ν β) (hRep ν β)
    (hnative ν β).1 (hnative ν β).2.1 (hnative ν β).2.2 ell tau
    (htau.trans_le htaul) htau.le (hReserve ν β) (hLcoordb ν β) (hAcoordb ν β)
    (hCutb ν β) (hEtab ν β) (hNormalb ν β)
  have hlocal (ν : Λ) (β : Β) := actual_original_primary_local_wave_split_scale_jets F hF g input
    ν β n length j horder (Sloc ν β) (hSloc ν β) tau ell Mg K htau htaul hell1 hMg hK
    (hA ν β) (hB ν β) (hG ν β) (hJ ν β) (hT0 ν β) (hSecond ν β) (hregular ν β).1
    (hAb ν β) (hBb ν β) (hGb ν β) (hJb ν β) (hT0b ν β) (hSecondb ν β) (hfreeb ν β)
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
  have hbound : ∀ ν β, ∀ r ≤ j, ∀ y ∈ S ∩ kappa ⁻¹' Ks ν β,
      tau^r * ‖iteratedFDeriv ℝ r (pieces ν β ∘ kappa) y‖ ≤ Ct*Cw*tau := by
    intro ν β r hr y hy
    have hh := actual_original_primary_piece_observation_jets F hF g input ν β length r tau ell
      (Cw*tau) kappa (O ν β) (hO ν β) (hsource ν β) (hadapt ν β) (htransition ν β)
      (hlocal ν β).1 T hT htau htaul y (hactiveO ν β ⟨hSOmega hy.1,hy.2⟩)
      (fun k hk => (hlocal ν β).2 k (hk.trans hr) _ (hsample ν β y hy))
      (fun k hk hkr => htransitionb ν β y hy k hk (hkr.trans hr))
    exact hh.2.trans ((mul_le_mul_of_nonneg_right
      (actualFastChartTransferCost_le_prefix T hT hr) (mul_nonneg hCw htau.le)).trans_eq (by ring))
  have hsum := actual_primary_observation_sum_weighted_jets pieces Kp Ks hsub W hW hsupport
    kappa Omega S hOmega hSOmega hkappa hmapW O hO hactiveO hreg Lprimary Rsub j
    hLprimary hRsub tau (Ct*Cw*tau) htau (by positivity) hbound
  have he := actual_original_primary_wave_eq_piece_sum F hF g input length tau
  have hactual : incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa =
      fun y => ∑ ν, ∑ β, pieces ν β (kappa y) := by rw [he]; rfl
  rw [← hactual] at hsum
  refine ⟨hsum.1,?_⟩
  intro delta r hr y hy
  change tau^r * ‖iteratedFDeriv ℝ r (fun z => delta •
    (incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa) z) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hsum.1.contDiffAt (hOmega.mem_nhds (hSOmega hy))).of_le
    (by simp : (r : ℕ∞ω) ≤ ∞)),norm_smul,Real.norm_eq_abs]
  calc
    tau^r*(|delta| *‖iteratedFDeriv ℝ r (incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa) y‖) =
      |delta| *(tau^r*‖iteratedFDeriv ℝ r (incrementsGlobalPrimaryWave F hF g input length tau ∘ kappa) y‖) := by ring
    _ ≤ |delta| *((Lprimary*Rsub : ℕ)*(Ct*Cw*tau)) :=
      mul_le_mul_of_nonneg_left (hsum.2 r hr y hy) (abs_nonneg delta)
    _ = _ := by ring

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repairEntranceCanonical_primary_wave_jets
