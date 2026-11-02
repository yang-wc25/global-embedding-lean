import GlobalEmbedding.Paper.IncrementsGlobalPrimaryMeanBinding

/-! The original global primary channels, with their genuine combined cutoff
supports. This exposes the existing proof from the original global mean binding
without imposing the unrelated tensor decomposition or nonresonance hypotheses.
Only primitive fields, true geometry and actual chart support data are inputs;
no desired output regularity or output support is supplied. -/

noncomputable section
open Manifold Filter
open scoped ContDiff Topology BigOperators ComplexConjugate

namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]


variable (F : Ep → M → (EuclideanSpace ℝ (Fin N)))
  (hF : ∀ t, ContMDiff I 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞ (F t))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)

theorem actual_global_primary_extension_regular
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ)
    (W : Set (Ep × M)) (_hW : IsOpen W) (primary : Λ → Set (Ep × M))
    (_hPrimary : ∀ ν, IsOpen (primary ν))
    (_hPrimarySupport : ∀ ν, incrementsGlobalRelativeSupport W (g.cutoff ν) ⊆ primary ν)
    (_hSourceW : ∀ ν β, (g.chart ν β).source ⊆ W ∩ primary ν)
    (_hChart : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (g.chart ν β) (g.chart ν β).source)
    (_hChartInv : ∀ ν β, ContMDiffOn 𝓘(ℝ, Ep × (EuclideanSpace ℝ (Fin (m + 1)))) 
      ((𝓘(ℝ, Ep)).prod I) ∞ (g.chart ν β).symm (g.chart ν β).target)
    (_hInverse : ∀ ν β z, z ∈ (g.chart ν β).target →
      (g.chart ν β).symm z = (z.1, g.inverse ν β z.1 z.2))
    (_hCombinedSupport : ∀ ν β,
      incrementsGlobalRelativeSupport W (fun z ↦ g.eta ν β z * g.cutoff ν z) ⊆
        (g.chart ν β).source)
    (_hCut : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (g.cutoff ν) (W ∩ primary ν))
    (_hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, (EuclideanSpace ℝ (Fin N))) ∞
      (g.normal ν) (W ∩ primary ν))
    (_hArgument : ∀ ν, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ g.linearArgument ν z.1 z.2 (input z.1 z.2)) (W ∩ primary ν))
    (_hEta : ∀ ν β, ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞ (g.eta ν β) W)
    (_hPositive : ∀ ν z, z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) →
      0 < g.linearArgument ν z.1 z.2 (input z.1 z.2))
    (_hG : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hJ : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2))
      (g.chart ν β).target)
    (_hT0 : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (_hA : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hB : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)
      (g.chart ν β).target)
    (_hSecond : ∀ ν β, ContDiffOn ℝ ∞ (fun z : Ep × (EuclideanSpace ℝ (Fin (m + 1))) ↦
      fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i :
        (EuclideanSpace ℝ (Fin N))))
      (g.chart ν β).target) :
    ∀ ν β,
      ContDiffOn ℝ ∞ (fun z : Ep × EuclideanSpace ℝ (Fin (m+1)) =>
        (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 :
          EuclideanSpace ℝ (Fin N))) (g.chart ν β).target ∧
      ContDiffOn ℝ ∞ (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input length tau true ν β) W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input length tau false ν β) W ∧
      tsupport (fun w : W => incrementsGlobalPrimaryExtension F hF g input length tau true ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun w => g.eta ν β w * g.cutoff ν w) ∧
      tsupport (fun w : W => incrementsGlobalPrimaryExtension F hF g input length tau false ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun w => g.eta ν β w * g.cutoff ν w) := by
  classical
  have hRelative (f : Ep × M → ℝ) :
      incrementsGlobalRelativeSupport W f = W ∩ tsupport f := by
    unfold incrementsGlobalRelativeSupport
    change Subtype.val '' closure (Subtype.val ⁻¹' Function.support f : Set W) =
      W ∩ closure (Function.support f)
    rw [← _hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (Function.support f), Set.image_preimage_eq_inter_range]
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, Set.inter_comm]
  have hBfree (ν : Λ) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, ℝ) ∞
        (incrementsGlobalPrimaryB F g input ν) W := by
    intro z hzW
    by_cases hz : z ∈ tsupport (g.cutoff ν)
    · have hzS : z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
        rw [hRelative]
        exact ⟨hzW, hz⟩
      have hloc := (_hW.inter (_hPrimary ν)).mem_nhds
        ⟨hzW, _hPrimarySupport ν hzS⟩
      have hsqrt := (Real.contDiffAt_sqrt (_hPositive ν z hzS).ne').contMDiffAt.comp z
        ((_hArgument ν).contMDiffAt hloc)
      exact (((_hCut ν).contMDiffAt hloc).mul hsqrt).contMDiffWithinAt
    · apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds hz] with w hw
      simp [incrementsGlobalPrimaryB, image_eq_zero_of_notMem_tsupport hw]
  have hFree (ν : Λ) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryFree F g input tau ν) W := by
    intro z hzW
    by_cases hz : z ∈ tsupport (g.cutoff ν)
    · have hzS : z ∈ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
        rw [hRelative]
        exact ⟨hzW, hz⟩
      have hloc := (_hW.inter (_hPrimary ν)).mem_nhds
        ⟨hzW, _hPrimarySupport ν hzS⟩
      exact ((contMDiffAt_const (c := Real.sqrt 2 * tau)).mul
        ((hBfree ν).contMDiffAt (_hW.mem_nhds hzW))).smul
          ((_hNormal ν).contMDiffAt hloc) |>.contMDiffWithinAt
    · apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin N)))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (g.cutoff ν)).isOpen_compl.mem_nhds hz] with w hw
      simp [incrementsGlobalPrimaryFree, incrementsGlobalPrimaryB,
        image_eq_zero_of_notMem_tsupport hw]
  have hLocalFree (ν : Λ) (β : Β) : ContDiffOn ℝ ∞
      (fun z : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 :
          EuclideanSpace ℝ (Fin N))) (g.chart ν β).target := by
    have h := ((_hEta ν β).smul (hFree ν)).comp (_hChartInv ν β)
      (fun z hz ↦ (_hSourceW ν β ((g.chart ν β).map_target hz)).1)
    apply h.contDiffOn.congr
    intro z hz
    simp [incrementsGlobalPrimaryLocalFree, hz, _hInverse ν β z hz,
      incrementsGlobalPrimaryFree, smul_smul]
  have hSource (ν : Λ) (β : Β) : ContDiffOn ℝ ∞
      (incrementsGlobalPrimarySource F hF g input tau ν β) (g.chart ν β).target := by
    have hs := incrementsModeSource_joint_contDiffOn F hF (g.inverse ν β)
      (fun _ _ _ ↦ 0) (incrementsGlobalPrimaryLocalFree F g input tau ν β)
      (g.chart ν β).target (_hSecond ν β) (_hJ ν β) contDiffOn_const (hLocalFree ν β)
    exact incrementsModeComplexInclude.contDiff.comp_contDiffOn hs
  have hZeroSource (ν : Λ) (β : Β) (z : Ep × EuclideanSpace ℝ (Fin (m + 1))) :
      incrementsModeSource (F z.1) (hF z.1) (g.inverse ν β z.1)
        (fun _ _ _ ↦ 0) (fun _ ↦ 0) z.2 = 0 := by
    simpa only [zero_smul] using incrementsModeSource_zero_smul (F z.1) (hF z.1)
      (g.inverse ν β z.1) (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1) z.2 0
  have hSourceOfZero (ν : Λ) (β : Β)
      (z : Ep × EuclideanSpace ℝ (Fin (m + 1)))
      (hz : (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 :
        EuclideanSpace ℝ (Fin N)) = 0) :
      incrementsGlobalPrimarySource F hF g input tau ν β z = 0 := by
    unfold incrementsGlobalPrimarySource
    rw [incrementsModeSource_eq_zeroFree_add, hZeroSource, hz, map_zero,
      smul_zero, add_zero, map_zero]
  have hLocalFreeZero (ν : Λ) (β : Β)
      (z : Ep × EuclideanSpace ℝ (Fin (m + 1))) (hz : z ∈ (g.chart ν β).target)
      (hn : (g.chart ν β).symm z ∉
        incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w)) :
      (fun w : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 :
          EuclideanSpace ℝ (Fin N))) =ᶠ[𝓝 z] 0 := by
    have hnT : (g.chart ν β).symm z ∉
        tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w) := by
      intro h
      apply hn
      rw [hRelative]
      exact ⟨(_hSourceW ν β ((g.chart ν β).map_target hz)).1, h⟩
    have hc := (g.chart ν β).symm.continuousOn.continuousAt
      ((g.chart ν β).open_target.mem_nhds hz)
    filter_upwards [(g.chart ν β).open_target.mem_nhds hz,
      hc.eventually ((isClosed_tsupport
        (fun w ↦ g.eta ν β w * g.cutoff ν w)).isOpen_compl.mem_nhds hnT)] with w hw hw0
    have hmul : g.eta ν β (w.1, g.inverse ν β w.1 w.2) *
        g.cutoff ν (w.1, g.inverse ν β w.1 w.2) = 0 := by
      simpa only [_hInverse ν β w hw] using image_eq_zero_of_notMem_tsupport hw0
    rcases mul_eq_zero.mp hmul with he | he
    · simp [incrementsGlobalPrimaryLocalFree, hw, he]
    · simp [incrementsGlobalPrimaryLocalFree, hw, incrementsGlobalPrimaryB, he]
  have hPiece (ν : Λ) (β : Β) :
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input length tau true ν β) W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
        (incrementsGlobalPrimaryExtension F hF g input length tau false ν β) W ∧
      tsupport (fun w : W ↦ incrementsGlobalPrimaryExtension
        F hF g input length tau true ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w) ∧
      tsupport (fun w : W ↦ incrementsGlobalPrimaryExtension
        F hF g input length tau false ν β w) ⊆
        Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w) := by
    let K := incrementsGlobalRelativeSupport W (fun w ↦ g.eta ν β w * g.cutoff ν w)
    have hK : IsClosed (Subtype.val ⁻¹' K : Set W) := by
      dsimp only [K]
      rw [hRelative]
      simpa only [Set.preimage_inter, Subtype.coe_preimage_self, Set.univ_inter] using
        (isClosed_tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w)).preimage
          continuous_subtype_val
    have hsub : K ⊆ incrementsGlobalRelativeSupport W (g.cutoff ν) := by
      rw [show K = W ∩ tsupport (fun w ↦ g.eta ν β w * g.cutoff ν w) from hRelative _,
        hRelative]
      exact Set.inter_subset_inter_right W tsupport_mul_subset_right
    have hs : (fun z : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
        incrementsGlobalPrimarySource F hF g input tau ν β z + Complex.I •
          incrementsModeComplexInclude
            (incrementsModeSource (F z.1) (hF z.1) (g.inverse ν β z.1)
              (fun _ _ _ ↦ 0) (fun _ ↦ 0) z.2)) =
        incrementsGlobalPrimarySource F hF g input tau ν β := by
      funext z
      rw [hZeroSource, map_zero, smul_zero, add_zero]
    have hout := incrementsModeFullReconstruction_supported_chart_pullback F hF
      (g.inverse ν β) (fun _ _ _ ↦ 0) (fun _ _ _ ↦ 0)
      (incrementsGlobalPrimaryLocalFree F g input tau ν β) (fun _ _ ↦ 0)
      length tau (g.chart ν β) W _hW (fun z hz ↦ (_hSourceW ν β hz).1)
      K hK (_hCombinedSupport ν β) (_hChart ν β) (_hInverse ν β)
      (_hG ν β) (_hJ ν β) (_hT0 ν β) (_hA ν β) (_hB ν β)
      contDiffOn_const contDiffOn_const (hLocalFree ν β) contDiffOn_const
    unfold incrementsGlobalPrimarySource at hs
    rw [hs] at hout
    have hloc (z : Ep × EuclideanSpace ℝ (Fin (m + 1)))
        (hz : z ∈ (g.chart ν β).target) (hn : (g.chart ν β).symm z ∉ K) :
        z ∉ tsupport (incrementsGlobalPrimarySource F hF g input tau ν β) ∧
        z ∉ tsupport (fun w : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
          (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 :
            EuclideanSpace ℝ (Fin N))) := by
      have hv := hLocalFreeZero ν β z hz hn
      exact ⟨notMem_tsupport_iff_eventuallyEq.mpr (by
        filter_upwards [hv] with w hw
        exact hSourceOfZero ν β w hw), notMem_tsupport_iff_eventuallyEq.mpr hv⟩
    have hi := hout (hSource ν β) (by
      intro z hz hin
      by_contra hn
      have ht := hloc z hz hn
      have hEmpty : tsupport (fun _ : Ep × EuclideanSpace ℝ (Fin (m + 1)) ↦
          fun _ : Fin (m + 1) ↦ fun _ : Fin (m + 1) ↦ (0 : ℝ)) = ∅ :=
        tsupport_fun_zero
      rw [hEmpty] at hin
      simp only [Submodule.coe_zero, tsupport_fun_zero, Set.mem_union,
        Set.mem_empty_iff_false, false_or, or_false] at hin
      exact hin.elim ht.1 ht.2)
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
  exact fun ν β => ⟨hLocalFree ν β, hSource ν β, hPiece ν β⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_global_primary_extension_regular
