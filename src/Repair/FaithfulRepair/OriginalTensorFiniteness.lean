import FaithfulRepair.OriginalTensorFrames
import AuxNormBridge.TensorAllOrderCore

/-!
# All original tensor norms are finite on the same Omega, Q and K

The compact host cores are manufactured inside the given finite chart
family over K × M.  The native tensor is transported from a host core to
each original sample with both genuine source-frame factors.  Their jets
are produced from the original source-transition budget.  No tensor jet
profile, frame profile, or compact original coordinate domain is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Module Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation.FaithfulRepair

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [R1Space M] [R1Space P] [CompactSpace M]

/-- Qualitative all-order finiteness of the actual original tensor in its
same source bases.  The only supplied profiles are the original coordinate
transition profiles, with no supplied tensor or frame conclusions. -/
theorem original_tensor_jet_profile_exists
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D i l) y‖ ≤ T k)
    (hSource : ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ TS k) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ i k y,
      y ∈ incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet i →
      ‖iteratedFDeriv ℝ k (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H i) y‖ ≤ B k := by
  classical
  let chart := originalJointCoordinateChart D
  let K := D.parameterSet ×ˢ (univ : Set M)
  let W := incrementsOriginalParameterRegion D
  have hK : IsCompact K := hd.parameter_compact.prod isCompact_univ
  have hW : IsOpen W := hd.parameter_open.prod isOpen_univ
  have hKW : K ⊆ W := fun _ hz => ⟨hd.parameter_subset hz.1,hz.2⟩
  obtain ⟨core,hCompact,hSub,hCover⟩ := original_finite_chart_compact_cores chart K W hK hW hKW
    (originalJointCoordinateChart_covers D hd K Subset.rfl)
  let f := incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H
  let V := fun i => (chart i).target ∩ (chart i).symm ⁻¹' W
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (chart i).symm.continuousOn.isOpen_inter_preimage (chart i).open_target hW
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (V i) := by
    simpa only [V,chart,originalJointCoordinateChart_target,originalJointCoordinateChart_symm,W,f]
      using hs.H_coordinates
  have hImageCompact : ∀ i, IsCompact ((chart i) '' core i) := fun i =>
    (hCompact i).image_of_continuousOn ((chart i).continuousOn.mono (fun _ hx => (hSub i hx).1))
  have hImageSub : ∀ i, (chart i) '' core i ⊆ V i := by
    intro i y hy
    obtain ⟨x,hx,rfl⟩ := hy
    refine ⟨(chart i).map_source (hSub i hx).1,?_⟩
    change (chart i).symm (chart i x) ∈ W
    rw [(chart i).left_inv (hSub i hx).1]
    exact (hSub i hx).2
  have hPrefix : ∀ j : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j →
      ∀ y ∈ (chart i) '' core i, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ R := by
    intro j
    have hEach : ∀ a : (Fin D.atlas.count × Fin D.parameterCount) × Fin (j+1), ∃ R : ℝ,
        ∀ y ∈ (chart a.1) '' core a.1, ‖iteratedFDeriv ℝ (a.2 : ℕ) (f a.1) y‖ ≤ R := by
      intro a
      obtain ⟨R,hR⟩ := parameterRound2_coordinate_jets_bounded_of_compact (f a.1) (V a.1)
        ((chart a.1) '' core a.1) ((chart a.1) '' core a.1) (hV a.1) (hImageCompact a.1)
        Subset.rfl (hImageSub a.1) (hf a.1) a.2
      exact ⟨R,fun y hy => hR ⟨⟨y,hy⟩,rfl⟩⟩
    choose R hR using hEach
    obtain ⟨B,hB⟩ := (Set.finite_range R).bddAbove
    refine ⟨max 0 B,le_max_left _ _,?_⟩
    intro i k hk y hy
    let a : (Fin D.atlas.count × Fin D.parameterCount) × Fin (j+1) := (i,⟨k,by omega⟩)
    exact (hR a y hy).trans ((hB (mem_range_self a)).trans (le_max_right _ _))
  let J := fun k => TS (k+1) * ‖originalSourceProjection n d‖^k
  have hJ : ∀ k, 0 ≤ J k := fun k => mul_nonneg (hTS _) (pow_nonneg (norm_nonneg _) _)
  have hOne : ∀ k (y : Fin (n+d) → ℝ), ‖iteratedFDeriv ℝ k (fun _ : Fin (n+d) → ℝ => (1:ℝ)) y‖ ≤ 1 := by
    intro k y
    cases k with
    | zero => simp
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_le_one]
  have hOrder : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p y,
      y ∈ incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet p → ‖iteratedFDeriv ℝ k (f p) y‖ ≤ B := by
    intro k
    obtain ⟨R,hR,hCore⟩ := hPrefix k
    let B := tensorTransferCore (fun _ => 1) T J k * R
    have hB : 0 ≤ B := mul_nonneg (tensorTransferCore_nonneg (fun _ => zero_le_one) hT hJ k) hR
    refine ⟨(n:ℝ)^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
    intro p y hy
    let x := (chart p).symm y
    have hx : x ∈ ⋃ i, core i := by
      rw [← hCover]
      exact ⟨hy.2.2.2,mem_univ _⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    let e := (chart p).symm.trans (chart i)
    have hpTarget : y ∈ (chart p).target := by
      rw [originalJointCoordinateChart_target]
      exact hy.1
    have he : y ∈ e.source := ⟨hpTarget,(hSub i hi).1⟩
    have hyV : y ∈ V p := ⟨hpTarget,hd.parameter_subset hy.2.2.2,mem_univ _⟩
    let O := e.source ∩ V p
    have hO : IsOpen O := e.open_source.inter (hV p)
    have hyO : y ∈ O := ⟨he,hyV⟩
    have heqO : e.source = actualOriginalGivenTransitionDomain D (p,i) :=
      originalJointCoordinateChart_transition_source D p i
    have ht : ContDiffOn ℝ ∞ e O := by
      have hh := actualOriginalGivenTransition_contDiffOn D hd (p,i)
      rw [← originalJointCoordinateChart_transition,← heqO] at hh
      exact hh.mono inter_subset_left
    have hmap : MapsTo e O (V i) := by
      intro z hz
      refine ⟨(chart i).map_source hz.1.2,?_⟩
      have hzi : (chart p).symm z ∈ (chart i).source := hz.1.2
      change (chart i).symm (chart i ((chart p).symm z)) ∈ W
      rw [(chart i).left_inv hzi]
      exact hz.2.2
    have htd : ∀ l, 1 ≤ l → ‖iteratedFDeriv ℝ l e y‖ ≤ T l := by
      intro l hl
      exact hTransition p i l hl y ⟨hy,heqO ▸ he⟩
    have hFrame : ∀ a r, ContDiffOn ℝ ∞ (originalTensorFrameEntry D hd p i a r) O :=
      fun a r => (originalTensorFrameEntry_contDiffOn D hd p i a r).mono
        (fun _ hz => heqO ▸ hz.1)
    have hFrameJets : ∀ a r l, ‖iteratedFDeriv ℝ l (originalTensorFrameEntry D hd p i a r) y‖ ≤ J l := by
      intro a r l
      exact (originalTensorFrameEntry_jet_le D hd p i a r y (heqO ▸ he) l).trans
        (mul_le_mul_of_nonneg_right (hSource p.1 i.1 (l+1) (by omega) _ hy.2.1
          ⟨hy.1.1,(show y ∈ actualOriginalGivenTransitionDomain D (p,i) from heqO ▸ he).2.2⟩)
          (pow_nonneg (norm_nonneg _) _))
    apply tensor_jet_le_of_components ((hf p).contDiffAt ((hV p).mem_nhds hyV))
      k ((n:ℝ)^2*B) (mul_nonneg (sq_nonneg _) hB)
    intro a
    obtain ⟨⟨a,c⟩,rfl⟩ := finProdFinEquiv.surjective a
    let term := fun r s z => (originalTensorFrameEntry D hd p i a r z *
      originalTensorFrameEntry D hd p i c s z) * f i (e z) (finProdFinEquiv (r,s))
    have hterm : ∀ r s, ContDiffOn ℝ ∞ (term r s) O := by
      intro r s
      exact ((hFrame a r).mul (hFrame c s)).mul
        (((contDiffOn_pi.mp (hf i)) (finProdFinEquiv (r,s))).comp ht hmap)
    have htermBound : ∀ r s, ‖iteratedFDeriv ℝ k (term r s) y‖ ≤ B := by
      intro r s
      have hb := tensor_transferred_entry_jet_le (fun _ => 1) T J
        (fun _ => zero_le_one) hT hJ hO (hV i) contDiffOn_const (hFrame a r) (hFrame c s)
        ((contDiffOn_pi.mp (hf i)) (finProdFinEquiv (r,s))) ht hmap hyO k R
        (fun l => hOne l y) (hFrameJets a r) (hFrameJets c s) htd (by
          intro l hl
          exact (tensor_component_jet_le ((hf i).contDiffAt ((hV i).mem_nhds (hmap hyO)))
            (finProdFinEquiv (r,s)) l).trans (hCore i l hl (e y) ⟨x,hi,rfl⟩))
      simpa only [one_pow,one_mul] using hb
    have hEq : (fun z => f p z (finProdFinEquiv (a,c))) =ᶠ[𝓝 y]
        (fun z => ∑ r, ∑ s, term r s z) := by
      filter_upwards [hO.mem_nhds hyO] with z hz
      have hz0 : z ∈ actualOriginalGivenTransitionDomain D (p,i) := heqO ▸ hz.1
      have hzi : (chart p).symm z ∈ (chart i).source := hz.1.2
      have hInv : incrementsOriginalJointPoint D.atlas D.parameterChart i (e z) =
          incrementsOriginalJointPoint D.atlas D.parameterChart p z := (chart i).left_inv hzi
      have hiTarget : e z ∈ incrementsOriginalDifferentiation D.atlas D.parameterChart i := by
        simpa only [chart,originalJointCoordinateChart_target] using (hmap hz).1
      change incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H p z (finProdFinEquiv (a,c)) = _
      rw [incrementsOriginalTensorCoordinates_eq_nativeFrame D.atlas hd.atlas_smooth D.parameterChart D.H p z hz0.1]
      rw [tensorFrameComponents_change
        (bufferedNativeTensorFrame D.atlas hd.atlas_smooth i.1
          (incrementsOriginalJointPoint D.atlas D.parameterChart p z).2)]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [term,f]
      rw [incrementsOriginalTensorCoordinates_eq_nativeFrame D.atlas hd.atlas_smooth D.parameterChart D.H i (e z) hiTarget,hInv]
      dsimp only [originalTensorFrameEntry,tensorFrameTransition,incrementsOriginalJointPoint]
      ring
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact AuxNormBridge.two_slot_sum_jet_le term
      (fun r s => (hterm r s).contDiffAt (hO.mem_nhds hyO)) k B htermBound
  choose B hB hJets using hOrder
  exact ⟨B,hB,fun i k y hy => hJets k i y hy⟩

/-- Every literal weighted original tensor norm is finite on the unchanged
original differentiation and sampling domains. -/
theorem original_tensor_weighted_finite
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hs : IncrementsOriginalSmoothInputs D)
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k)
    (hTransition : ∀ i l k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (i,l),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D i l) y‖ ≤ T k)
    (hSource : ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ TS k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates D.atlas D.parameterChart D.H)
      (incrementsOriginalDifferentiation D.atlas D.parameterChart)
      (incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain
        D.parameterNormDomain D.parameterSet) ≠ ⊤ := by
  obtain ⟨B,_,hJets⟩ := original_tensor_jet_profile_exists D hd hs T TS hT hTS hTransition hSource
  let O := incrementsOriginalDifferentiation D.atlas D.parameterChart
  let S := incrementsOriginalEvaluation D.atlas D.parameterChart D.sourceNormDomain D.parameterNormDomain D.parameterSet
  let U := fun i => O i ∩ (incrementsOriginalJointPoint D.atlas D.parameterChart i) ⁻¹'
    incrementsOriginalParameterRegion D
  have hO := parameterRound2_originalDifferentiation_open D.atlas D.parameterChart
  have hU := actual_original_parameter_coordinate_region_open D hd.parameter_open
  have hSU : ∀ i, S i ⊆ U i := fun _ _ hy => ⟨hy.1,hd.parameter_subset hy.2.2.2,mem_univ _⟩
  rw [actual_paperAtlasWeighted_open_restrict base j ell _ O U S hO hU
    (fun _ => inter_subset_left) hSU]
  apply paperAtlasWeighted_ne_top base j ell _ U S hU hSU hs.H_coordinates
  intro i k _
  refine ⟨B k,?_⟩
  rintro _ ⟨y,rfl⟩
  exact hJets i k y y.property

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_tensor_jet_profile_exists
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_tensor_weighted_finite
