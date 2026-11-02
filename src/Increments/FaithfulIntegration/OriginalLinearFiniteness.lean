import FaithfulIntegration.OriginalInnerCores
import FaithfulIntegration.OriginalDualFrameJets
import FaithfulIncrements.LocalPrimaryFiniteness
import AuxNormBridge.TensorAllOrderCore

/-!
# Actual all-order finiteness of the original linear tensor functionals

The same ell_nu is evaluated on the original symmetric coordinate tensors.
Internal compact host cores lie in the original source inners, so the
reverse coframe jets are paid by the ORIGINAL source transition budget.
The original Omega/Q, observation set K, and all given functions are
retained.  This manufactures finiteness; no desired coefficient profile or
all-order numerical input bound is an assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Module Filter
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation.FaithfulIntegration
open FaithfulRepair FaithfulIncrements

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [T2Space M] [T2Space P]

theorem originalDualFrameEntry_eq_repr
    (D : IncrementsOriginalNativeData n d N M P) (hd : IncrementsOriginalDomainConditions D)
    (p i : Fin D.atlas.count × Fin D.parameterCount) (a r : Fin n)
    (y : Fin (n+d) → ℝ) (hy : y ∈ actualOriginalGivenTransitionDomain D (p,i)) :
    originalDualFrameEntry D hd p i a r y =
      (bufferedNativeTensorFrame D.atlas hd.atlas_smooth p.1
        (incrementsOriginalJointPoint D.atlas D.parameterChart p y).2).repr
      (bufferedNativeTensorFrame D.atlas hd.atlas_smooth i.1
        (incrementsOriginalJointPoint D.atlas D.parameterChart p y).2 a) r := by
  let chart := originalJointCoordinateChart D
  have hy' : y ∈ ((chart p).symm.trans (chart i)).source := by
    rwa [originalJointCoordinateChart_transition_source]
  have hInv : incrementsOriginalJointPoint D.atlas D.parameterChart i
      (actualOriginalGivenTransition D p i y) =
      incrementsOriginalJointPoint D.atlas D.parameterChart p y :=
    (chart i).left_inv hy'.2
  change (bufferedNativeTensorFrame D.atlas hd.atlas_smooth p.1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i
        (actualOriginalGivenTransition D p i y)).2).repr
    (bufferedNativeTensorFrame D.atlas hd.atlas_smooth i.1
      (incrementsOriginalJointPoint D.atlas D.parameterChart i
        (actualOriginalGivenTransition D p i y)).2 a) r = _
  rw [hInv]

theorem local_primary_linear_jet_profile
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hl : IncrementsOriginalLinearSmoothInputs D)
    (Vparam : Set P) (domain : Fin D.primaryCount → Set (P × M))
    (nu : Fin D.primaryCount)
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆
      D.primaryDomain nu ∩ incrementsOriginalParameterRegion D)
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k)
    (hTransition : ∀ p i k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (p,i),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D p i) y‖ ≤ T k)
    (hSource : ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ TS k) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ i k y,
      y ∈ incrementsOriginalPrimaryEvaluation (localPrimaryData D Vparam domain) nu i →
      ‖iteratedFDeriv ℝ k (incrementsOriginalLinearArgumentCoordinates D nu i) y‖ ≤ B k := by
  classical
  let chart := originalJointCoordinateChart D
  let C := closure (domain nu) ∩ (D.parameterSet ×ˢ (univ : Set M))
  let W := D.primaryDomain nu ∩ incrementsOriginalParameterRegion D
  let f := incrementsOriginalLinearArgumentCoordinates D nu
  let V := fun i => (chart i).target ∩ (chart i).symm ⁻¹' W
  have hC : IsCompact C := hCompact.inter_right (hd.parameter_compact.isClosed.prod isClosed_univ)
  have hW : IsOpen W := (hd.primary_open nu).inter (hd.parameter_open.prod isOpen_univ)
  have hCW : C ⊆ W := fun _ hz => hClosure hz.1
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (chart i).symm.continuousOn.isOpen_inter_preimage (chart i).open_target hW
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (V i) := by
    intro i
    simpa only [V,chart,originalJointCoordinateChart_target,originalJointCoordinateChart_symm,
      W,f,incrementsOriginalPrimaryDifferentiation,preimage_inter,inter_assoc] using hl.linear_coordinates nu i
  obtain ⟨core,hCoreCompact,hSub,hInner,hCovered,hPrefix⟩ :=
    original_inner_compact_family_jet_cores D hd C W hC hW hCW inter_subset_right f hf
  let J := originalDualFrameJetProfile n d T TS
  have hJ : ∀ k, 0 ≤ J k := originalDualFrameJetProfile_nonneg T TS hT hTS
  have hOne : ∀ k (y : Fin (n+d) → ℝ),
      ‖iteratedFDeriv ℝ k (fun _ : Fin (n+d) → ℝ => (1:ℝ)) y‖ ≤ 1 := by
    intro k y
    cases k with
    | zero => simp
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_le_one]
  have hOrder : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (p : Fin D.atlas.count × Fin D.parameterCount) y,
      y ∈ incrementsOriginalPrimaryEvaluation (localPrimaryData D Vparam domain) nu p →
      ‖iteratedFDeriv ℝ k (f p) y‖ ≤ B := by
    intro k
    obtain ⟨R,hR,hCore⟩ := hPrefix k
    let B := tensorTransferCore (fun _ => 1) T J k * R
    have hB : 0 ≤ B := mul_nonneg (tensorTransferCore_nonneg (fun _ => zero_le_one) hT hJ k) hR
    refine ⟨(n:ℝ)^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
    intro p y hy
    let x := (chart p).symm y
    have hx : x ∈ ⋃ i, core i := by
      rw [← hCovered]
      exact ⟨subset_closure hy.2,hy.1.2.2.2,mem_univ _⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    let e := (chart p).symm.trans (chart i)
    have hpTarget : y ∈ (chart p).target := by
      rw [originalJointCoordinateChart_target]
      exact hy.1.1
    have he : y ∈ e.source := ⟨hpTarget,(hSub i hi).1⟩
    have hyV : y ∈ V p := ⟨hpTarget,hClosure (subset_closure hy.2)⟩
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
      exact hTransition p i l hl y ⟨hy.1,heqO ▸ he⟩
    have hFrame : ∀ a r, ContDiffOn ℝ ∞ (originalDualFrameEntry D hd p i a r) O :=
      fun a r => (originalDualFrameEntry_contDiffOn D hd p i a r).mono
        (fun _ hz => heqO ▸ hz.1)
    have hFrameJets : ∀ a r l, ‖iteratedFDeriv ℝ l (originalDualFrameEntry D hd p i a r) y‖ ≤ J l :=
      fun a r l => originalDualFrameEntry_jet_le D hd T TS hT hTS hTransition hSource
        p i a r y ⟨hy.1,heqO ▸ he⟩ (hInner i x hi) l
    apply tensor_jet_le_of_components ((hf p).contDiffAt ((hV p).mem_nhds hyV))
      k ((n:ℝ)^2*B) (mul_nonneg (sq_nonneg _) hB)
    intro a
    obtain ⟨⟨a,c⟩,rfl⟩ := finProdFinEquiv.surjective a
    let term := fun r s z => (originalDualFrameEntry D hd p i r a z *
      originalDualFrameEntry D hd p i s c z) * f i (e z) (finProdFinEquiv (r,s))
    have hterm : ∀ r s, ContDiffOn ℝ ∞ (term r s) O := by
      intro r s
      exact ((hFrame r a).mul (hFrame s c)).mul
        (((contDiffOn_pi.mp (hf i)) (finProdFinEquiv (r,s))).comp ht hmap)
    have htermBound : ∀ r s, ‖iteratedFDeriv ℝ k (term r s) y‖ ≤ B := by
      intro r s
      have hb := tensor_transferred_entry_jet_le (fun _ => 1) T J
        (fun _ => zero_le_one) hT hJ hO (hV i) contDiffOn_const (hFrame r a) (hFrame s c)
        ((contDiffOn_pi.mp (hf i)) (finProdFinEquiv (r,s))) ht hmap hyO k R
        (fun l => hOne l y) (hFrameJets r a) (hFrameJets s c) htd (by
          intro l hl
          exact (tensor_component_jet_le ((hf i).contDiffAt ((hV i).mem_nhds (hmap hyO)))
            (finProdFinEquiv (r,s)) l).trans (hCore i l hl (e y) ⟨x,hi,rfl⟩))
      simpa only [one_pow,one_mul] using hb
    have hEq : (fun z => f p z (finProdFinEquiv (a,c))) =ᶠ[𝓝 y]
        (fun z => ∑ r, ∑ s, term r s z) := by
      filter_upwards [hO.mem_nhds hyO] with z hz
      have hz0 : z ∈ actualOriginalGivenTransitionDomain D (p,i) := heqO ▸ hz.1
      have hInv : incrementsOriginalJointPoint D.atlas D.parameterChart i (e z) =
          incrementsOriginalJointPoint D.atlas D.parameterChart p z := (chart i).left_inv hz.1.2
      simp only [f, incrementsOriginalLinearArgumentCoordinates, Equiv.symm_apply_apply]
      have hpPoint : (incrementsOriginalJointPoint D.atlas D.parameterChart p z).2 ∈
          (D.atlas.chart p.1).source := (D.atlas.chart p.1).map_target hz0.1.1
      have hiPoint : (incrementsOriginalJointPoint D.atlas D.parameterChart p z).2 ∈
          (D.atlas.chart i.1).source := hz0.2.2
      rw [original_linear_argument_change D hd.atlas_smooth nu
        (incrementsOriginalJointPoint D.atlas D.parameterChart p z).1 p.1 i.1
        (incrementsOriginalJointPoint D.atlas D.parameterChart p z).2 hpPoint hiPoint a c]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [term]
      rw [originalDualFrameEntry_eq_repr D hd p i r a z hz0,
        originalDualFrameEntry_eq_repr D hd p i s c z hz0]
      dsimp only [f,incrementsOriginalLinearArgumentCoordinates]
      rw [hInv]
      simp only [finProdFinEquiv.symm_apply_apply]
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact AuxNormBridge.two_slot_sum_jet_le term
      (fun r s => (hterm r s).contDiffAt (hO.mem_nhds hyO)) k B htermBound
  choose B hB hJets using hOrder
  exact ⟨B,hB,fun i k y hy => hJets k i y hy⟩

theorem local_primary_linear_weighted_finite
    (D : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions D) (hl : IncrementsOriginalLinearSmoothInputs D)
    (V : Set P) (domain : Fin D.primaryCount → Set (P × M))
    (nu : Fin D.primaryCount) (hOpen : IsOpen (domain nu))
    (hCompact : IsCompact (closure (domain nu)))
    (hClosure : closure (domain nu) ⊆ D.primaryDomain nu ∩ incrementsOriginalParameterRegion D)
    (T TS : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTS : ∀ k, 0 ≤ TS k)
    (hTransition : ∀ p i k, 1 ≤ k → ∀ y ∈ actualOriginalGivenTransitionSample D (p,i),
      ‖iteratedFDeriv ℝ k (actualOriginalGivenTransition D p i) y‖ ≤ T k)
    (hSource : ∀ p i k, 1 ≤ k → ∀ y ∈ D.sourceNormDomain p,
      y ∈ ((D.atlas.chart p).symm.trans (D.atlas.chart i)).source →
      ‖iteratedFDeriv ℝ k ((D.atlas.chart p).symm.trans (D.atlas.chart i)) y‖ ≤ TS k)
    (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalLinearArgumentCoordinates D nu)
      (incrementsOriginalPrimaryDifferentiation (localPrimaryData D V domain) nu)
      (incrementsOriginalPrimaryEvaluation (localPrimaryData D V domain) nu) ≠ ⊤ := by
  let D' := localPrimaryData D V domain
  let O := incrementsOriginalPrimaryDifferentiation D' nu
  let S := incrementsOriginalPrimaryEvaluation D' nu
  let U := fun i => O i ∩ actualOriginalPrimaryCoordinateOpen D nu i
  have hO : ∀ i, IsOpen (O i) := fun i =>
    (actual_original_jointPoint_continuousOn D i).isOpen_inter_preimage
      (parameterRound2_originalDifferentiation_open D.atlas D.parameterChart i) hOpen
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (hO i).inter (actualOriginalPrimaryCoordinateOpen_isOpen D hd nu i)
  have hSU : ∀ i, S i ⊆ U i := by
    intro i y hy
    exact ⟨⟨hy.1.1,hy.2⟩,⟨hy.1.1,(hClosure (subset_closure hy.2)).1⟩,
      hd.parameter_subset hy.1.2.2.2,mem_univ _⟩
  rw [actual_paperAtlasWeighted_open_restrict base j ell _ O U S hO hU
    (fun _ => inter_subset_left) hSU]
  obtain ⟨B,_,hJets⟩ := local_primary_linear_jet_profile D hd hl V domain nu hCompact hClosure
    T TS hT hTS hTransition hSource
  apply paperAtlasWeighted_ne_top base j ell _ U S hU hSU
    (fun i => (hl.linear_coordinates nu i).mono inter_subset_right)
  intro i k _
  refine ⟨B k,?_⟩
  rintro _ ⟨y,rfl⟩
  exact hJets i k y y.property

end GlobalEmbedding.Continuation.FaithfulIntegration

#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.local_primary_linear_jet_profile
#print axioms GlobalEmbedding.Continuation.FaithfulIntegration.local_primary_linear_weighted_finite

