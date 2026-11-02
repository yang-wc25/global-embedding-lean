import Smoothing.ParameterRound2GlobalCorrectionIdentity
import Smoothing.ParameterTransferBounds

/-!
# Primitive relative support of the actual global correction

The actual finite reconstruction preserves its source support. That source is
zero on every genuine zero germ of eta*cutoff. Consequently the SAME global
fullZ-minus-free correction has relative support in the original combined
cutoff support. No smoothness, support, or estimate of a desired output is
postulated. The observation zero-germ lemma uses relative support on W only.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem parameterRound2_global_relativeSupport_eq
    (W : Set (Ep × M)) (hW : IsOpen W) (f : Ep × M → ℝ) :
    incrementsGlobalRelativeSupport W f = W ∩ tsupport f := by
  unfold incrementsGlobalRelativeSupport
  change Subtype.val '' closure (Subtype.val ⁻¹' Function.support f : Set W) =
    W ∩ closure (Function.support f)
  rw [← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val (Function.support f),Set.image_preimage_eq_inter_range]
  simp only [Subtype.range_coe_subtype,Set.ofPred_mem_eq,Set.inter_comm]

theorem parameterRound2_globalCorrection_relative_support
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β)
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hsupport : incrementsGlobalRelativeSupport W
      (fun z => g.eta ν β z*g.cutoff ν z) ⊆ (g.chart ν β).source)
    (hinverse : ∀ z ∈ (g.chart ν β).target,
      (g.chart ν β).symm z = (z.1,g.inverse ν β z.1 z.2)) :
    tsupport (fun z : W => parameterRound2_globalCorrection F hF g input length tau realChannel ν β z) ⊆
      Subtype.val ⁻¹' incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z) := by
  let K := incrementsGlobalRelativeSupport W (fun z => g.eta ν β z*g.cutoff ν z)
  have hK : IsClosed (Subtype.val ⁻¹' K : Set W) := by
    dsimp only [K]
    rw [parameterRound2_global_relativeSupport_eq W hW]
    simpa only [Set.preimage_inter,Subtype.coe_preimage_self,Set.univ_inter] using
      (isClosed_tsupport (fun z => g.eta ν β z*g.cutoff ν z)).preimage continuous_subtype_val
  apply closure_minimal _ hK
  intro z hz
  by_contra hn
  apply hz
  change parameterRound2_globalCorrection F hF g input length tau realChannel ν β z.val = 0
  rw [parameterRound2_globalCorrection_eq_conditional F hF g input length tau realChannel ν β
    W hsupport hinverse z.val z.property]
  split_ifs with hsource
  · let y := g.chart ν β z.val
    have hy : y ∈ (g.chart ν β).target := (g.chart ν β).map_source hsource
    have hnot : z.val ∉ tsupport (fun w => g.eta ν β w*g.cutoff ν w) := by
      intro h
      apply hn
      change z.val ∈ incrementsGlobalRelativeSupport W (fun w => g.eta ν β w*g.cutoff ν w)
      rw [parameterRound2_global_relativeSupport_eq W hW]
      exact ⟨z.property,h⟩
    have hinvz : (g.chart ν β).symm y = z.val := (g.chart ν β).left_inv hsource
    have hcont := (g.chart ν β).symm.continuousOn.continuousAt
      ((g.chart ν β).open_target.mem_nhds hy)
    have hfreeZero : (fun w : X =>
        (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [(g.chart ν β).open_target.mem_nhds hy,
        hcont.eventually ((isClosed_tsupport (fun w => g.eta ν β w*g.cutoff ν w)).isOpen_compl.mem_nhds
          (by change (g.chart ν β).symm y ∉ tsupport (fun w => g.eta ν β w*g.cutoff ν w)
              rw [hinvz]
              exact hnot))] with w hw hw0
      have hm : g.eta ν β (w.1,g.inverse ν β w.1 w.2) *
          g.cutoff ν (w.1,g.inverse ν β w.1 w.2) = 0 := by
        simpa only [hinverse w hw] using image_eq_zero_of_notMem_tsupport hw0
      rcases mul_eq_zero.mp hm with he | he
      · simp [incrementsGlobalPrimaryLocalFree,hw,he]
      · simp [incrementsGlobalPrimaryLocalFree,hw,incrementsGlobalPrimaryB,he]
    have hsourceZero : incrementsGlobalPrimarySource F hF g input tau ν β =ᶠ[𝓝 y] 0 := by
      filter_upwards [hfreeZero] with w hw
      have hzero : incrementsModeSource (F w.1) (hF w.1) (g.inverse ν β w.1)
          (fun _ _ _ => 0) (fun _ => 0) w.2 = 0 := by
        simpa only [zero_smul] using incrementsModeSource_zero_smul (F w.1) (hF w.1)
          (g.inverse ν β w.1) (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1) w.2 0
      unfold incrementsGlobalPrimarySource
      rw [incrementsModeSource_eq_zeroFree_add,hzero,hw]
      simp only [Pi.zero_apply,map_zero,smul_zero,add_zero]
    have hnotJoint : y ∉ tsupport (incrementsGlobalPrimarySource F hF g input tau ν β) :=
      notMem_tsupport_iff_eventuallyEq.mpr hsourceZero
    have hnotSlice : y.2 ∉ tsupport
        (fun x => incrementsGlobalPrimarySource F hF g input tau ν β (y.1,x)) := by
      intro hx
      apply hnotJoint
      exact tsupport_comp_subset_preimage (incrementsGlobalPrimarySource F hF g input tau ν β)
        (f := fun x : D => (y.1,x)) (by fun_prop) hx
    let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
      if realChannel then incrementsModeRealPart else incrementsModeImagPart
    have hchannel := actual_full_mean_channel_support (F y.1) (hF y.1) (g.inverse ν β y.1)
      ch tau length (fun x => incrementsGlobalPrimarySource F hF g input tau ν β (y.1,x))
    change incrementsPrimaryReconstructedChannel (F y.1) (hF y.1) (g.inverse ν β y.1)
      ch tau length (fun x => incrementsGlobalPrimarySource F hF g input tau ν β (y.1,x)) y.2 = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hnotSlice (hchannel h))
  · rfl

/-- Relative original support suffices for an actual observation zero germ;
no global closedness of K or behavior outside W is required. -/
theorem parameterRound2_relative_observation_zero_germ
    {P0 X0 V0 : Type*} [TopologicalSpace P0] [TopologicalSpace X0] [Zero V0]
    (f : P0 → V0) (W K : Set P0) (hW : IsOpen W)
    (hsupport : tsupport (fun y : W => f y.val) ⊆ Subtype.val ⁻¹' K)
    (kappa : X0 → P0) (x : X0) (hkappa : ContinuousAt kappa x)
    (hxW : kappa x ∈ W) (hxK : kappa x ∉ K) :
    f ∘ kappa =ᶠ[𝓝 x] (fun _ => 0) := by
  have hnot : kappa x ∉ tsupport f := by
    intro h
    apply hxK
    apply hsupport (show (⟨kappa x,hxW⟩ : W) ∈ tsupport (fun y : W => f y.val) from ?_)
    change (⟨kappa x,hxW⟩ : W) ∈ closure (Subtype.val ⁻¹' Function.support f)
    rw [← hW.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (Function.support f)]
    exact h
  exact hkappa.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp hnot)

/-- The literal finite sum in one actual observation chart. Its constant is
the true local support multiplicity. Relative support on W is sufficient,
and a common shifted weight retains the reconstruction's extra ell factor. -/
theorem parameterRound2_relative_supported_sum_weighted_jets
    {P0 X0 V0 A0 : Type*} [TopologicalSpace P0]
    [NormedAddCommGroup X0] [NormedSpace ℝ X0]
    [NormedAddCommGroup V0] [NormedSpace ℝ V0] [Fintype A0]
    (f : A0 → P0 → V0) (W : Set P0) (K : A0 → Set P0) (hW : IsOpen W)
    (hsupport : ∀ a, tsupport (fun y : W => f a y.val) ⊆ Subtype.val ⁻¹' K a)
    (kappa : X0 → P0) (Omega S : Set X0) (hOmega : IsOpen Omega) (hSOmega : S ⊆ Omega)
    (hkappa : ContinuousOn kappa Omega) (hmap : MapsTo kappa Omega W)
    (U : A0 → Set X0) (hU : ∀ a, IsOpen (U a))
    (hOU : ∀ a, Omega ∩ kappa ⁻¹' K a ⊆ U a)
    (hreg : ∀ a, ContDiffOn ℝ ∞ (f a ∘ kappa) (U a))
    (R j shift : ℕ)
    (hR : ∀ x ∈ S, (Finset.univ.filter (fun a => kappa x ∈ K a)).card ≤ R)
    (ell Budget : ℝ) (hell : 0 < ell) (hBudget : 0 ≤ Budget)
    (hbound : ∀ a, ∀ k ≤ j, ∀ x ∈ S ∩ kappa ⁻¹' K a,
      ell^(k+shift) * ‖iteratedFDeriv ℝ k (f a ∘ kappa) x‖ ≤ Budget) :
    ContDiffOn ℝ ∞ (fun x => ∑ a, f a (kappa x)) Omega ∧
    ∀ k ≤ j, ∀ x ∈ S,
      ell^(k+shift) * ‖iteratedFDeriv ℝ k (fun y => ∑ a, f a (kappa y)) x‖ ≤ (R:ℝ)*Budget := by
  classical
  have hzero (a : A0) (x : X0) (hx : x ∈ Omega) (hn : kappa x ∉ K a) :
      f a ∘ kappa =ᶠ[𝓝 x] (fun _ => 0) :=
    parameterRound2_relative_observation_zero_germ (f a) W (K a) hW (hsupport a)
      kappa x (hkappa.continuousAt (hOmega.mem_nhds hx)) (hmap hx) hn
  have hfull (a : A0) : ContDiffOn ℝ ∞ (f a ∘ kappa) Omega := by
    intro x hx
    by_cases hm : kappa x ∈ K a
    · exact ((hreg a).contDiffAt ((hU a).mem_nhds (hOU a ⟨hx,hm⟩))).contDiffWithinAt
    · exact (contDiffAt_const.congr_of_eventuallyEq (hzero a x hx hm)).contDiffWithinAt
  refine ⟨ContDiffOn.sum (fun a _ => hfull a),?_⟩
  intro k hk x hx
  let active := Finset.univ.filter (fun a => kappa x ∈ K a)
  have ha : active.card ≤ R := hR x hx
  have hactive : ∀ a ∈ active, ContDiffAt ℝ ∞ (f a ∘ kappa) x :=
    fun a _ => (hfull a).contDiffAt (hOmega.mem_nhds (hSOmega hx))
  have hinactive : ∀ a ∉ active, f a ∘ kappa =ᶠ[𝓝 x] (fun _ => 0) := by
    intro a ha
    apply hzero a x (hSOmega hx)
    intro h
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hb : ∀ a ∈ active, ‖iteratedFDeriv ℝ k (f a ∘ kappa) x‖ ≤ Budget/ell^(k+shift) := by
    intro a ha
    apply (le_div_iff₀ (pow_pos hell _)).2
    simpa only [mul_comm] using hbound a k hk x ⟨hx,(Finset.mem_filter.mp ha).2⟩
  have hh := parameter_finite_sum_jet_le (fun a => f a ∘ kappa) x active R k
    (Budget/ell^(k+shift)) ha (by positivity) hactive hinactive hb
  calc
    _ ≤ ell^(k+shift) * ((R:ℝ)*(Budget/ell^(k+shift))) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hell.le _)
    _ = _ := by field_simp [(pow_pos hell (k+shift)).ne']

#print axioms parameterRound2_globalCorrection_relative_support
#print axioms parameterRound2_relative_observation_zero_germ
#print axioms parameterRound2_relative_supported_sum_weighted_jets
end GlobalEmbedding.Continuation
