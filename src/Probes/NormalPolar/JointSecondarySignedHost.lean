import NormalPolar.JointSecondarySignedBuffers
import Probes.ActualSecondaryQuadraticConstruction

/-! The actual host of a signed-phase piece is the constructed outer buffer.
The inner and outer charts retain the same global coordinate functions. Their
true transition is locally the identity, so every positive-order inverse
transition budget is one. Cutoff budgets come from the original smooth
partition on the nested compact target, before all orders and scales. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer

variable (b b' : JointSecondarySignedBuffer d i)
  (hbb : b.compactTarget ⊆ interior b'.compactTarget)

include hbb in
theorem source_in_outer : b.chart.source ⊆ b'.chart.source := by
  intro x hx
  exact ⟨hx.1,hbb (interior_subset hx.2)⟩

def hostTransition : OpenPartialHomeomorph X X :=
  ((OpenPartialHomeomorph.refl Ep).prod b'.chart).symm.trans
    ((OpenPartialHomeomorph.refl Ep).prod b.chart)

include hbb in
theorem hostTransition_target : (b.hostTransition (Ep := Ep) b').target = univ ×ˢ b.chart.target :=
  actual_secondary_host_transition_target _ _ (fun z hz => ⟨hz.1,b.source_in_outer b' hbb hz.2⟩)

include hbb in
theorem hostTransition_inverse (z : X) (hz : z ∈ (b.hostTransition b').target) :
    (b.hostTransition b').symm z = z := by
  rw [b.hostTransition_target b' hbb] at hz
  have hy : z.2 ∈ b'.chart.target := by
    rw [b'.chart_target]
    exact hbb (interior_subset (by simpa only [b.chart_target] using hz.2))
  exact Prod.ext rfl (b'.chart.right_inv hy)

include hbb in
theorem hostTransition_inverse_smooth :
    ContDiffOn ℝ ∞ (b.hostTransition (Ep := Ep) b').symm (b.hostTransition b').target :=
  contDiffOn_id.congr (fun z hz => b.hostTransition_inverse b' hbb z hz)

private theorem linear_positive_jets
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) (ell : ℝ) (k : ℕ) (hk : 1 ≤ k) (z : A) :
    ell^(k-1)*‖iteratedFDeriv ℝ k L z‖ ≤ ‖L‖ := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  cases r with
  | zero =>
    simp only [Nat.sub_self,pow_zero,one_mul,norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
    exact le_rfl
  | succ r =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ : A => L := funext (fun y => L.fderiv)
    rw [he,iteratedFDeriv_const_of_ne (by omega : r+1 ≠ 0)]
    simp only [Pi.zero_apply,norm_zero,mul_zero]
    exact L.opNorm_nonneg

include hbb in
theorem hostTransition_inverse_jets (ell : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (z : X) (hz : z ∈ (b.hostTransition b').target) :
    ell^(k-1)*‖iteratedFDeriv ℝ k (b.hostTransition b').symm z‖ ≤ 1 := by
  have he : (b.hostTransition b').symm =ᶠ[𝓝 z] (id : X → X) :=
    (show EqOn (b.hostTransition b').symm id (b.hostTransition b').target from
      b.hostTransition_inverse b' hbb).eventuallyEq_of_mem
        ((b.hostTransition b').open_target.mem_nhds hz)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact (linear_positive_jets (ContinuousLinearMap.id ℝ X) ell k hk z).trans
    (ContinuousLinearMap.norm_id_le)

theorem host_cutoff_smooth :
    ContDiffOn ℝ ∞ (fun z : X => d.cutoff i (b'.chart.symm z.2))
      (b.hostTransition b').source := by
  have hc : ContMDiffOn 𝓘(ℝ,D) 𝓘(ℝ,ℝ) ∞
      (d.cutoff i ∘ b'.chart.symm) b'.chart.target :=
    (d.cutoff_smooth i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas b'.maximal)
  exact hc.contDiffOn.comp contDiffOn_snd (fun z hz => hz.1.2)

include hbb in
theorem exists_host_cutoff_profile :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧ ∀ ell, 0 ≤ ell → ell ≤ 1 →
      ∀ n k, k ≤ n → ∀ z : X, z.2 ∈ b.chart.target →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => d.cutoff i (b'.chart.symm y.2))
        ((b.hostTransition b').symm z)‖ ≤ C n := by
  have hBU : b.compactTarget ⊆ b'.chart.target := by rw [b'.chart_target]; exact hbb
  have hc : ContDiffOn ℝ ∞ (fun y : D => d.cutoff i (b'.chart.symm y)) b'.chart.target :=
    ((d.cutoff_smooth i).comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas b'.maximal)).contDiffOn
  obtain ⟨C,hC,hbound⟩ := b.exists_passive_prefix_profile (Ep := Ep)
    b'.chart.target b'.chart.open_target hBU _ hc
  refine ⟨C,hC,?_⟩
  intro ell hell hell1 n k hk z hz
  have hzt : z ∈ (b.hostTransition b').target := by
    rw [b.hostTransition_target b' hbb]
    exact ⟨mem_univ _,hz⟩
  rw [b.hostTransition_inverse b' hbb z hzt]
  exact hbound ell hell hell1 n k hk z hz

theorem relative_cutoff_support :
    incrementsGlobalRelativeSupport (univ : Set (Ep × M)) (fun z => d.cutoff i z.2) ∩
      (univ ×ˢ K) ⊆ univ ×ˢ (tsupport (d.cutoff i) ∩ K) := by
  rintro z ⟨⟨w,hw,rfl⟩,hz⟩
  exact ⟨mem_univ _,
    tsupport_comp_subset_preimage (d.cutoff i) (continuous_subtype_val.snd) hw,hz.2⟩

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.hostTransition_inverse_jets
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_host_cutoff_profile
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.relative_cutoff_support
