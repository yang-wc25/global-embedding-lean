import NormalPolar.JointSecondarySignedBuffers
import NormalPolar.OriginalWaveSeedScaleJets
import NormalPolar.OriginalWaveSeedObserverBounds

/-! Uniform actual profiles on the fixed compact contraction interval and the
same inner signed-phase target. Constants precede both the contraction and
all requested orders and scales. The parameter space is arbitrary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.NormalPolar
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D
variable {phase : M → ℝ} {K O : Set M}
  {d : JointSecondarySignedRefinement (m := m) phase K O} {i : Fin d.count}
namespace JointSecondarySignedBuffer

variable (b b' : JointSecondarySignedBuffer d i)
  (hbb : b.compactTarget ⊆ interior b'.compactTarget)

include hbb in
theorem rescale_sample_in_outer :
    (Icc (1/2 : ℝ) 1 ×ˢ b.compactTarget) ⊆ Ioo (1/4 : ℝ) 2 ×ˢ b'.chart.target := by
  rintro ⟨c,y⟩ ⟨hc,hy⟩
  refine ⟨⟨by linarith [hc.1],by linarith [hc.2]⟩,?_⟩
  rw [b'.chart_target]
  exact hbb hy

include hbb in
theorem exists_rescaled_prefix_profile {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℝ × D → Y)
    (hf : ContDiffOn ℝ ∞ f (Ioo (1/4 : ℝ) 2 ×ˢ b'.chart.target)) :
    ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ (c : ℝ), c ∈ Icc (1/2 : ℝ) 1 →
      ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 →
      ∀ n k, k ≤ n → ∀ z : X, z.2 ∈ b.chart.target →
        ell^k * ‖iteratedFDeriv ℝ k (fun y : X => f (c,y.2)) z‖ ≤ C n := by
  let U := Ioo (1/4 : ℝ) 2 ×ˢ b'.chart.target
  let S := Icc (1/2 : ℝ) 1 ×ˢ b.compactTarget
  have hU : IsOpen U := isOpen_Ioo.prod b'.chart.open_target
  have hSU : S ⊆ U := b.rescale_sample_in_outer b' hbb
  obtain ⟨C,hC,hbound⟩ := exists_compact_native_prefix S U
    (isCompact_Icc.prod b.compact) hU hSU f hf
  refine ⟨C,hC,?_⟩
  intro c hc ell hell hell1 n k hk z hz
  have hzL : z.2 ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz
  have hs : (c,z.2) ∈ S := ⟨hc,hzL⟩
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (fun y : X => f (c,y.2)) z‖ :=
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hell hell1) (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖iteratedFDeriv ℝ k f (c,z.2)‖ :=
      fixedParameter_iteratedFDeriv_norm_le c f U hU hf z (hSU hs) k
    _ ≤ C n := hbound n k hk (c,z.2) hs

include hbb in
theorem rescaled_slice_smooth {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℝ × D → Y)
    (hf : ContDiffOn ℝ ∞ f (Ioo (1/4 : ℝ) 2 ×ˢ b'.chart.target))
    (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 1) :
    ContDiffOn ℝ ∞ (fun z : X => f (c,z.2)) (univ ×ˢ b.chart.target) := by
  apply hf.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
  intro z hz
  have hzL : z.2 ∈ b.compactTarget := by
    rw [b.chart_target] at hz
    exact interior_subset hz.2
  exact b.rescale_sample_in_outer b' hbb ⟨hc,hzL⟩

end JointSecondarySignedBuffer
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.exists_rescaled_prefix_profile
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedBuffer.rescaled_slice_smooth
