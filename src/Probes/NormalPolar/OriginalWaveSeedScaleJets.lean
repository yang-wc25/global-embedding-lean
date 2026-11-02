import NormalPolar.PassiveParameterJets
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Restrict the genuine joint jets to a fixed parameter value by an affine
contraction of norm one. This is an upper bound for any seed parameter space,
so compact scalar-parameter geometry gives uniform spatial raw profiles. -/

noncomputable section
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

theorem fixedParameter_iteratedFDeriv_norm_le
    {S E D V : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s₀ : S) (f : S × D → V) (O : Set (S × D))
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O)
    (z : E × D) (hz : (s₀,z.2) ∈ O) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w : E × D => f (s₀,w.2)) z‖ ≤
      ‖iteratedFDeriv ℝ j f (s₀,z.2)‖ := by
  let shift : S × D → S × D := fun y => (s₀,0)+y
  let g : S × D → V := f ∘ shift
  let O' : Set (S × D) := shift ⁻¹' O
  let L : (E × D) →L[ℝ] (S × D) := passiveParameterProjection
  have hshift : ContDiff ℝ ∞ shift := contDiff_const.add contDiff_id
  have hO' : IsOpen O' := hO.preimage hshift.continuous
  have hg : ContDiffOn ℝ ∞ g O' := hf.comp hshift.contDiffOn (fun _ hy => hy)
  have hzL : L z ∈ O' := by simpa only [O',mem_preimage,shift,L,passiveParameterProjection_apply,
    Prod.mk_add_mk,add_zero,zero_add] using hz
  have hpre : IsOpen (L ⁻¹' O') := hO'.preimage L.continuous
  have hp := L.iteratedFDerivWithin_comp_right hg hO'.uniqueDiffOn hpre.uniqueDiffOn hzL
    (show (j : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
      (((hg.comp_continuousLinearMap L).contDiffAt (hpre.mem_nhds hzL)).of_le (by simp)) hzL,
    iteratedFDerivWithin_eq_iteratedFDeriv hO'.uniqueDiffOn
      ((hg.contDiffAt (hO'.mem_nhds hzL)).of_le (by simp)) hzL] at hp
  have he : (fun w : E × D => f (s₀,w.2)) = g ∘ L := by
    funext w
    simp only [g,Function.comp_apply,shift,L,passiveParameterProjection_apply,
      Prod.mk_add_mk,add_zero,zero_add]
  have hgjet : iteratedFDeriv ℝ j g (L z) = iteratedFDeriv ℝ j f (s₀,z.2) := by
    dsimp only [g,shift,Function.comp_def]
    rw [iteratedFDeriv_comp_add_left]
    simp only [L,passiveParameterProjection_apply,Prod.mk_add_mk,add_zero,zero_add]
  rw [he,hp,hgjet]
  exact passiveParameterProjection_multilinear_norm_le _

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.fixedParameter_iteratedFDeriv_norm_le

