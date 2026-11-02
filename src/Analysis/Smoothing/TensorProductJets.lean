import Smoothing.TensorTransferJets
import Smoothing.ParameterProductAtlas

/-!
# All joint derivatives of the actual product preparation

The product atlas uses the max product norm. Projection to either original
factor has operator norm at most one, in every dimension including zero.
Thus genuine separate cutoff and transition profiles give genuine joint
profiles without a chart-count factor or a dimension-dependent projection loss.
-/

open Function Set
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E F G Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A fixed norm-at-most-one source projection costs no derivative factor. -/
theorem tensor_comp_nonexpansive_linear_jet_le
    (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1) {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {x : G} (hx : L x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hpre hx,
    iteratedFDerivWithin_of_isOpen _ hU hx] at h
  rw [h]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_one₀ (norm_nonneg _) hL

/-- All mixed derivatives of the actual independent-factor transition are
bounded by the maximum of the original transition bounds. -/
theorem tensor_product_map_jet_le
    {f : E → G} {g : F → Q} {U : Set E} {V : Set F}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) {x : E × F} (hx : x.1 ∈ U) (hy : x.2 ∈ V)
    (k : ℕ) (A B : ℝ)
    (hA : ‖iteratedFDeriv ℝ k f x.1‖ ≤ A)
    (hB : ‖iteratedFDeriv ℝ k g x.2‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun z : E × F => (f z.1, g z.2)) x‖ ≤ max A B := by
  have hfr := hf.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ E F)
  have hgr := hg.comp_continuousLinearMap (ContinuousLinearMap.snd ℝ E F)
  have hfat := hfr.contDiffAt ((hU.preimage continuous_fst).mem_nhds hx)
  have hgat := hgr.contDiffAt ((hV.preimage continuous_snd).mem_nhds hy)
  change ContDiffAt ℝ ∞ (fun z : E × F => f z.1) x at hfat
  change ContDiffAt ℝ ∞ (fun z : E × F => g z.2) x at hgat
  rw [iteratedFDeriv_prodMk hfat hgat (i := k) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max
    ((tensor_comp_nonexpansive_linear_jet_le (ContinuousLinearMap.fst ℝ E F)
      (ContinuousLinearMap.norm_fst_le ..) hU hf hx k).trans hA)
    ((tensor_comp_nonexpansive_linear_jet_le (ContinuousLinearMap.snd ℝ E F)
      (ContinuousLinearMap.norm_snd_le ..) hV hg hy k).trans hB)

/-- The literal product cutoff has the uniform Leibniz profile in the true
joint product coordinates, including every parameter/source mixed derivative. -/
theorem tensor_product_scalar_jet_le
    {f : E → ℝ} {g : F → ℝ} {U : Set E} {V : Set F}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) {x : E × F} (hx : x.1 ∈ U) (hy : x.2 ∈ V)
    (A B : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (hfB : ∀ k, ‖iteratedFDeriv ℝ k f x.1‖ ≤ A k)
    (hgB : ∀ k, ‖iteratedFDeriv ℝ k g x.2‖ ≤ B k) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z : E × F => f z.1 * g z.2) x‖ ≤
      tensorProductJetConstant A B k := by
  have hfr : ContDiffOn ℝ ∞ (fun z : E × F => f z.1) (U ×ˢ V) :=
    (hf.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ E F)).mono (fun _ h => h.1)
  have hgr : ContDiffOn ℝ ∞ (fun z : E × F => g z.2) (U ×ˢ V) :=
    (hg.comp_continuousLinearMap (ContinuousLinearMap.snd ℝ E F)).mono (fun _ h => h.2)
  apply tensor_scalar_product_jet_le A B hA hB (hU.prod hV) hfr hgr ⟨hx, hy⟩ k
  · intro j
    exact (tensor_comp_nonexpansive_linear_jet_le (ContinuousLinearMap.fst ℝ E F)
      (ContinuousLinearMap.norm_fst_le ..) hU hf hx j).trans (hfB j)
  · intro j
    exact (tensor_comp_nonexpansive_linear_jet_le (ContinuousLinearMap.snd ℝ E F)
      (ContinuousLinearMap.norm_snd_le ..) hV hg hy j).trans (hgB j)

end
end GlobalEmbedding.Offline
