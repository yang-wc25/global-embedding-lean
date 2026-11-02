import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Integration of a smooth family with fixed compact support

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
the local convolution differentiation step. This file applies Mathlib's
existing parametric convolution theorem to the constant function one.
It exposes the resulting ordinary parameter integral, while retaining
the open parameter domain and genuine compact integration support.
-/

open MeasureTheory
open scoped ContDiff Convolution Topology

namespace GlobalEmbedding.Offline

noncomputable section

variable {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

/-- Integrating a jointly smooth family with a common compact support
gives a smooth function on its actual open parameter domain. -/
theorem contDiffOn_compactIntegral {n : ℕ∞} {U : Set P} (hU : IsOpen U)
    {S : Set E} (hS : IsCompact S) {f : P → E → F}
    (hzero : ∀ p ∈ U, ∀ y ∉ S, f p y = 0)
    (hf : ContDiffOn ℝ n (Function.uncurry f) (U ×ˢ Set.univ)) :
    ContDiffOn ℝ n (fun p => ∫ y, f p y ∂mu) U := by
  let g : P → E → F := fun p y => f p (-y)
  have hg : ContDiffOn ℝ n (Function.uncurry g) (U ×ˢ Set.univ) := by
    exact hf.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun _ hz => ⟨hz.1, trivial⟩)
  have hcompact : IsCompact ((fun y : E => -y) '' S) := hS.image continuous_neg
  have hgz : ∀ p y, p ∈ U → y ∉ (fun y : E => -y) '' S → g p y = 0 := by
    intro p y hp hy
    apply hzero p hp (-y)
    intro h
    exact hy ⟨-y, h, neg_neg y⟩
  have h := contDiffOn_convolution_right_with_param_comp
    (μ := mu) (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : P => (0 : E))
    contDiffOn_const hU hcompact hgz
    (continuous_const.locallyIntegrable (f := fun _ : E => (1 : ℝ))) hg
  simpa only [convolution_lsmul, zero_sub, g, neg_neg, one_smul] using h

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Outside a common closed integration support, every joint derivative
vanishes on an open parameter domain, by local equality with zero. -/
theorem compactFamily_fderiv_zero {U : Set P} (hU : IsOpen U)
    {S : Set E} (hS : IsClosed S) {f : P → E → F}
    (hzero : ∀ p ∈ U, ∀ y ∉ S, f p y = 0)
    {p : P} (hp : p ∈ U) {y : E} (hy : y ∉ S) :
    fderiv ℝ (Function.uncurry f) (p, y) = 0 := by
  apply (hasFDerivAt_zero_of_eventually_const (0 : F) ?_).fderiv
  have hN : U ×ˢ Sᶜ ∈ nhds (p, y) :=
    (hU.prod hS.isOpen_compl).mem_nhds ⟨hp, hy⟩
  filter_upwards [hN] with z hz
  exact hzero z.1 hz.1 z.2 hz.2

/-- Parameter differentiation commutes with the actual integral for a
jointly C1 family with common compact support. The derivative is the
native Fréchet derivative of the row function, not a supplied surrogate. -/
theorem hasFDerivAt_compactIntegral [CompleteSpace F]
    {U : Set P} (hU : IsOpen U) {S : Set E} (hS : IsCompact S) {f : P → E → F}
    (hzero : ∀ p ∈ U, ∀ y ∉ S, f p y = 0)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ Set.univ))
    {p : P} (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ y, f q y ∂mu)
      (∫ y, fderiv ℝ (fun q => f q y) p ∂mu) p := by
  let g : P → E → F := fun q y => f q (-y)
  let S' := (fun y : E => -y) '' S
  let inl := ContinuousLinearMap.inl ℝ P E
  let M := (ContinuousLinearMap.compL ℝ P (P × E) F).flip inl
  have hg : ContDiffOn ℝ 1 (Function.uncurry g) (U ×ˢ Set.univ) :=
    hf.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun _ hz => ⟨hz.1, trivial⟩)
  have hS' : IsCompact S' := hS.image continuous_neg
  have hgz : ∀ q y, q ∈ U → y ∉ S' → g q y = 0 := by
    intro q y hq hy
    apply hzero q hq (-y)
    intro h
    exact hy ⟨-y, h, neg_neg y⟩
  have hd := hasFDerivAt_convolution_right_with_param
    (μ := mu) (ContinuousLinearMap.lsmul ℝ ℝ) hU hS' hgz
    (continuous_const.locallyIntegrable (f := fun _ : E => (1 : ℝ))) hg (p, 0) hp
  have hd' := hd.comp p inl.hasFDerivAt
  have heq : (fun q : P =>
      ((fun _ : E => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] g q) 0) =
      (fun q => ∫ y, f q y ∂mu) := by
    funext q
    simp only [convolution_lsmul, zero_sub, g, neg_neg, one_smul]
  change HasFDerivAt (fun q : P =>
      ((fun _ : E => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] g q) 0)
      ((((fun _ : E => (1 : ℝ)) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (P × E), mu]
        (fun y => fderiv ℝ (Function.uncurry g) (p, y))) 0).comp inl) p at hd'
  rw [heq] at hd'
  have hDcont : Continuous (fun y : E => fderiv ℝ (Function.uncurry g) (p, -y)) :=
    (hg.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_neg) (fun _ => ⟨hp, trivial⟩)
  have hDcompact : HasCompactSupport (fun y : E => fderiv ℝ (Function.uncurry g) (p, -y)) := by
    apply exists_compact_iff_hasCompactSupport.mp
    refine ⟨S, hS, ?_⟩
    intro y hy
    apply compactFamily_fderiv_zero hU hS'.isClosed (fun q hq z hz => hgz q z hq hz) hp
    rintro ⟨z, hz, he⟩
    apply hy
    have : z = y := neg_injective he
    simpa only [this] using hz
  have hInt := hDcont.integrable_of_hasCompactSupport (μ := mu) hDcompact
  have hconv :
      ((fun _ : E => (1 : ℝ)) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (P × E), mu]
        (fun y => fderiv ℝ (Function.uncurry g) (p, y))) 0 =
      ∫ y, fderiv ℝ (Function.uncurry g) (p, -y) ∂mu := by
    simp only [convolution, zero_sub, ContinuousLinearMap.precompR_apply]
    congr 1
    funext y
    apply ContinuousLinearMap.ext
    intro v
    change (1 : ℝ) • (fderiv ℝ (Function.uncurry g) (p, -y) v) = _
    simp
  rw [hconv] at hd'
  have hderiv : (∫ y, fderiv ℝ (Function.uncurry g) (p, -y) ∂mu).comp inl =
      ∫ y, fderiv ℝ (fun q => f q y) p ∂mu := by
    change M (∫ y, fderiv ℝ (Function.uncurry g) (p, -y) ∂mu) = _
    rw [← M.integral_comp_comm hInt]
    apply integral_congr_ae
    filter_upwards [] with y
    have hgat : ContDiffAt ℝ 1 (Function.uncurry g) (p, -y) :=
      hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, trivial⟩)
    have hmap : HasFDerivAt (fun q : P => (q, -y)) inl p :=
      (hasFDerivAt_id p).prodMk (hasFDerivAt_const (-y) p)
    have hrow := (hgat.differentiableAt one_ne_zero).hasFDerivAt.comp p hmap
    simpa only [M, inl, g, Function.comp_def, Function.uncurry_apply_pair, neg_neg,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using hrow.fderiv.symm
  rw [hderiv] at hd'
  exact hd'

end

end GlobalEmbedding.Offline
