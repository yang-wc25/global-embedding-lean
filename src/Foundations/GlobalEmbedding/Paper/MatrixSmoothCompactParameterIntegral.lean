import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smooth parameter integrals over one compact period

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 307–315. DAG node: `matrix-normed-compact-parameter-integral`.
-/

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

universe u v

namespace GlobalEmbedding.Paper

/-- A jointly `C^n` integrand, including true `C∞`, has a `C^n` parameter integral over a compact period.

Proof: at order zero use continuity of compact parametric integrals on the open parameter
subspace. For the successor step, integrate the parameter derivative and apply the induction
hypothesis with continuous linear maps as codomain. On a compact parameter ball times the
period, the next derivative is uniformly bounded. Dominated differentiation identifies the
integrated derivative as the actual derivative of the integral, proving the successor step.
Source: `prop:matrix` proof, lines 307–315. -/
theorem contDiffOn_compact_parameter_integral
    {P : Type u} {E : Type (max u v)} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ∞) (U : Set P) (hU : IsOpen U) (F : P × ℝ → E)
    (hF : ContDiffOn ℝ n F (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun p ↦ ∫ t in Icc (0 : ℝ) 1, F (p, t)) U := by
  have hfinite {E : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] (n : ℕ) (F : P × ℝ → E)
      (hF : ContDiffOn ℝ n F (U ×ˢ univ)) :
      ContDiffOn ℝ n (fun p ↦ ∫ t in Icc (0 : ℝ) 1, F (p, t)) U := by
    induction n generalizing E with
    | zero =>
      change ContDiffOn ℝ 0 (fun p ↦ ∫ t in Icc (0 : ℝ) 1, F (p, t)) U
      rw [contDiffOn_zero, continuousOn_iff_continuous_domRestrict]
      have hsub : Continuous (fun z : U × ℝ ↦ F (z.1, z.2)) := by
        exact hF.continuousOn.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
          (fun z ↦ ⟨z.1.property, mem_univ _⟩)
      let : LocallyCompactSpace U := hU.locallyCompactSpace
      exact continuous_parametric_integral_of_continuous hsub isCompact_Icc
    | succ n ih =>
      let D : P × ℝ → P →L[ℝ] E := fun z ↦
        (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P ℝ)
      have hopen : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
      have hD : ContDiffOn ℝ n D (U ×ˢ univ) := by
        exact (hF.fderiv_of_isOpen hopen (by simp)).clm_comp contDiffOn_const
      have hI := ih D hD
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).2
      refine ⟨by simp, fun p ↦ ∫ t in Icc (0 : ℝ) 1, D (p, t), hI, ?_⟩
      intro p hp
      have hslice (q : P) (hq : q ∈ U) :
          ContinuousOn (fun t : ℝ ↦ F (q, t)) (Icc 0 1) := by
        exact hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t _ ↦ ⟨hq, mem_univ t⟩)
      have hDslice : ContinuousOn (fun t : ℝ ↦ D (p, t)) (Icc 0 1) := by
        exact hD.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t _ ↦ ⟨hp, mem_univ t⟩)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
      have hclosed : closedBall p (δ / 2) ⊆ U := by
        intro q hq
        apply hball
        rw [mem_ball]
        exact lt_of_le_of_lt (mem_closedBall.mp hq) (by linarith)
      have hprod : closedBall p (δ / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ U ×ˢ univ :=
        Set.prod_mono hclosed (subset_univ _)
      obtain ⟨C, hC⟩ := ((isCompact_closedBall p (δ / 2)).prod isCompact_Icc)
        |>.exists_bound_of_continuousOn (hD.continuousOn.mono hprod)
      have hderiv (q : P) (hq : q ∈ U) (t : ℝ) :
          HasFDerivAt (fun q ↦ F (q, t)) (D (q, t)) q := by
        have hAt : ContDiffAt ℝ (n + 1 : ℕ) F (q, t) :=
          hF.contDiffAt (hopen.mem_nhds ⟨hq, mem_univ t⟩)
        exact (hAt.differentiableAt (by simp)).hasFDerivAt.comp q
          (hasFDerivAt_prodMk_left q t)
      apply (hasFDerivAt_integral_of_dominated_of_fderiv_le
        (μ := volume.restrict (Icc (0 : ℝ) 1))
        (F := fun q t ↦ F (q, t)) (F' := fun q t ↦ D (q, t)) (bound := fun _ ↦ C)
        (ball_mem_nhds p (show 0 < δ / 2 by linarith)) ?_
        (hslice p hp).integrableOn_Icc (hDslice.aestronglyMeasurable measurableSet_Icc) ?_
        (integrableOn_const isCompact_Icc.measure_ne_top) ?_).hasFDerivWithinAt
      · filter_upwards [ball_mem_nhds p (show 0 < δ / 2 by linarith)] with q hq
        exact (hslice q (hclosed (ball_subset_closedBall hq))).aestronglyMeasurable
          measurableSet_Icc
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht q hq
        exact hC (q, t) ⟨ball_subset_closedBall hq, ht⟩
      · exact .of_forall fun t q hq ↦ hderiv q (hclosed (ball_subset_closedBall hq)) t
  induction n using ENat.recTopCoe with
  | top =>
    apply contDiffOn_infty.2
    intro m
    exact hfinite m F (hF.of_le (by simp))
  | coe n => exact hfinite n F hF

#print axioms contDiffOn_compact_parameter_integral

end GlobalEmbedding.Paper
