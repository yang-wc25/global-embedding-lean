import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# ORIGINAL local joint input and its literal spatial slice jets

Source: `main.tex`, lem:increments, lines 594–648, finite auxiliary parameters.
DAG: `increments-joint-spatial-jet-bridge`. Exclusive worker W2.
STAGE2 ONLY: proposed statement awaiting ROOT lock; the sole sorry is expected.
No new spatial derivative, norm, carrier, mode solver or output field is defined.
-/

open scoped ContDiff
namespace GlobalEmbedding.Paper

/-- On the ORIGINAL open joint domain, genuine input joint smoothness identifies
the slice derivative with the full derivative restricted by the native spatial
inclusion, and gives joint smoothness of the first two literal spatial jets.

Proof plan, pending ROOT statement lock: at z in open O, input ContDiffOn gives
true DifferentiableAt. Native hasFDerivAt_prodMk_right differentiates x↦(p,x);
HasFDerivAt.comp and fderiv identify the first slice derivative with full fderiv
composed with native inr. Native ContDiffOn.fderiv_of_isOpen and fixed CLM
composition prove joint regularity of that expression, and equality on O transfers
it to the literal first spatial jet. Apply the same local rule to this genuine
first-jet field. For fixed p, the two first-jet expressions agree on the open slice
{x | (p,x) in O}; native derivative locality identifies its slice derivative with
the literal second spatial derivative. This supplies the final joint smoothness.
No identity outside O, nonsmooth totalized derivative identity, compactness, global
extension or desired coefficient/output smoothness assumption is used.
Source: ORIGINAL spatial differential construction (6.2) with finite parameters. -/
theorem incrementsJointSpatialJets_bridge
    {Ep Es Y : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Ep × Es → Y) (O : Set (Ep × Es)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) :
    (∀ z ∈ O, fderiv ℝ (fun x ↦ f (z.1, x)) z.2 =
      (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ Ep Es)) ∧
    ContDiffOn ℝ ∞ (fun z : Ep × Es ↦
      fderiv ℝ (fun x ↦ f (z.1, x)) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × Es ↦
      fderiv ℝ (fderiv ℝ (fun x ↦ f (z.1, x))) z.2) O := by
  have heq (z : Ep × Es) (hz : z ∈ O) :
      fderiv ℝ (fun x ↦ f (z.1, x)) z.2 =
        (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ Ep Es) := by
    have hd := (hf.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  have hfirst : ContDiffOn ℝ ∞ (fun z : Ep × Es ↦
      fderiv ℝ (fun x ↦ f (z.1, x)) z.2) O := by
    have hfull := hf.fderiv_of_isOpen hO (m := ∞) (by simp)
    exact (hfull.clm_comp contDiffOn_const).congr heq
  refine ⟨heq, hfirst, ?_⟩
  have hfull := hfirst.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hrestricted : ContDiffOn ℝ ∞ (fun z : Ep × Es ↦
      (fderiv ℝ (fun w : Ep × Es ↦
        fderiv ℝ (fun x ↦ f (w.1, x)) w.2) z).comp
          (ContinuousLinearMap.inr ℝ Ep Es)) O := hfull.clm_comp contDiffOn_const
  apply hrestricted.congr
  intro z hz
  have hd : DifferentiableAt ℝ (fun w : Ep × Es ↦
      fderiv ℝ (fun x ↦ f (w.1, x)) w.2) z :=
    (hfirst.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hins : HasFDerivAt (fun x : Es ↦ (z.1, x))
      (ContinuousLinearMap.inr ℝ Ep Es) z.2 := hasFDerivAt_prodMk_right z.1 z.2
  have hc := hd.hasFDerivAt.comp z.2 hins
  exact hc.fderiv

end GlobalEmbedding.Paper
