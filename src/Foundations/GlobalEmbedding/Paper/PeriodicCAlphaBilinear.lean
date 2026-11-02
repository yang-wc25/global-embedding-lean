import GlobalEmbedding.Paper.PeriodicCAlphaBilinearJetBound
import GlobalEmbedding.Paper.PeriodicCAlphaBilinearQuotientBound

/-!
# Actual periodic Hölder carrier multiplication by a continuous bilinear value map

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-raw-bilinear-product`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Construct the actual periodic Hölder element with lift B(f(x),g(x)) from actual inputs,
using exactly their declared regularity and α≤1.

Periodicity and C^k regularity follow from the original input data and bilinear calculus.
The proved finite binomial jet bound supplies every derivative witness. Compactness gives a
finite actual flat torus diameter; the proved actual top quotient bound then supplies the
Holder witness. No product membership or extra derivative is assumed.
Source: bounded pointwise multiplication in `lem:balanced`. -/
noncomputable def periodicCAlphaBilinear {a M N L k : ℕ} {α : ℝ}
    (B : EuclideanSpace ℝ (Fin M) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin L))
    (hα : α ≤ 1) (f : PeriodicCAlphaFunction a M k α) (g : PeriodicCAlphaFunction a N k α) :
    PeriodicCAlphaFunction a L k α where
  toFun x := B (f.toFun x) (g.toFun x)
  periodic := by
    intro x m
    rw [f.periodic x m, g.periodic x m]
  contDiff := (B.contDiff.comp f.contDiff).clm_apply g.contDiff
  derivative_bounded := by
    intro j hj
    refine ⟨‖B‖ * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * ‖f‖ * ‖g‖, ?_⟩
    intro x hx
    exact periodicCAlpha_bilinear_jet_bound B f g j hj x
  holder_bounded := by
    have hcompact : IsCompact (univ : Set (PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ)))) := by
      have hrange : Set.range (toLp 2 : (Fin a → AddCircle (1 : ℝ)) →
          PiLp 2 (fun _ : Fin a ↦ AddCircle (1 : ℝ))) = univ :=
        Set.range_eq_univ.mpr (WithLp.equiv 2 (Fin a → AddCircle (1 : ℝ))).symm.surjective
      rw [← hrange]
      exact isCompact_range (PiLp.continuous_toLp _ _)
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp hcompact.isBounded
    have hdiam (x y : EuclideanSpace ℝ (Fin a)) :
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D :=
      hD (mem_univ _) (mem_univ _)
    refine ⟨2 * ‖B‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
      (1 + D ^ (1 - α)) * ‖f‖ * ‖g‖, ?_⟩
    intro x y d hd
    exact periodicCAlpha_bilinear_quotient_bound B f g hα D hdiam x y hd

#print axioms periodicCAlphaBilinear

end GlobalEmbedding.Paper
