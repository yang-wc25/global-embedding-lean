import GlobalEmbedding.Paper.LittlePeriodicCAlphaSourceFamilySmooth
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate

/-!
# Construct actual globally smooth periodic Hölder families and their joint translations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-global-smooth-translated-family`.
-/

open WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A globally joint genuine C∞ periodic source function has an actual little Hölder slice
family which is genuinely norm C∞, as is its joint parameter/Euclidean-shift family.

Construct each actual slice by the smooth periodic membership theorem. Its exact lift formula
transfers source smoothness to the actual family, so the genuine norm-family smoothness
theorem applies. Apply it again to actual translated slices, whose underlying source is
F(p,x+h), a composition of genuine smooth maps. No Banach action smoothness or carrier data
is assumed. Open parameter-domain localization is separate.
Source: jointly smooth translated slices in the proof of `lem:balanced`. -/
theorem global_smooth_periodic_holder_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a N k : ℕ} {α : ℝ}
    (F : P → EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hperiodic : ∀ (p : P) (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ),
      F p (x + toLp 2 (fun i ↦ (m i : ℝ))) = F p x) (hα : α ≤ 1) :
    ∃ g : P → LittlePeriodicCAlphaFunction a N k α,
      (∀ p, (g p).val.toFun = F p) ∧ ContDiff ℝ ∞ g ∧
      ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦
        littlePeriodicCAlphaTranslateIsometry z.2 (g z.1)) := by
  have hslice (p : P) : ∃ g : LittlePeriodicCAlphaFunction a N k α, g.val.toFun = F p :=
    smooth_periodic_little_membership (F p) (hF.comp (contDiff_const.prodMk contDiff_id))
      (hperiodic p) hα k
  choose g hg using hslice
  refine ⟨g, hg, ?_, ?_⟩
  · apply littlePeriodicCAlpha_source_family_smooth g _ hα
    simp_rw [hg]
    exact hF
  · apply littlePeriodicCAlpha_source_family_smooth
      (fun z : P × EuclideanSpace ℝ (Fin a) ↦ littlePeriodicCAlphaTranslateIsometry z.2 (g z.1))
      _ hα
    change ContDiff ℝ ∞ (fun z : (P × EuclideanSpace ℝ (Fin a)) ×
      EuclideanSpace ℝ (Fin a) ↦ (g z.1.1).val.toFun (z.2 + z.1.2))
    simp_rw [hg]
    exact hF.comp (contDiff_fst.fst.prodMk (contDiff_snd.add contDiff_fst.snd))

#print axioms global_smooth_periodic_holder_family

end GlobalEmbedding.Paper
