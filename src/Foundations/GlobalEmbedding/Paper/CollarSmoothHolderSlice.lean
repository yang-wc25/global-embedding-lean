import GlobalEmbedding.Paper.CollarHolderNormFromJetBounds
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSpace
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Construct an actual little Hölder slice from smooth periodic coefficient jet bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Coefficient Taylor terms are smooth and periodic. Bounds through one
additional spatial derivative place them in the actual little Hölder space with a norm bound.
-/

open Set WithLp
open scoped ContDiff NNReal

namespace GlobalEmbedding.Paper

/-- A smooth periodic lift with concrete cube jet bounds through k+1 determines an actual
little C^{k,α} element with the prescribed global lift and the expected norm estimate.

Source: Proposition `prop:collar`, proof lines 530–534, coefficient power-series terms.
Integer periodicity passes to every iterated derivative. Reduce any lift point to the fractional
part cube, giving global bounds from the supplied cube bounds. The next derivative bound and the
mean value theorem make the top jet Lipschitz; the attained flat-torus distance estimate gives its
Holder quotient bound. These are the actual raw-carrier fields, so construct that carrier element.
Its lift is genuinely C∞, putting it in the actual smooth submodule and hence its topological
closure, the little space. The proved actual norm estimate supplies the stated bound. No Holder
membership, top-jet Lipschitz property or completeness is assumed as input.
-/
theorem collar_smooth_holder_slice
    {a N k : ℕ} {α : ℝ}
    (g : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (hg : ContDiff ℝ ∞ g)
    (hperiodic : ∀ (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ),
      g (x + toLp 2 (fun i ↦ (n i : ℝ))) = g x)
    (C : ℕ → ℝ)
    (hC : ∀ j ≤ k + 1, ∀ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) → ‖iteratedFDeriv ℝ j g x‖ ≤ C j)
    (hα : α ≤ 1) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ∃ f : LittlePeriodicCAlphaFunction a N k α,
      (f : PeriodicCAlphaFunction a N k α).toFun = g ∧
      ‖f‖ ≤ (∑ j ∈ Finset.range (k + 1), C j) + C (k + 1) * D ^ (1 - α) := by
  have hjetperiodic (j : ℕ) (x : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ) :
      iteratedFDeriv ℝ j g (x + toLp 2 (fun i ↦ (n i : ℝ))) = iteratedFDeriv ℝ j g x := by
    have heq : (fun z ↦ g (z + toLp 2 (fun i ↦ (n i : ℝ)))) = g :=
      funext (fun z ↦ hperiodic z n)
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) j
      (toLp 2 (fun i ↦ (n i : ℝ))) x
    simpa only [heq] using ht.symm
  have hglobal (j : ℕ) (hj : j ≤ k + 1) (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j g x‖ ≤ C j := by
    let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
    have hy : ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
      fun i ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hxy : y + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by
      ext i
      simp [y, Int.fract_add_floor]
    have heq := hjetperiodic j y (fun i ↦ ⌊x i⌋)
    rw [hxy] at heq
    rw [heq]
    exact hC j hj y hy
  have hnext : 0 ≤ C (k + 1) :=
    (norm_nonneg _).trans (hglobal (k + 1) le_rfl 0)
  let L : ℝ≥0 := ⟨C (k + 1), hnext⟩
  have hlip : LipschitzWith L (iteratedFDeriv ℝ k g) := by
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k g) :=
      hg.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
    apply lipschitzWith_of_nnnorm_fderiv_le hdiff
    intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ k g) x‖ ≤ C (k + 1)
    rw [norm_fderiv_iteratedFDeriv]
    exact hglobal (k + 1) le_rfl x
  have hquotient := collar_periodic_holder_from_lipschitz
    (iteratedFDeriv ℝ k g) (hjetperiodic k) L hlip α hα D hdiam
  let f : PeriodicCAlphaFunction a N k α :=
    { toFun := g
      periodic := hperiodic
      contDiff := hg.of_le (by simp)
      derivative_bounded := fun j hj ↦
        ⟨C j, hC j (hj.trans (Nat.le_succ k))⟩
      holder_bounded := ⟨(L : ℝ) * D ^ (1 - α), hquotient⟩ }
  have hsmooth : f ∈ smoothPeriodicCAlphaSubmodule a N k α := by
    change ContDiff ℝ ∞ f.toFun
    exact hg
  have hlittle : f ∈ (smoothPeriodicCAlphaSubmodule a N k α).topologicalClosure :=
    (smoothPeriodicCAlphaSubmodule a N k α).le_topologicalClosure hsmooth
  refine ⟨⟨f, hlittle⟩, rfl, ?_⟩
  exact collar_holder_norm_from_jet_bounds f C
    (fun j hj ↦ hC j (hj.trans (Nat.le_succ k))) L hlip hα D hdiam

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_smooth_holder_slice
