import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaGlobalJetBound
import Mathlib.Topology.MetricSpace.Holder

open scoped Topology NNReal ContDiff
open Set WithLp

/-!
# The original periodic norm controls the actual Euclidean Hölder constant

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines382–386.
-/

namespace GlobalEmbedding.Paper

/-- The actual Euclidean top jet is Hölder with constant the original flat-torus norm.

Source: `lem:balanced`, original periodic Hölder norm and shifted Schauder estimate.
Proof: all actual derivative suprema in the original norm formula are nonnegative, so its
actual top-jet Hölder quotient supremum is at most the full norm. When the actual quotient
distance is positive, membership in the bounded supremum set gives the quotient bound;
multiply by the positive distance power. The attained lattice minimum bounds flat distance
by Euclidean distance, and nonnegative-exponent monotonicity gives the Euclidean bound.
When the flat distance is zero, that same actual minimizing lattice vector identifies the
points up to integer translation; actual jet periodicity makes their difference zero.
Finally convert the real distance bound to native HolderWith. All a,N,k≥0 and α≥0 are
retained, including empty positive-distance quotient sets. -/
theorem periodicCAlpha_top_jet_holderWith_norm {a N k : ℕ} {α : ℝ≥0}
    (f : PeriodicCAlphaFunction a N k (α : ℝ)) :
    HolderWith ‖f‖₊ α (iteratedFDeriv ℝ k f.toFun) := by
  let Q : Set ℝ := {r | ∃ x y : EuclideanSpace ℝ (Fin a),
    let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
    0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ /
      d ^ (α : ℝ)}
  have hQ : sSup Q ≤ ‖f‖ := by
    change sSup Q ≤ periodicCAlphaNorm f
    unfold periodicCAlphaNorm
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro j _
    apply Real.sSup_nonneg
    rintro r ⟨z, hz, rfl⟩
    exact norm_nonneg _
  have hp (z : EuclideanSpace ℝ (Fin a)) (n : Fin a → ℤ) :
      iteratedFDeriv ℝ k f.toFun (z + toLp 2 (fun i ↦ (n i : ℝ))) =
        iteratedFDeriv ℝ k f.toFun z := by
    have heq : (fun y ↦ f.toFun (y + toLp 2 (fun i ↦ (n i : ℝ)))) = f.toFun :=
      funext fun y ↦ f.periodic y n
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) k
      (toLp 2 (fun i ↦ (n i : ℝ))) z
    simpa only [heq] using ht.symm
  intro x y
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hdist : dist (iteratedFDeriv ℝ k f.toFun x) (iteratedFDeriv ℝ k f.toFun y) ≤
      ‖f‖ * dist x y ^ (α : ℝ) := by
    let d := dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
      (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
    obtain ⟨n, hn, hmin⟩ := periodic_flat_torus_distance_minimum x y
    have hdn : 0 ≤ d := dist_nonneg
    have hdle : d ≤ dist x y := by
      have hm := hmin (fun _ ↦ 0)
      have hzero : toLp 2 (fun _i : Fin a ↦ ((0 : ℤ) : ℝ)) =
          (0 : EuclideanSpace ℝ (Fin a)) := by ext i; simp
      rw [hzero, sub_zero] at hm
      change d ≤ ‖x - y‖ at hm
      simpa only [dist_eq_norm] using hm
    by_cases hd0 : d = 0
    · have hz : x - y - toLp 2 (fun i ↦ (n i : ℝ)) = 0 :=
        norm_eq_zero.mp (hn.symm.trans hd0)
      have hxy : x = y + toLp 2 (fun i ↦ (n i : ℝ)) := by
        apply sub_eq_zero.mp
        calc
          x - (y + toLp 2 (fun i ↦ (n i : ℝ))) =
              x - y - toLp 2 (fun i ↦ (n i : ℝ)) := by abel
          _ = 0 := hz
      rw [hxy, hp, dist_self]
      positivity
    · have hd : 0 < d := hdn.lt_of_ne' hd0
      have hquot : ‖iteratedFDeriv ℝ k f.toFun x -
          iteratedFDeriv ℝ k f.toFun y‖ / d ^ (α : ℝ) ≤ sSup Q :=
        le_csSup (periodicCAlpha_supremum_bounds f).2 ⟨x, y, hd, rfl⟩
      have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hd (α : ℝ))).mp (hquot.trans hQ)
      simpa only [dist_eq_norm] using hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hdn hdle α.coe_nonneg) (norm_nonneg _))
  exact_mod_cast hdist

/-- In order0 the original periodic forcing norm controls its actual global Euclidean
Hölder constant.

Source: `lem:balanced`, periodic shifted Schauder estimate, lines382–386.
Proof: apply the actual top-jet estimate at order0. The native zero-linear-map curry
isometry identifies the actual zeroth jet with the function value without any norm loss. -/
theorem periodicCAlpha_holderWith_norm {a N : ℕ} {α : ℝ≥0}
    (f : PeriodicCAlphaFunction a N 0 (α : ℝ)) : HolderWith ‖f‖₊ α f.toFun := by
  let I := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin a))
    (EuclideanSpace ℝ (Fin N))
  have hi : HolderWith 1 1 I := I.isometry.lipschitzWith.holderWith
  have hh := hi.comp (periodicCAlpha_top_jet_holderWith_norm f)
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, iteratedFDeriv_zero_eq_comp,
    Function.comp_def, I, LinearIsometryEquiv.apply_symm_apply] using hh

#print axioms GlobalEmbedding.Paper.periodicCAlpha_top_jet_holderWith_norm
#print axioms GlobalEmbedding.Paper.periodicCAlpha_holderWith_norm

end GlobalEmbedding.Paper
