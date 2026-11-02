import GlobalEmbedding.Paper.SmoothPeriodicLittleMembership
import GlobalEmbedding.Paper.SmoothParameterDerivative
import GlobalEmbedding.Paper.PeriodicCAlphaSmoothFamilyContinuous
import GlobalEmbedding.Paper.PeriodicCAlphaCarrierInjective
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Construct actual continuous Hölder-valued parameter derivative data from source smoothness

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-actual-parameter-derivative-data`.
-/

open WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Source joint smoothness constructs actual norm-continuous little Hölder parameter-derivative
operators with their exact pointwise lift formula. No derivative slice membership, continuous
operator family, or Hölder-norm differentiability is assumed.

Proof: the genuine pointwise parameter directional derivatives are jointly C∞ and remain
integer-periodic. The actual smooth periodic membership theorem constructs their little-space
representatives. Pointwise derivative-tensor linearity gives linearity in the direction;
finite-dimensionality makes that map bounded. Each direction's actual source-smooth slice
family is Hölder-norm continuous, and the finite-domain operator criterion gives operator-norm
continuity. Source: mixed parameter/spatial derivatives in `lem:balanced`. -/
theorem littlePeriodicCAlpha_parameter_derivative_data
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a N k : ℕ} {α : ℝ} (F : P → LittlePeriodicCAlphaFunction a N k α)
    (hF : ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (F z.1).val.toFun z.2))
    (hα : α ≤ 1) :
    ∃ A : P → P →L[ℝ] LittlePeriodicCAlphaFunction a N k α,
      Continuous A ∧ ∀ (p v : P) (x : EuclideanSpace ℝ (Fin a)),
        (A p v).val.toFun x = fderiv ℝ (fun q ↦ (F q).val.toFun x) p v := by
  let G (z : P × P) (x : EuclideanSpace ℝ (Fin a)) :=
    fderiv ℝ (fun q ↦ (F q).val.toFun x) z.1 z.2
  have hG : ContDiff ℝ ∞ (Function.uncurry G) :=
    smooth_parameter_derivative (fun p ↦ (F p).val.toFun) hF
  have hperiodic (z : P × P) (x : EuclideanSpace ℝ (Fin a)) (m : Fin a → ℤ) :
      G z (x + toLp 2 (fun i ↦ (m i : ℝ))) = G z x := by
    have heq : (fun q ↦ (F q).val.toFun (x + toLp 2 (fun i ↦ (m i : ℝ)))) =
        (fun q ↦ (F q).val.toFun x) := funext (fun q ↦ (F q).val.periodic x m)
    dsimp [G]
    rw [heq]
  have hslice (z : P × P) : ∃ f : LittlePeriodicCAlphaFunction a N k α,
      f.val.toFun = G z :=
    smooth_periodic_little_membership (G z) (hG.comp (contDiff_const.prodMk contDiff_id))
      (hperiodic z) hα k
  choose L hL using hslice
  let B (p : P) : P →ₗ[ℝ] LittlePeriodicCAlphaFunction a N k α :=
    { toFun := fun v ↦ L (p, v)
      map_add' := by
        intro v w
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext x
        change (L (p, v + w)).val.toFun x = ((L (p, v)).val + (L (p, w)).val).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.1]
        change (L (p, v + w)).val.toFun x =
          (L (p, v)).val.toFun x + (L (p, w)).val.toFun x
        rw [hL, hL, hL]
        exact (fderiv ℝ (fun q ↦ (F q).val.toFun x) p).map_add v w
      map_smul' := by
        intro c v
        apply Subtype.ext
        apply periodicCAlpha_toFun_injective
        funext x
        change (L (p, c • v)).val.toFun x = (c • (L (p, v)).val).toFun x
        rw [(periodicCAlpha_pointwise_operations a N k α).2.2]
        change (L (p, c • v)).val.toFun x = c • (L (p, v)).val.toFun x
        rw [hL, hL]
        exact (fderiv ℝ (fun q ↦ (F q).val.toFun x) p).map_smul c v }
  let A (p : P) : P →L[ℝ] LittlePeriodicCAlphaFunction a N k α :=
    (B p).toContinuousLinearMap
  have hrep (p v : P) : (A p v).val.toFun = G (p, v) := hL (p, v)
  refine ⟨A, ?_, fun p v x ↦ congrFun (hrep p v) x⟩
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_induced_rng.mpr
  apply periodicCAlpha_smooth_family_continuous (fun p ↦ (A p v).val) _ hα
  have hsource : ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ G (z.1, v) z.2) :=
    hG.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  simpa only [hrep] using hsource

#print axioms littlePeriodicCAlpha_parameter_derivative_data

end GlobalEmbedding.Paper
