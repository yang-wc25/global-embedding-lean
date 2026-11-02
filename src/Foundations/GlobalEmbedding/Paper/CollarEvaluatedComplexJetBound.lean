import GlobalEmbedding.Paper.CollarIteratedJetNorm
import GlobalEmbedding.Paper.CollarAffineJetBound
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Spatial jets of evaluated normalized complex parameter derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This supplies actual mixed-jet estimates for the canonical coefficient
functions on a real affine orbit slice.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The jth real spatial jet of an evaluated normalized nth complex joint derivative is bounded
by the joint (n+j)th derivative norm times the inverse factorial and the parameter norm product.

Source: Proposition `prop:collar`, proof lines 530–534. Evaluation at fixed parameter vectors
is a bounded complex linear map of norm at most their norm product. Scale it by the inverse
factorial and restrict its scalars to reals. The jet chain rule bounds its composition by that
operator norm. Pulling the nth joint jet back to the real affine slice costs at most one since
its linear part has norm at most one. Complex analyticity makes the nth joint jet analytic;
restriction of scalars identifies its real derivatives with the complex ones without changing
norm. The exact iterated-jet norm identity then identifies this norm with D^(n+j)g. Only local
joint analyticity at the point is used.
-/
theorem collar_evaluated_complex_jet_bound
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]
    (g : E → F) (c : E) (J : X →L[ℝ] E) (hJ : ‖J‖ ≤ 1) (x : X)
    (hg : AnalyticAt ℂ g (c + J x)) (n j : ℕ) (v : Fin n → E) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (n.factorial : ℂ)⁻¹ •
      iteratedFDeriv ℂ n g (c + J y) v) x‖ ≤
      (‖(n.factorial : ℂ)⁻¹‖ * ∏ i : Fin n, ‖v i‖) *
        ‖iteratedFDeriv ℂ (n + j) g (c + J x)‖ := by
  let q := iteratedFDeriv ℂ n g
  let K : ℝ := ∏ i : Fin n, ‖v i‖
  have hK : 0 ≤ K := Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)
  let L : (E [×n]→L[ℂ] F) →ₗ[ℂ] F :=
    { toFun := fun f ↦ f v
      map_add' := by intro f h; rfl
      map_smul' := by intro a f; rfl }
  have hL (f : E [×n]→L[ℂ] F) : ‖L f‖ ≤ K * ‖f‖ := by
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, K, mul_comm] using f.le_opNorm v
  let A := (((n.factorial : ℂ)⁻¹ • L.mkContinuous K hL).restrictScalars ℝ)
  have hA : ‖A‖ ≤ ‖(n.factorial : ℂ)⁻¹‖ * K := by
    rw [ContinuousLinearMap.norm_restrictScalars, norm_smul]
    exact mul_le_mul_of_nonneg_left (L.mkContinuous_norm_le hK hL) (norm_nonneg _)
  have hloc : AnalyticOnNhd ℂ g {c + J x} := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using hg
  have hq : AnalyticAt ℂ q (c + J x) := hloc.iteratedFDeriv n _ (mem_singleton _)
  have hqreal : ContDiffAt ℝ j q (c + J x) := hq.restrictScalars.contDiffAt
  have hqcomplex : ContDiffAt ℂ j q (c + J x) := hq.contDiffAt
  have hfull : ‖iteratedFDeriv ℝ j q (c + J x)‖ =
      ‖iteratedFDeriv ℂ (n + j) g (c + J x)‖ := by
    rw [← hqcomplex.restrictScalars_iteratedFDeriv, Function.comp_apply]
    change ‖iteratedFDeriv ℂ j q (c + J x)‖ = _
    exact collar_iterated_jet_norm g (c + J x) n j
  have hpow : ‖J‖ ^ j ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg J) hJ j
  have hpull : ‖iteratedFDeriv ℝ j (fun y ↦ q (c + J y)) x‖ ≤
      ‖iteratedFDeriv ℂ (n + j) g (c + J x)‖ := by
    apply (collar_affine_jet_bound q c J x j hqreal).trans
    rw [hfull]
    exact mul_le_of_le_one_right (norm_nonneg _) hpow
  have hslice : ContDiffAt ℝ j (fun y ↦ q (c + J y)) x :=
    hqreal.comp x (contDiffAt_const.add J.contDiff.contDiffAt)
  change ‖iteratedFDeriv ℝ j (A ∘ (fun y ↦ q (c + J y))) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_left hslice le_rfl]
  exact (A.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul hA hpull (norm_nonneg _) (mul_nonneg (norm_nonneg _) hK))

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_evaluated_complex_jet_bound
