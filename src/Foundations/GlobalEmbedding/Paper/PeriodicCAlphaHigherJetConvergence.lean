import GlobalEmbedding.Paper.CollarHolderNormFromJetBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# One higher uniform jet convergence gives actual full Hölder norm convergence

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-higher-jet-norm-convergence`.
-/

open Filter Set WithLp
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- Global uniform convergence of genuine spatial jets through k+1 implies convergence in the
actual FULL periodic C^{k,α} norm for α≤1.

Proof: all k+2 jets of the difference eventually have uniform norm at most δ. The next jet
bound and the real mean value theorem make the top jet Lipschitz with constant δ. The actual
jet-to-Hölder estimate bounds the full norm by δ times a fixed finite constant involving the
flat torus diameter. Choose δ proportional to epsilon.
Source: mixed parameter/spatial slice estimates in the proof of `lem:balanced`. -/
theorem periodicCAlpha_tendsto_of_higher_uniform_jets
    {ι : Type*} {l : Filter ι} {a N k : ℕ} {α : ℝ}
    (F : ι → PeriodicCAlphaFunction a N k α) (g : PeriodicCAlphaFunction a N k α)
    (hF : ∀ p, ContDiff ℝ (k + 1) (F p).toFun) (hg : ContDiff ℝ (k + 1) g.toFun)
    (hlim : ∀ j ≤ k + 1, TendstoUniformly
      (fun p x ↦ iteratedFDeriv ℝ j (F p).toFun x) (iteratedFDeriv ℝ j g.toFun) l)
    (hα : α ≤ 1) : Tendsto F l (𝓝 g) := by
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
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  let B : ℝ := (k : ℝ) + 1 + D ^ (1 - α)
  have hB : 0 < B := by dsimp [B]; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * B)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hall : ∀ᶠ p in l, ∀ j : Fin (k + 2), ∀ x : EuclideanSpace ℝ (Fin a),
      ‖iteratedFDeriv ℝ j.val (F p).toFun x - iteratedFDeriv ℝ j.val g.toFun x‖ ≤ δ := by
    apply eventually_all.mpr
    intro j
    have hj : j.val ≤ k + 1 := Nat.le_of_lt_succ j.isLt
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hlim j.val hj)) δ hδ] with p hp
    intro x
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using (hp x).le
  filter_upwards [hall] with p hp
  have hsub : (F p - g).toFun = (F p).toFun - g.toFun :=
    congrArg (fun z : periodicCAlphaSubmodule a N k α ↦ z.val)
      ((periodicCAlphaCarrierEquiv a N k α).addEquiv.map_sub (F p) g)
  have hjbound (j : ℕ) (hj : j ≤ k + 1) (x : EuclideanSpace ℝ (Fin a)) :
      ‖iteratedFDeriv ℝ j (F p - g).toFun x‖ ≤ δ := by
    rw [hsub, iteratedFDeriv_sub_apply (hF p |>.of_le (by exact_mod_cast hj)).contDiffAt
      (hg.of_le (by exact_mod_cast hj)).contDiffAt]
    exact hp ⟨j, Nat.lt_succ_of_le hj⟩ x
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k (F p - g).toFun) := by
    rw [hsub]
    exact ((hF p).sub hg).differentiable_iteratedFDeriv (m := k) (by norm_cast; omega)
  have hlip : LipschitzWith (⟨δ, hδ.le⟩ : ℝ≥0) (iteratedFDeriv ℝ k (F p - g).toFun) := by
    apply lipschitzWith_of_nnnorm_fderiv_le hdiff
    intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ k (F p - g).toFun) x‖ ≤ δ
    rw [norm_fderiv_iteratedFDeriv]
    exact hjbound (k + 1) le_rfl x
  have hnorm := collar_holder_norm_from_jet_bounds (F p - g) (fun _ ↦ δ)
    (fun j hj x hx ↦ hjbound j (hj.trans (Nat.le_succ k)) x) ⟨δ, hδ.le⟩ hlip hα D hdiam
  change ‖F p - g‖ ≤ (∑ j ∈ Finset.range (k + 1), δ) + δ * D ^ (1 - α) at hnorm
  have hnorm' : ‖F p - g‖ ≤ ((k : ℝ) + 1) * δ + δ * D ^ (1 - α) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      using hnorm
  have hδeq : δ * B = ε / 2 := by dsimp [δ]; field_simp
  rw [dist_eq_norm]
  have hnorm'' : ‖F p - g‖ ≤ δ * B := by dsimp [B]; nlinarith [hnorm']
  rw [hδeq] at hnorm''
  exact hnorm''.trans_lt (half_lt_self hε)

#print axioms periodicCAlpha_tendsto_of_higher_uniform_jets

end GlobalEmbedding.Paper
