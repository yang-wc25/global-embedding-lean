import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Actual compact positive operator fields: uniform coercivity and inverse bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line307.
DAG node: `matrix-compact-positive-operator-bound`.

The compact unit-sphere minimum proof below adapts
`OAI.PotentialABP.compact_matrix_lower_bound` from
openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
lean/OAI/Geometry/PrescribedPotential/CoordinateEllipticity.lean.
The original complex matrix field is replaced by an actual real continuous-linear
operator field. The minimum and normalization proof is retained in this setting.
Upstream license: Apache-2.0; exact license copy
`coord/external-reuse/licenses/openai-math-7ef5c0cc-LICENSE.txt`.
-/

open Set Metric
open scoped InnerProductSpace NNReal

namespace GlobalEmbedding.Paper

/-- Actual continuous positive operator fields on actual compact parameter sets
have a common positive quadratic lower bound.

Proof: adapt the cited licensed OAI compact unit-sphere minimum proof. The actual
quadratic form is continuous and positive on K×sphere0,1, so its actual compact
minimum is positive (choose1 if that set is empty). Normalize each nonzero vector
and rescale the actual quadratic inequality; the zero vector is immediate.
Source: `prop:matrix`, weighted Gram uniform positivity, line307. -/
theorem compact_positive_operator_lower_bound
    {Q E : Type*} [TopologicalSpace Q] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set Q} (hK : IsCompact K) (A : Q → E →L[ℝ] E)
    (hcont : ContinuousOn A K)
    (hpos : ∀ p ∈ K, ∀ v : E, v ≠ 0 → 0 < ⟪A p v, v⟫_ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ v : E, δ * ‖v‖ ^ 2 ≤ ⟪A p v, v⟫_ℝ := by
  let QF : Q × E → ℝ := fun z ↦ ⟪A z.1 z.2, z.2⟫_ℝ
  let L := K ×ˢ sphere (0 : E) 1
  have hLc : IsCompact L := hK.prod (isCompact_sphere _ _)
  have hQc : ContinuousOn QF L := by
    have hc := hcont.comp continuous_fst.continuousOn
      (show MapsTo Prod.fst L K from fun _ hz ↦ hz.1)
    exact (hc.clm_apply continuous_snd.continuousOn).inner continuous_snd.continuousOn
  have hp : ∀ z ∈ L, 0 < QF z := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    apply hpos p hp v
    intro hv0
    have hw : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
    rw [hv0, norm_zero] at hw
    norm_num at hw
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ L, δ ≤ QF z := by
    by_cases hn : L.Nonempty
    · obtain ⟨z, hz, hzmin⟩ := hLc.exists_isMinOn hn hQc
      exact ⟨QF z, hp z hz, fun _ hy ↦ hzmin hy⟩
    · exact ⟨1, by norm_num, fun z hz ↦ (hn ⟨z, hz⟩).elim⟩
  obtain ⟨δ, hδ, hbound⟩ := hδ
  refine ⟨δ, hδ, ?_⟩
  intro p hp v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb := hbound (p, (‖v‖⁻¹ : ℝ) • v)
    ⟨hp, by simpa [mem_sphere, dist_zero_right] using hw⟩
  have he : QF (p, (‖v‖⁻¹ : ℝ) • v) =
      ‖v‖⁻¹ * ‖v‖⁻¹ * ⟪A p v, v⟫_ℝ := by
    dsimp only [QF]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)
  have hc : ‖v‖ ^ 2 * (‖v‖⁻¹ * ‖v‖⁻¹ * ⟪A p v, v⟫_ℝ) =
      ⟪A p v, v⟫_ℝ := by field_simp
  rw [hc] at hh
  nlinarith

/-- The same actual data give actual inverse equivalences with a common inverse
operator-norm bound.

Proof: use the actual positive lower bound just proved. Native coercivity gives
actual IsUnit and an actual anti-Lipschitz estimate. The native equivalence from
the actual unit supplies its inverse; evaluate the anti-Lipschitz estimate on
that inverse and0 to bound its actual operator norm. Source: `prop:matrix`, line307. -/
theorem compact_positive_operator_inverse_bound
    {Q E : Type*} [TopologicalSpace Q] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set Q} (hK : IsCompact K) (A : Q → E →L[ℝ] E)
    (hcont : ContinuousOn A K)
    (hpos : ∀ p ∈ K, ∀ v : E, v ≠ 0 → 0 < ⟪A p v, v⟫_ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ p ∈ K, ∀ v : E, δ * ‖v‖ ^ 2 ≤ ⟪A p v, v⟫_ℝ) ∧
      ∀ p ∈ K, ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = A p ∧
        ‖e.symm.toContinuousLinearMap‖ ≤ δ⁻¹ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨δ, hδ, hbound⟩ := compact_positive_operator_lower_bound hK A hcont hpos
  refine ⟨δ, hδ, hbound, ?_⟩
  intro p hp
  let c : ℝ≥0 := ⟨δ, hδ.le⟩
  have hc : 0 < c := hδ
  have hcoercive (v : E) : ‖v‖ ^ 2 * c ≤ ‖⟪A p v, v⟫_ℝ‖ := by
    have hlo : ‖v‖ ^ 2 * (c : ℝ) ≤ ⟪A p v, v⟫_ℝ := by
      change ‖v‖ ^ 2 * δ ≤ _
      simpa only [mul_comm] using hbound p hp v
    exact hlo.trans (by simpa only [Real.norm_eq_abs] using le_abs_self ⟪A p v, v⟫_ℝ)
  have hanti := ContinuousLinearMap.antilipschitz_of_forall_le_inner_map (A p) hc hcoercive
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (A p) hc hcoercive
  let e := ContinuousLinearEquiv.unitsEquiv ℝ E u
  have he : e.toContinuousLinearMap = A p := by
    ext v
    change (u : E →L[ℝ] E) v = A p v
    rw [hu]
  refine ⟨e, he, e.symm.toContinuousLinearMap.opNorm_le_bound (inv_nonneg.mpr hδ.le) ?_⟩
  intro v
  change ‖e.symm v‖ ≤ δ⁻¹ * ‖v‖
  have h := hanti.le_mul_dist (e.symm v) 0
  have hi : A p (e.symm v) = v := by rw [← he]; exact e.apply_symm_apply v
  have hcδ : (c : ℝ) = δ := rfl
  simpa only [map_zero, dist_zero_right, NNReal.coe_inv, hcδ, hi] using h

#print axioms compact_positive_operator_lower_bound
#print axioms compact_positive_operator_inverse_bound

end GlobalEmbedding.Paper
