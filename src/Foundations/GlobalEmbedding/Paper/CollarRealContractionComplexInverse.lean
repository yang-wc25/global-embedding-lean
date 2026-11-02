import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Complex inversion from contraction on a real form

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This supplies the complex inverse needed by the analytic implicit-function
route to dependence of the collar fixed point. No comparison of the real and complex operator
norms by the constant one is assumed.
-/

namespace GlobalEmbedding.Paper

/-- A complex-linear map which preserves a real form and contracts on that form has a convergent
complex operator-norm Neumann series. The continuous real and imaginary coordinate projections
account for the constant in the bound on its powers.

Source: Proposition `prop:collar`, proof lines 530–534, analytic contraction step.
For a vector in the real form, induction gives the bound `q^n * ‖x‖` for its nth iterate.
Decompose a general vector as `r(x) + I • s(x)`. Complex linearity and the triangle inequality
bound its nth iterate by `q^n * (‖r(x)‖ + ‖s(x)‖)`, hence by
`(‖r‖ + ‖s‖ + 1) * q^n * ‖x‖`. The resulting geometric majorant is summable because
`0 ≤ q < 1`. The two geometric-series multiplication identities give both composition
identities for the sum and `I-T`; these construct the continuous complex inverse and identify
it with that sum. A closed real form with unique continuous coordinates supplies the data
used here; the proof only needs the displayed decomposition, so does not require uniqueness
or closedness as additional hypotheses.
-/
theorem collar_real_contraction_complex_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (R : Submodule ℝ E) (r s : E →L[ℝ] R)
    (hdecomp : ∀ x : E, (r x : E) + Complex.I • (s x : E) = x)
    (T : E →L[ℂ] E) (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hpres : ∀ x : E, x ∈ R → T x ∈ R)
    (hcontract : ∀ x : E, x ∈ R → ‖T x‖ ≤ q * ‖x‖) :
    ∃ K : ℝ, 0 < K ∧ (∀ n : ℕ, ‖T ^ n‖ ≤ K * q ^ n) ∧
      Summable (fun n : ℕ ↦ T ^ n) ∧
      (ContinuousLinearMap.id ℂ E - T).IsInvertible ∧
      HasSum (fun n : ℕ ↦ T ^ n) (ContinuousLinearMap.id ℂ E - T).inverse := by
  have hreal (n : ℕ) (x : E) (hx : x ∈ R) :
      (T ^ n) x ∈ R ∧ ‖(T ^ n) x‖ ≤ q ^ n * ‖x‖ := by
    induction n with
    | zero => simpa using And.intro hx (le_refl ‖x‖)
    | succ n ih =>
      rw [pow_succ']
      change T ((T ^ n) x) ∈ R ∧ ‖T ((T ^ n) x)‖ ≤ q ^ (n + 1) * ‖x‖
      refine ⟨hpres _ ih.1, (hcontract _ ih.1).trans ?_⟩
      calc
        q * ‖(T ^ n) x‖ ≤ q * (q ^ n * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih.2 hq₀
        _ = q ^ (n + 1) * ‖x‖ := by rw [pow_succ]; ring
  let K : ℝ := ‖r‖ + ‖s‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound (n : ℕ) : ‖T ^ n‖ ≤ K * q ^ n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK.le (pow_nonneg hq₀ n))
    intro x
    calc
      ‖(T ^ n) x‖ = ‖(T ^ n) ((r x : E) + Complex.I • (s x : E))‖ := by
        rw [hdecomp x]
      _ ≤ ‖(T ^ n) (r x : E)‖ + ‖(T ^ n) (s x : E)‖ := by
        rw [map_add, map_smul]
        simpa only [norm_smul, Complex.norm_I, one_mul] using
          norm_add_le ((T ^ n) (r x : E)) (Complex.I • (T ^ n) (s x : E))
      _ ≤ q ^ n * ‖r x‖ + q ^ n * ‖s x‖ :=
        add_le_add (hreal n (r x) (r x).property).2 (hreal n (s x) (s x).property).2
      _ ≤ q ^ n * (‖r‖ * ‖x‖) + q ^ n * (‖s‖ * ‖x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (r.le_opNorm x) (pow_nonneg hq₀ n))
          (mul_le_mul_of_nonneg_left (s.le_opNorm x) (pow_nonneg hq₀ n))
      _ = (‖r‖ + ‖s‖) * q ^ n * ‖x‖ := by ring
      _ ≤ K * q ^ n * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq₀ n)
        dsimp [K]
        linarith
  have hsum : Summable (fun n : ℕ ↦ T ^ n) :=
    ((summable_geometric_of_lt_one hq₀ hq₁).mul_left K).of_norm_bounded hbound
  have hleft : (ContinuousLinearMap.id ℂ E - T).comp (∑' n : ℕ, T ^ n) =
      ContinuousLinearMap.id ℂ E := hsum.one_sub_mul_tsum_pow
  have hright : (∑' n : ℕ, T ^ n).comp (ContinuousLinearMap.id ℂ E - T) =
      ContinuousLinearMap.id ℂ E := hsum.tsum_pow_mul_one_sub
  refine ⟨K, hK, hbound, hsum, .of_inverse hleft hright, ?_⟩
  rw [ContinuousLinearMap.inverse_eq hleft hright]
  exact hsum.hasSum

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_real_contraction_complex_inverse
