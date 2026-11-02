import GlobalEmbedding.Paper.IncrementsWeightedIterate
import Mathlib.Analysis.Complex.Basic

/-!
# Support and real homogeneity of the actual finite mode formula

Source: `main.tex`, lem:increments617–650. The expression below is exactly the actual
first-order function expression in `IncrementsWeightedIterate`. Its finite scaled
function iterates give the original polynomial shape, without postulating a linear
operator on arbitrary raw functions or creating a module of smooth sections.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The SAME actual first-order expression used by the accepted weighted iterate.
This is a function expression, not a claimed linear endomorphism of raw functions. -/
def incrementsActualFirstOrder (A : D → (D →L[ℝ] E) →L[ℝ] E)
    (B : D → E →L[ℝ] E) (u : D → E) (x : D) : E :=
  B x (u x) + A x (fderiv ℝ u x)

/-- Actual locality never enlarges topological support. This uses the native zero
derivative outside support and is valid even without global smoothness. It does NOT
claim that derivatives preserve the pointwise nonzero set. -/
theorem increments_actual_first_order_tsupport (A : D → (D →L[ℝ] E) →L[ℝ] E)
    (B : D → E →L[ℝ] E) (u : D → E) :
    tsupport (incrementsActualFirstOrder A B u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hu
  apply hx
  simp only [incrementsActualFirstOrder, image_eq_zero_of_notMem_tsupport hu,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hu, map_zero, add_zero]

/-- Local smoothness of the literal expression follows from native smoothness of
the derivative field and CLM application on the ORIGINAL open domain. -/
theorem increments_actual_first_order_contDiffOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E) (u : D → E)
    (O : Set D) (hO : IsOpen O) (hA : ContDiffOn ℝ ∞ A O)
    (hB : ContDiffOn ℝ ∞ B O) (hu : ContDiffOn ℝ ∞ u O) :
    ContDiffOn ℝ ∞ (incrementsActualFirstOrder A B u) O := by
  exact (hB.clm_apply hu).add (hA.clm_apply (hu.fderiv_of_isOpen hO (by simp)))

/-- Real scalar homogeneity at an ACTUAL differentiability point. No derivative
linearity on arbitrary nonsmooth functions is asserted. -/
theorem increments_actual_first_order_real_smul
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E) (u : D → E)
    (δ : ℝ) (x : D) (hu : DifferentiableAt ℝ u x) :
    incrementsActualFirstOrder A B (fun y ↦ δ • u y) x =
      δ • incrementsActualFirstOrder A B u x := by
  rw [incrementsActualFirstOrder, fderiv_fun_const_smul hu δ]
  simp only [map_smul, incrementsActualFirstOrder, smul_add]

section ComplexScale

variable [NormedSpace ℂ E]

/-- The literal scaled step -alpha L, acting on actual functions. The original
caller sets alpha=tau/i. No complex-linearity of L is assumed here. -/
def incrementsActualModeStep (A : D → (D →L[ℝ] E) →L[ℝ] E)
    (B : D → E →L[ℝ] E) (α : ℂ) (u : D → E) (x : D) : E :=
  (-α) • incrementsActualFirstOrder A B u x

/-- The ORIGINAL finite shape alpha SUM_(m<p) (-alpha L)^m k, using actual function
iterates. Scalars have not been commuted through L. The canonical abstract finite
residual theorem is separate from realizing its actual geometric mode equation. -/
def incrementsActualModeSum (A : D → (D →L[ℝ] E) →L[ℝ] E)
    (B : D → E →L[ℝ] E) (α : ℂ) (p : ℕ) (k : D → E) (x : D) : E :=
  α • ∑ m ∈ Finset.range p, ((incrementsActualModeStep A B α)^[m] k) x

/-- Native scalar support and actual first-order locality control the scaled step. -/
theorem increments_actual_mode_step_tsupport
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E) (α : ℂ) (u : D → E) :
    tsupport (incrementsActualModeStep A B α u) ⊆ tsupport u := by
  exact (tsupport_smul_subset_right (fun _ ↦ -α) _).trans
    (increments_actual_first_order_tsupport A B u)

/-- Each actual scaled function iterate preserves the original source support. -/
theorem increments_actual_mode_iterate_tsupport
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) :
    tsupport ((incrementsActualModeStep A B α)^[p] k) ⊆ tsupport k := by
  induction p with
  | zero => exact Set.Subset.rfl
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    exact (increments_actual_mode_step_tsupport A B α _).trans ih

/-- The SAME finite reconstruction preserves actual source support. No compact
support, nonempty space, positive iteration length or nonzero alpha is needed. -/
theorem increments_actual_mode_sum_tsupport
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) :
    tsupport (incrementsActualModeSum A B α p k) ⊆ tsupport k := by
  apply closure_minimal _ (isClosed_tsupport k)
  intro x hx
  by_contra hk
  have hz (m : ℕ) : ((incrementsActualModeStep A B α)^[m] k) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦
      hk (increments_actual_mode_iterate_tsupport A B α m k h)
  apply hx
  simp only [incrementsActualModeSum, hz, Finset.sum_const_zero, smul_zero]

/-- Pairwise intersections are preserved even when the two original modes use
different coefficient fields, scales and finite lengths. -/
theorem increments_actual_mode_sum_support_inter
    (A₁ A₂ : D → (D →L[ℝ] E) →L[ℝ] E) (B₁ B₂ : D → E →L[ℝ] E)
    (α β : ℂ) (p q : ℕ) (k h : D → E) :
    tsupport (incrementsActualModeSum A₁ B₁ α p k) ∩
        tsupport (incrementsActualModeSum A₂ B₂ β q h) ⊆ tsupport k ∩ tsupport h :=
  Set.inter_subset_inter (increments_actual_mode_sum_tsupport A₁ B₁ α p k)
    (increments_actual_mode_sum_tsupport A₂ B₂ β q h)

variable [IsScalarTower ℝ ℂ E]

/-- Every actual scaled iterate is smooth on the SAME original open domain. -/
theorem increments_actual_mode_iterate_contDiffOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) :
    ContDiffOn ℝ ∞ ((incrementsActualModeStep A B α)^[p] k) O := by
  induction p with
  | zero => exact hk
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    exact (increments_actual_first_order_contDiffOn A B _ O hO hA hB ih).const_smul (-α)

/-- Actual finite-sum smoothness, with no global smooth extension or compactness. -/
theorem increments_actual_mode_sum_contDiffOn
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) :
    ContDiffOn ℝ ∞ (incrementsActualModeSum A B α p k) O := by
  apply ContDiffOn.const_smul α
  exact ContDiffOn.sum fun m _ ↦
    increments_actual_mode_iterate_contDiffOn A B α m k O hO hA hB hk

/-- Real delta homogeneity for ACTUAL scaled iterates on the original smooth open
domain. Equality on this domain is converted to equality of germs before comparing
derivatives. No linearity of totalized differentiation on arbitrary functions is used. -/
theorem increments_actual_mode_iterate_real_smul
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) (δ : ℝ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) :
    Set.EqOn ((incrementsActualModeStep A B α)^[p] (fun y ↦ δ • k y))
      (fun y ↦ δ • ((incrementsActualModeStep A B α)^[p] k) y) O := by
  induction p with
  | zero => intro x hx; rfl
  | succ p ih =>
    intro x hx
    have he : ((incrementsActualModeStep A B α)^[p] (fun y ↦ δ • k y)) =ᶠ[𝓝 x]
        (fun y ↦ δ • ((incrementsActualModeStep A B α)^[p] k) y) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact ih hy
    have hd : DifferentiableAt ℝ ((incrementsActualModeStep A B α)^[p] k) x :=
      ((increments_actual_mode_iterate_contDiffOn A B α p k O hO hA hB hk x hx).contDiffAt
        (hO.mem_nhds hx)).differentiableAt (by simp)
    have hL : incrementsActualFirstOrder A B
        ((incrementsActualModeStep A B α)^[p] (fun y ↦ δ • k y)) x =
        incrementsActualFirstOrder A B
          (fun y ↦ δ • ((incrementsActualModeStep A B α)^[p] k) y) x := by
      rw [incrementsActualFirstOrder, incrementsActualFirstOrder,
        he.self_of_nhds, he.fderiv_eq (𝕜 := ℝ)]
    simp only [Function.iterate_succ_apply', incrementsActualModeStep]
    rw [hL, increments_actual_first_order_real_smul A B _ δ x hd, smul_comm]

/-- The SAME literal finite formula satisfies U_p(delta*k)=delta*U_p(k) for real
delta on the original smooth open domain, including delta=0. This is an actual
identity, not an assumed normalized error estimate or abstract L-linearity premise. -/
theorem increments_actual_mode_sum_real_smul
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) (δ : ℝ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) :
    Set.EqOn (incrementsActualModeSum A B α p (fun y ↦ δ • k y))
      (fun y ↦ δ • incrementsActualModeSum A B α p k y) O := by
  intro x hx
  unfold incrementsActualModeSum
  simp_rw [increments_actual_mode_iterate_real_smul A B α _ k δ O hO hA hB hk hx]
  rw [← Finset.smul_sum, smul_comm]

/-- Actual first derivatives of the SAME finite formula inherit its real delta
homogeneity by native germ locality at smooth points. This directly supports later
normalization of actual reconstruction derivative errors, without proving any bound. -/
theorem increments_actual_mode_sum_fderiv_real_smul
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k : D → E) (δ : ℝ) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) (x : D) (hx : x ∈ O) :
    fderiv ℝ (incrementsActualModeSum A B α p (fun y ↦ δ • k y)) x =
      δ • fderiv ℝ (incrementsActualModeSum A B α p k) x := by
  have he : incrementsActualModeSum A B α p (fun y ↦ δ • k y) =ᶠ[𝓝 x]
      (fun y ↦ δ • incrementsActualModeSum A B α p k y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact increments_actual_mode_sum_real_smul A B α p k δ O hO hA hB hk hy
  have hd : DifferentiableAt ℝ (incrementsActualModeSum A B α p k) x :=
    ((increments_actual_mode_sum_contDiffOn A B α p k O hO hA hB hk x hx).contDiffAt
      (hO.mem_nhds hx)).differentiableAt (by simp)
  rw [he.fderiv_eq, fderiv_fun_const_smul hd δ]

end ComplexScale
end GlobalEmbedding.Paper
