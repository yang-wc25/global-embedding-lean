import GlobalEmbedding.Paper.IncrementsActualReconstructionSupport

/-!
# Residual of the same actual finite mode formula

Source: `main.tex`, lem:increments630–650. All iterates are the accepted actual
function iterates. Coefficient scalar commutation is an internal geometric output,
not an assumed complex-linear differential operator on arbitrary raw functions.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The literal residual of the SAME finite reconstruction. -/
def incrementsActualModeResidual (A : D → (D →L[ℝ] E) →L[ℝ] E)
    (B : D → E →L[ℝ] E) (α : ℂ) (p : ℕ) (k : D → E) (x : D) : E :=
  α⁻¹ • incrementsActualModeSum A B α p k x +
    incrementsActualFirstOrder A B (incrementsActualModeSum A B α p k) x - k x

/-- Native finite-sum differentiation and genuine coefficient commutation realize
the residual as minus the next actual iterate. The iteration length is fixed before
any derivative observation, and the identity also holds for p=0. -/
theorem increments_actual_mode_residual_eq
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (p : ℕ) (k : D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (x : D) (hx : x ∈ O) :
    incrementsActualModeResidual A B α p k x =
      -((incrementsActualModeStep A B α)^[p] k) x := by
  let v (m : ℕ) := (incrementsActualModeStep A B α)^[m] k
  have hd (m : ℕ) : DifferentiableAt ℝ (v m) x :=
    ((increments_actual_mode_iterate_contDiffOn A B α m k O hO hA hB hk x hx).contDiffAt
      (hO.mem_nhds hx)).differentiableAt (by simp)
  have hds : DifferentiableAt ℝ (fun y ↦ ∑ m ∈ Finset.range p, v m y) x :=
    DifferentiableAt.fun_sum fun m _ ↦ hd m
  have hLU : incrementsActualFirstOrder A B (incrementsActualModeSum A B α p k) x =
      ∑ m ∈ Finset.range p, α • incrementsActualFirstOrder A B (v m) x := by
    unfold incrementsActualFirstOrder incrementsActualModeSum
    rw [fderiv_fun_const_smul hds α, fderiv_fun_sum (fun m _ ↦ hd m),
      hBc x hx, hAc x hx]
    simp only [map_sum, smul_add, Finset.smul_sum, ← Finset.sum_add_distrib]
    rfl
  have hstep (m : ℕ) : α • incrementsActualFirstOrder A B (v m) x = -v (m + 1) x := by
    simp only [v, Function.iterate_succ_apply', incrementsActualModeStep, neg_smul,
      neg_neg]
  have ht := Finset.sum_range_sub' (fun m ↦ v m x) p
  unfold incrementsActualModeResidual
  rw [hLU]
  simp_rw [hstep]
  rw [incrementsActualModeSum, inv_smul_smul₀ hα]
  change (∑ m ∈ Finset.range p, v m x) +
    (∑ m ∈ Finset.range p, -v (m + 1) x) - k x = -v p x
  rw [← Finset.sum_add_distrib]
  simp_rw [← sub_eq_add_neg]
  rw [ht]
  change (k x - v p x) - k x = -v p x
  abel

/-- The actual residual inherits the accepted weighted iterate bound on the SAME
original open domain. Coefficient/source jet bounds are genuine internal geometric
inputs. No bound on the desired residual, abstract L-linearity, or solver is assumed. -/
theorem increments_actual_mode_residual_scaled_jet
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hkb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ K)
    (j : ℕ) (hjp : j + p ≤ N) (x : D) (hx : x ∈ S) :
    ell ^ j * ‖iteratedFDeriv ℝ j (incrementsActualModeResidual A B α p k) x‖ ≤
      (2 * 2 ^ N * M) ^ p * (‖α‖ / ell) ^ p * K := by
  have : SMulCommClass ℝ ℂ E := IsScalarTower.to_smulCommClass
  let As := fun y ↦ (-α) • A y
  let Bs := fun y ↦ (-α) • B y
  have hAs : ContDiffOn ℝ ∞ As O := hA.const_smul (-α)
  have hBs : ContDiffOn ℝ ∞ Bs O := hB.const_smul (-α)
  have hAsb : ∀ i ≤ N, ∀ y ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i As y‖ ≤ ‖α‖ * M := by
    intro i hi y hy
    have hs : ContDiffAt ℝ i A y :=
      ((hA y (hSO hy)).contDiffAt (hO.mem_nhds (hSO hy))).of_le (by simp)
    dsimp only [As]
    rw [iteratedFDeriv_const_smul_apply' hs]
    have hn : ‖(-α) • iteratedFDeriv ℝ i A y‖ ≤
        ‖-α‖ * ‖iteratedFDeriv ℝ i A y‖ := by
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro z
      rw [smul_apply]
      calc
        _ ≤ ‖-α‖ * ‖iteratedFDeriv ℝ i A y z‖ :=
          ContinuousLinearMap.opNorm_smul_le (-α) _
        _ ≤ ‖-α‖ * (‖iteratedFDeriv ℝ i A y‖ * ∏ t, ‖z t‖) :=
          mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ i A y).le_opNorm z)
            (norm_nonneg (-α))
        _ = _ := by ring
    calc
      _ ≤ ell ^ i * (‖-α‖ * ‖iteratedFDeriv ℝ i A y‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ‖α‖ * (ell ^ i * ‖iteratedFDeriv ℝ i A y‖) := by rw [norm_neg]; ring
      _ ≤ ‖α‖ * M := mul_le_mul_of_nonneg_left (hAb i hi y hy) (norm_nonneg _)
  have hBsb : ∀ i ≤ N, ∀ y ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i Bs y‖ ≤ ‖α‖ * M := by
    intro i hi y hy
    have hs : ContDiffAt ℝ i B y :=
      ((hB y (hSO hy)).contDiffAt (hO.mem_nhds (hSO hy))).of_le (by simp)
    dsimp only [Bs]
    rw [iteratedFDeriv_const_smul_apply' hs]
    calc
      _ ≤ ell ^ i * (‖-α‖ * ‖iteratedFDeriv ℝ i B y‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_le _ _) (by positivity)
      _ = ‖α‖ * (ell ^ i * ‖iteratedFDeriv ℝ i B y‖) := by rw [norm_neg]; ring
      _ ≤ ‖α‖ * M := mul_le_mul_of_nonneg_left (hBb i hi y hy) (norm_nonneg _)
  have hstep : (fun u y ↦ Bs y (u y) + As y (fderiv ℝ u y)) =
      incrementsActualModeStep A B α := by
    funext u y
    simp only [As, Bs, smul_apply, incrementsActualModeStep,
      incrementsActualFirstOrder, smul_add]
  have hb := increments_first_order_scaled_iterate N p O S hO hSO As Bs k
    hAs hBs hk ell (‖α‖ * M) K hell hell1 (mul_nonneg (norm_nonneg _) hM) hK
    hAsb hBsb hkb j hjp x hx
  rw [hstep] at hb
  have he : incrementsActualModeResidual A B α p k =ᶠ[𝓝 x]
      (fun y ↦ -((incrementsActualModeStep A B α)^[p] k) y) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact increments_actual_mode_residual_eq A B α hα p k O hO hA hB hk hAc hBc y hy
  have hj := (he.iteratedFDeriv ℝ j).self_of_nhds
  rw [hj]
  change ell ^ j * ‖iteratedFDeriv ℝ j (-((incrementsActualModeStep A B α)^[p] k)) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  apply (mul_le_mul_iff_left₀ (pow_pos hell p)).mp
  calc
    _ = ell ^ (j + p) *
        ‖iteratedFDeriv ℝ j ((incrementsActualModeStep A B α)^[p] k) x‖ := by
      rw [pow_add]
      ring
    _ ≤ (2 * 2 ^ N * (‖α‖ * M)) ^ p * K := hb
    _ = ((2 * 2 ^ N * M) ^ p * (‖α‖ / ell) ^ p * K) * ell ^ p := by
      rw [div_pow]
      field_simp
      ring

/-- Original alpha=tau/i: native complex norms turn the same fixed-p residual bound
into the genuine slow/fast ratio (tau/ell)^p. No fast multiplier estimate is used. -/
theorem increments_actual_mode_residual_scaled_jet_tau
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (τ : ℝ) (hτ : 0 < τ) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet,
      A x (((τ : ℂ) / Complex.I) • jet) = ((τ : ℂ) / Complex.I) • A x jet)
    (hBc : ∀ x ∈ O, ∀ z,
      B x (((τ : ℂ) / Complex.I) • z) = ((τ : ℂ) / Complex.I) • B x z)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hkb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ K)
    (j : ℕ) (hjp : j + p ≤ N) (x : D) (hx : x ∈ S) :
    ell ^ j * ‖iteratedFDeriv ℝ j
        (incrementsActualModeResidual A B ((τ : ℂ) / Complex.I) p k) x‖ ≤
      (2 * 2 ^ N * M) ^ p * (τ / ell) ^ p * K := by
  have hn : ‖(τ : ℂ) / Complex.I‖ = τ := by
    simp [abs_of_pos hτ]
  have hα : (τ : ℂ) / Complex.I ≠ 0 := by
    exact norm_pos_iff.mp (by rw [hn]; exact hτ)
  simpa only [hn] using increments_actual_mode_residual_scaled_jet N p O S hO hSO A B
    ((τ : ℂ) / Complex.I) hα k hA hB hk hAc hBc ell M K hell hell1 hM hK
    hAb hBb hkb j hjp x hx

end GlobalEmbedding.Paper
