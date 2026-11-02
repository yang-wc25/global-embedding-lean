import GlobalEmbedding.Paper.IncrementsActualModeSize

/-! The genuine first-order operator with distinct coefficient scales.
The derivative coefficient A has ell^k jets, while the value coefficient B
has ell^(k+1) jets. This is the scale produced by slowly varying adapted
coordinates: Gamma and T0 may be O(ell^-1). The unchanged actual finite
polynomial still loses only one ell per step. No uniform O(1) value coefficient
is postulated and no new solver is introduced. -/

noncomputable section
open GlobalEmbedding.Paper Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

theorem actual_increment_first_order_split_scale_jets
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] F) (B : D → E →L[ℝ] F) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hf : ContDiffOn ℝ ∞ f O)
    (ell M K : ℝ) (hell : 0 < ell) (_hell1 : ell ≤ 1)
    (hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ j, ∀ x ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hfb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K) :
    ∀ k ≤ j, ∀ x ∈ S,
      ell ^ (k + 1) *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y) + A y (fderiv ℝ f y)) x‖ ≤
        2 * 2 ^ k * M * K := by
  intro k hk x hx
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) O := hf.fderiv_of_isOpen hO (by simp)
  have hBdiv : ∀ i ≤ k, ell^i * ‖iteratedFDeriv ℝ i B x‖ ≤ M/ell := by
    intro i hi
    apply (le_div_iff₀ hell).mpr
    calc
      _ = ell^(i+1)*‖iteratedFDeriv ℝ i B x‖ := by rw [pow_succ]; ring
      _ ≤ M := hBb i (hi.trans hk) x hx
  have h0 := scaled_clm_apply O hO B f hB hf k 0 ell (M/ell) K hell.le
    hBdiv (fun i hi => by simpa using hfb i (by omega) x hx) (hSO hx)
  have h1 := scaled_clm_apply O hO A (fderiv ℝ f) hA hdf k 1 ell M K hell.le
    (fun i hi ↦ hAb i (hi.trans hk) x hx)
    (fun i hi ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hfb (i + 1) (by omega) x hx)
    (hSO hx)
  have h0' : ell ^ (k + 1) * ‖iteratedFDeriv ℝ k (fun y ↦ B y (f y)) x‖ ≤
      2 ^ k * M * K := by
    calc
      _ = ell * (ell^k * ‖iteratedFDeriv ℝ k (fun y => B y (f y)) x‖) := by
        rw [pow_succ]; ring
      _ ≤ ell * (2^k * (M/ell) * K) := mul_le_mul_of_nonneg_left (by simpa using h0) hell.le
      _ = 2^k*M*K := by field_simp
  have hsum := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    (((hB.clm_apply hf).of_le (by simp)).contDiffWithinAt (hSO hx))
    (((hA.clm_apply hdf).of_le (by simp)).contDiffWithinAt (hSO hx))
    hO.uniqueDiffOn (hSO hx)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO (hSO hx)] at hsum
  rw [hsum]
  calc
    _ ≤ ell ^ (k + 1) *
        (‖iteratedFDeriv ℝ k (fun y ↦ B y (f y)) x‖ +
          ‖iteratedFDeriv ℝ k (fun y ↦ A y (fderiv ℝ f y)) x‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ 2 * 2 ^ k * M * K := by nlinarith [h0', h1]

theorem actual_increment_first_order_split_scale_iterate
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E) (f : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hf : ContDiffOn ℝ ∞ f O)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
    (hfb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ K) :
    let L : (D → E) → D → E := fun u x ↦ B x (u x) + A x (fderiv ℝ u x)
    ∀ k, k + p ≤ N → ∀ x ∈ S,
      ell ^ (k + p) * ‖iteratedFDeriv ℝ k (L^[p] f) x‖ ≤ (2 * 2 ^ N * M) ^ p * K := by
  let L : (D → E) → D → E := fun u x ↦ B x (u x) + A x (fderiv ℝ u x)
  let C := 2 * 2 ^ N * M
  change ∀ k, k + p ≤ N → ∀ x ∈ S,
    ell ^ (k + p) * ‖iteratedFDeriv ℝ k (L^[p] f) x‖ ≤ C ^ p * K
  have hLs : ∀ t, ContDiffOn ℝ ∞ (L^[t] f) O := by
    intro t
    induction t with
    | zero => simpa using hf
    | succ t ht =>
      rw [Function.iterate_succ_apply']
      exact (hB.clm_apply ht).add
        (hA.clm_apply (ht.fderiv_of_isOpen hO (by simp)))
  induction p with
  | zero =>
    intro k hk x hx
    simpa using hfb k (by simpa using hk) x hx
  | succ p ih =>
    intro k hk x hx
    have hsrc : ∀ i ≤ k + 1, ∀ y ∈ S,
        ell ^ i * ‖iteratedFDeriv ℝ i (L^[p] f) y‖ ≤ (C ^ p * K) / ell ^ p := by
      intro i hi y hy
      apply (le_div_iff₀ (pow_pos hell p)).2
      calc
        _ = ell ^ (i + p) * ‖iteratedFDeriv ℝ i (L^[p] f) y‖ := by
          rw [pow_add]
          ring
        _ ≤ C ^ p * K := ih i (by omega) y hy
    have hs := actual_increment_first_order_split_scale_jets k O S hO hSO A B (L^[p] f)
      hA hB (hLs p) ell M ((C ^ p * K) / ell ^ p) hell hell1
      (fun i hi y hy ↦ hAb i (by omega) y hy)
      (fun i hi y hy ↦ hBb i (by omega) y hy) hsrc
    have hbase : 2 * 2 ^ k * M ≤ C := by
      dsimp [C]
      gcongr <;> norm_num
      omega
    calc
      _ = ell ^ p * (ell ^ (k + 1) *
          ‖iteratedFDeriv ℝ k (fun y ↦ B y ((L^[p] f) y) +
            A y (fderiv ℝ (L^[p] f) y)) x‖) := by
        rw [Function.iterate_succ_apply']
        rw [show k + (p + 1) = p + (k + 1) by omega, pow_add]
        ring
      _ ≤ ell ^ p * (2 * 2 ^ k * M * ((C ^ p * K) / ell ^ p)) :=
        mul_le_mul_of_nonneg_left (hs k le_rfl x hx) (by positivity)
      _ = (2 * 2 ^ k * M) * (C ^ p * K) := by field_simp
      _ ≤ C * (C ^ p * K) := mul_le_mul_of_nonneg_right hbase (by dsimp [C]; positivity)
      _ = C ^ (p + 1) * K := by rw [pow_succ]; ring

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem actual_increment_mode_residual_split_scale_jets
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell M K : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
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
      ell ^ (i+1) * ‖iteratedFDeriv ℝ i Bs y‖ ≤ ‖α‖ * M := by
    intro i hi y hy
    have hs : ContDiffAt ℝ i B y :=
      ((hB y (hSO hy)).contDiffAt (hO.mem_nhds (hSO hy))).of_le (by simp)
    dsimp only [Bs]
    rw [iteratedFDeriv_const_smul_apply' hs]
    calc
      _ ≤ ell ^ (i+1) * (‖-α‖ * ‖iteratedFDeriv ℝ i B y‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_le _ _) (by positivity)
      _ = ‖α‖ * (ell ^ (i+1) * ‖iteratedFDeriv ℝ i B y‖) := by rw [norm_neg]; ring
      _ ≤ ‖α‖ * M := mul_le_mul_of_nonneg_left (hBb i hi y hy) (norm_nonneg _)
  have hstep : (fun u y ↦ Bs y (u y) + As y (fderiv ℝ u y)) =
      incrementsActualModeStep A B α := by
    funext u y
    simp only [As, Bs, smul_apply, incrementsActualModeStep,
      incrementsActualFirstOrder, smul_add]
  have hb := actual_increment_first_order_split_scale_iterate N p O S hO hSO As Bs k
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

theorem actual_increment_mode_sum_split_scale_jets
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ Mb)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ (i+1) * ‖iteratedFDeriv ℝ i B x‖ ≤ Mb)
    (hkb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ Kb)
    (j : ℕ) (hjp : j + p ≤ N) (x : D) (hx : x ∈ S) :
    ell ^ j * ‖iteratedFDeriv ℝ j (incrementsActualModeSum A B α p k) x‖ ≤
      ‖α‖ * Kb * ∑ m ∈ Finset.range p, ((2 * 2 ^ N * Mb) * ‖α‖ / ell) ^ m := by
  let v (m : ℕ) := (incrementsActualModeStep A B α)^[m] k
  have hs (m : ℕ) : ContDiffAt ℝ j (v m) x :=
    ((increments_actual_mode_iterate_contDiffOn A B α m k O hO hA hB hk x (hSO hx)).contDiffAt
      (hO.mem_nhds (hSO hx))).of_le (by simp)
  have hsum : ContDiffAt ℝ j (fun y ↦ ∑ m ∈ Finset.range p, v m y) x :=
    ContDiffAt.sum fun m _ ↦ hs m
  have hb (m : ℕ) (hm : m ∈ Finset.range p) :
      ell ^ j * ‖iteratedFDeriv ℝ j (v m) x‖ ≤
        (2 * 2 ^ N * Mb) ^ m * (‖α‖ / ell) ^ m * Kb := by
    have he : incrementsActualModeResidual A B α m k =ᶠ[𝓝 x] (fun y ↦ -v m y) := by
      filter_upwards [hO.mem_nhds (hSO hx)] with y hy
      exact increments_actual_mode_residual_eq A B α hα m k O hO hA hB hk hAc hBc y hy
    have hi := actual_increment_mode_residual_split_scale_jets N m O S hO hSO A B α hα k
      hA hB hk hAc hBc ell Mb Kb hell hell1 hM hK hAb hBb hkb j
      (by have := Finset.mem_range.mp hm; omega) x hx
    rw [(he.iteratedFDeriv ℝ j).self_of_nhds] at hi
    change ell ^ j * ‖iteratedFDeriv ℝ j (-v m) x‖ ≤ _ at hi
    simpa only [iteratedFDeriv_neg_apply, norm_neg] using hi
  unfold incrementsActualModeSum
  change ell ^ j * ‖iteratedFDeriv ℝ j
    (fun y ↦ α • ∑ m ∈ Finset.range p, v m y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hsum,
    iteratedFDeriv_fun_sum_apply (fun m _ ↦ hs m), norm_smul]
  calc
    _ ≤ ell ^ j * (‖α‖ * ∑ m ∈ Finset.range p, ‖iteratedFDeriv ℝ j (v m) x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)) (by positivity)
    _ = ‖α‖ * ∑ m ∈ Finset.range p,
        ell ^ j * ‖iteratedFDeriv ℝ j (v m) x‖ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ ‖α‖ * ∑ m ∈ Finset.range p,
        ((2 * 2 ^ N * Mb) ^ m * (‖α‖ / ell) ^ m * Kb) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← mul_pow, ← mul_div_assoc]
      ring


end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_first_order_split_scale_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_first_order_split_scale_iterate
#print axioms GlobalEmbedding.Continuation.actual_increment_mode_residual_split_scale_jets
#print axioms GlobalEmbedding.Continuation.actual_increment_mode_sum_split_scale_jets
