import GlobalEmbedding.Paper.IncrementsActualFiniteResidual
import GlobalEmbedding.Paper.IncrementsModeComplexLinearity
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Slow jet size of the same actual finite mode formula

Source: `main.tex`, lem:increments638–650. The finite length p is chosen before
observing j. Native finite-sum calculus and the accepted actual iterate bound are
reused. Coefficient/source jet bounds are genuine internal original geometry outputs.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The SAME actual finite formula has an unrestricted finite-sum size bound.
The canonical residual/iterate identity reuses the accepted weighted iterate without
another coefficient-scaling or weighted-induction proof. Coefficient commutation is
an actual geometric output, not an assumed differential operator on raw functions. -/
theorem increments_actual_mode_sum_scaled_jet
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ Mb)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ Mb)
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
    have hi := increments_actual_mode_residual_scaled_jet N m O S hO hSO A B α hα k
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

/-- For a fixed finite derivative budget N, a ratio at most one half gives the
size bound 2*norm(alpha)*Kb for SAME U_p. This is NOT asserted to be the original
j-independent finite-input validity threshold: the unrestricted finite-sum bound
above retains higher-jet constants without changing the finite formula. -/
theorem increments_actual_mode_sum_scaled_jet_half
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ Mb)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ Mb)
    (hkb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ Kb)
    (hr : (2 * 2 ^ N * Mb) * ‖α‖ / ell ≤ 1 / 2)
    (j : ℕ) (hjp : j + p ≤ N) (x : D) (hx : x ∈ S) :
    ell ^ j * ‖iteratedFDeriv ℝ j (incrementsActualModeSum A B α p k) x‖ ≤
      2 * ‖α‖ * Kb := by
  let r := (2 * 2 ^ N * Mb) * ‖α‖ / ell
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := lt_of_le_of_lt hr (by norm_num)
  have hgeom : ∑ m ∈ Finset.range p, r ^ m ≤ 2 := by
    calc
      _ ≤ 1 / (1 - r) := by
        simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := p) hr0 hr1)
      _ ≤ 2 := (div_le_iff₀ (sub_pos.mpr hr1)).2 (by dsimp [r] at *; linarith)
  calc
    _ ≤ ‖α‖ * Kb * ∑ m ∈ Finset.range p, r ^ m :=
      increments_actual_mode_sum_scaled_jet N p O S hO hSO A B α hα k
        hA hB hk hAc hBc ell Mb Kb hell hell1 hM hK hAb hBb hkb j hjp x hx
    _ ≤ ‖α‖ * Kb * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- The SAME actual polynomial preserves source differences on the original smooth
open domain. Native fderiv_sub is used only at genuine differentiability points of
the actual iterates; no linearity of totalized derivatives is asserted. -/
theorem increments_actual_mode_sum_sub
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (p : ℕ) (k h : D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) (hh : ContDiffOn ℝ ∞ h O) :
    Set.EqOn (incrementsActualModeSum A B α p (fun y ↦ k y - h y))
      (fun y ↦ incrementsActualModeSum A B α p k y -
        incrementsActualModeSum A B α p h y) O := by
  have hit (q : ℕ) :
      Set.EqOn ((incrementsActualModeStep A B α)^[q] (fun y ↦ k y - h y))
        (fun y ↦ ((incrementsActualModeStep A B α)^[q] k) y -
          ((incrementsActualModeStep A B α)^[q] h) y) O := by
    induction q with
    | zero => intro x hx; rfl
    | succ q ih =>
      intro x hx
      have he : (incrementsActualModeStep A B α)^[q] (fun y ↦ k y - h y) =ᶠ[𝓝 x]
          (fun y ↦ ((incrementsActualModeStep A B α)^[q] k) y -
            ((incrementsActualModeStep A B α)^[q] h) y) := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact ih hy
      have hdk : DifferentiableAt ℝ ((incrementsActualModeStep A B α)^[q] k) x :=
        ((increments_actual_mode_iterate_contDiffOn A B α q k O hO hA hB hk x hx).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)
      have hdh : DifferentiableAt ℝ ((incrementsActualModeStep A B α)^[q] h) x :=
        ((increments_actual_mode_iterate_contDiffOn A B α q h O hO hA hB hh x hx).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)
      simp only [Function.iterate_succ_apply', incrementsActualModeStep]
      rw [← smul_sub]
      congr 1
      unfold incrementsActualFirstOrder
      rw [he.self_of_nhds, he.fderiv_eq, fderiv_fun_sub hdk hdh]
      simp only [map_sub]
      abel
  intro x hx
  unfold incrementsActualModeSum
  simp_rw [hit _ hx]
  rw [Finset.sum_sub_distrib, smul_sub]

/-- True source-difference size for SAME A/B and SAME finite formula, from actual
smooth polynomial subtraction. Only source-difference jets are bounded; individual
source size bounds are unnecessary. Different coefficient fields are not compared. -/
theorem increments_actual_mode_sum_sub_scaled_jet_half
    (N p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (α : ℂ) (hα : α ≠ 0) (k h : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) (hh : ContDiffOn ℝ ∞ h O)
    (hAc : ∀ x ∈ O, ∀ jet, A x (α • jet) = α • A x jet)
    (hBc : ∀ x ∈ O, ∀ z, B x (α • z) = α • B x z)
    (ell Mb Kd : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kd)
    (hAb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ Mb)
    (hBb : ∀ i ≤ N, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ Mb)
    (hkb : ∀ i ≤ N, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k y - h y) x‖ ≤ Kd)
    (hr : (2 * 2 ^ N * Mb) * ‖α‖ / ell ≤ 1 / 2)
    (j : ℕ) (hjp : j + p ≤ N) (x : D) (hx : x ∈ S) :
    ell ^ j * ‖iteratedFDeriv ℝ j
        (fun y ↦ incrementsActualModeSum A B α p k y -
          incrementsActualModeSum A B α p h y) x‖ ≤ 2 * ‖α‖ * Kd := by
  have he : (fun y ↦ incrementsActualModeSum A B α p k y -
        incrementsActualModeSum A B α p h y) =ᶠ[𝓝 x]
      incrementsActualModeSum A B α p (fun y ↦ k y - h y) := by
    filter_upwards [hO.mem_nhds (hSO hx)] with y hy
    exact (increments_actual_mode_sum_sub A B α p k h O hO hA hB hk hh hy).symm
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  exact increments_actual_mode_sum_scaled_jet_half N p O S hO hSO A B α hα
    (fun y ↦ k y - h y) hA hB (hk.sub hh) hAc hBc ell Mb Kd hell hell1 hM hK
    hAb hBb hkb hr j hjp x hx

end GlobalEmbedding.Paper

namespace GlobalEmbedding.Paper

open Manifold

section OriginalMode

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Unrestricted finite-sum size for SAME original geometric coefficients and
alpha=tau/i. W2 coefficient commutation is discharged, with original geometry/source
smoothness and weighted jets still honest internal caller outputs. -/
theorem incrementsModeActualSum_scaled_jet_tau
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (n p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (τ : ℝ) (hτ : 0 < τ) (k : D → Cdata)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ContDiffOn ℝ ∞ k O)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ Kb)
    (j : ℕ) (hjp : j + p ≤ n) (x : D) (hx : x ∈ S) :
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    ell ^ j * ‖iteratedFDeriv ℝ j
        (incrementsActualModeSum A B ((τ : ℂ) / Complex.I) p k) x‖ ≤
      τ * Kb * ∑ a ∈ Finset.range p, ((2 * 2 ^ n * Mb) * τ / ell) ^ a := by
  let α := (τ : ℂ) / Complex.I
  have hn : ‖α‖ = τ := by dsimp [α]; simp [abs_of_pos hτ]
  have hα : α ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hτ)
  simpa only [hn] using increments_actual_mode_sum_scaled_jet n p O S hO hSO
    (incrementsModeComplexFirstOrderA F hF c) (incrementsModeComplexFirstOrderB F hF c)
    α hα k hA hB hk
    (fun y _ jet ↦ incrementsModeComplexFirstOrderA_smul F hF c y α jet)
    (fun y _ z ↦ incrementsModeComplexFirstOrderB_smul F hF c y α z)
    ell Mb Kb hell hell1 hM hK hAb hBb hkb j hjp x hx

/-- Actual original finite reconstruction size at a fixed derivative budget and
ratio at most one half. SAME p is retained before choosing j; this does not claim
an all-orders validity threshold from the high-order coefficient constant. -/
theorem incrementsModeActualSum_scaled_jet_tau_half
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (n p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (τ : ℝ) (hτ : 0 < τ) (k : D → Cdata)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ContDiffOn ℝ ∞ k O)
    (ell Mb Kb : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kb)
    (hAb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i k x‖ ≤ Kb)
    (hr : (2 * 2 ^ n * Mb) * τ / ell ≤ 1 / 2)
    (j : ℕ) (hjp : j + p ≤ n) (x : D) (hx : x ∈ S) :
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    ell ^ j * ‖iteratedFDeriv ℝ j
        (incrementsActualModeSum A B ((τ : ℂ) / Complex.I) p k) x‖ ≤ 2 * τ * Kb := by
  let α := (τ : ℂ) / Complex.I
  have hn : ‖α‖ = τ := by dsimp [α]; simp [abs_of_pos hτ]
  have hα : α ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hτ)
  have hr' : (2 * 2 ^ n * Mb) * ‖α‖ / ell ≤ 1 / 2 := by simpa only [hn] using hr
  simpa only [hn] using increments_actual_mode_sum_scaled_jet_half n p O S hO hSO
    (incrementsModeComplexFirstOrderA F hF c) (incrementsModeComplexFirstOrderB F hF c)
    α hα k hA hB hk
    (fun y _ jet ↦ incrementsModeComplexFirstOrderA_smul F hF c y α jet)
    (fun y _ z ↦ incrementsModeComplexFirstOrderB_smul F hF c y α z)
    ell Mb Kb hell hell1 hM hK hAb hBb hkb hr' j hjp x hx

/-- True difference size for original SAME geometric coefficients. Actual source
difference jets, rather than desired reconstruction differences, are the input.
This compares the SAME polynomial at two sources with fixed original F and c. -/
theorem incrementsModeActualSum_sub_scaled_jet_tau_half
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (n p : ℕ) (O S : Set D) (hO : IsOpen O) (hSO : S ⊆ O)
    (τ : ℝ) (hτ : 0 < τ) (k h : D → Cdata)
    (hA : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderA F hF c) O)
    (hB : ContDiffOn ℝ ∞ (incrementsModeComplexFirstOrderB F hF c) O)
    (hk : ContDiffOn ℝ ∞ k O) (hh : ContDiffOn ℝ ∞ h O)
    (ell Mb Kd : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hM : 0 ≤ Mb) (hK : 0 ≤ Kd)
    (hAb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderA F hF c) x‖ ≤ Mb)
    (hBb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (incrementsModeComplexFirstOrderB F hF c) x‖ ≤ Mb)
    (hkb : ∀ i ≤ n, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ k y - h y) x‖ ≤ Kd)
    (hr : (2 * 2 ^ n * Mb) * τ / ell ≤ 1 / 2)
    (j : ℕ) (hjp : j + p ≤ n) (x : D) (hx : x ∈ S) :
    let A := incrementsModeComplexFirstOrderA F hF c
    let B := incrementsModeComplexFirstOrderB F hF c
    let U := incrementsActualModeSum A B ((τ : ℂ) / Complex.I) p
    ell ^ j * ‖iteratedFDeriv ℝ j (fun y ↦ U k y - U h y) x‖ ≤ 2 * τ * Kd := by
  let α := (τ : ℂ) / Complex.I
  have hn : ‖α‖ = τ := by dsimp [α]; simp [abs_of_pos hτ]
  have hα : α ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hτ)
  have hr' : (2 * 2 ^ n * Mb) * ‖α‖ / ell ≤ 1 / 2 := by simpa only [hn] using hr
  simpa only [hn] using increments_actual_mode_sum_sub_scaled_jet_half n p O S hO hSO
    (incrementsModeComplexFirstOrderA F hF c) (incrementsModeComplexFirstOrderB F hF c)
    α hα k h hA hB hk hh
    (fun y _ jet ↦ incrementsModeComplexFirstOrderA_smul F hF c y α jet)
    (fun y _ z ↦ incrementsModeComplexFirstOrderB_smul F hF c y α z)
    ell Mb Kd hell hell1 hM hK hAb hBb hkb hr' j hjp x hx

end OriginalMode
end GlobalEmbedding.Paper
