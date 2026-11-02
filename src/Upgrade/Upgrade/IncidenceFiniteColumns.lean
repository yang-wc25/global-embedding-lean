import Upgrade.IncidenceJointDerivative
import Upgrade.IncidencePairedColumns

/-!
# Fixed finite combinations of actual joint-incidence columns

The coefficient vectors are selected from the reference geometric principal
map. At a perturbed incidence they are applied to the same parameter responses
and the scaled actual source direction. Only the already differentiated map
is used, so fast-angle-dependent radial vectors do not acquire extra terms.
The final rank step reuses the accepted finite-column stability theorem.
-/

noncomputable section
open GlobalEmbedding.Offline
open scoped BigOperators

namespace GlobalEmbedding.Upgrade

variable {ι P X Y T R V W : Type*} [Fintype ι]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The accepted finite-column norm calculation, with arbitrary finite labels
so the original packet and its duplicated labels need not be relabelled. -/
theorem norm_incidence_finite_column_error_le (e : ι → W) {b : ℝ}
    (_hb : 0 ≤ b) (he : ∀ i, ‖e i‖ ≤ b) (c : ι → ℝ) :
    ‖∑ i, c i • e i‖ ≤ (Fintype.card ι : ℝ) * b * ‖c‖ := by
  calc
    ‖∑ i, c i • e i‖ ≤ ∑ i, ‖c i • e i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖c‖ * b := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm c i) (he i) (norm_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι : ℝ) * b * ‖c‖ := by simp; ring

/-- One literal vector in the full derivative domain. -/
def incidenceFiniteDirection (d : ι → P)
    (a : ℝ) (c : ι → ℝ) (e : X) : P × (X × Y) :=
  (∑ i, c i • d i, a • e, 0)

theorem incidenceFiniteDirection_response
    (J : P × (X × Y) →L[ℝ] W) (d : ι → P)
    (a : ℝ) (c : ι → ℝ) (e : X) :
    J (incidenceFiniteDirection d a c e) =
      (∑ i, c i • J (d i, 0, 0)) + J (0, a • e, 0) := by
  have hd : incidenceFiniteDirection (Y := Y) d a c e =
      (∑ i, c i • (d i, (0 : X), (0 : Y))) + (0, a • e, 0) := by
    ext <;> simp [incidenceFiniteDirection, Prod.fst_sum, Prod.snd_sum]
  rw [hd, map_add, map_sum]
  simp only [map_smul]

/-- Actual native parameter and source errors combine with fixed finite
coefficients. This retains the exact source scale and both endpoints. -/
theorem norm_jointScaledIncidence_finite_error_le
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y)
    (hJ : DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y))
    (d : ι → P) (principal : ι → R × V) (D : X →L[ℝ] V)
    (ep es : ℝ) (hep : 0 ≤ ep)
    (hparam : ∀ i,
      ‖fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u (d i) -
        principal i‖ ≤ ep)
    (hsource : ∀ e,
      ‖fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • e) -
        (0, D e)‖ ≤ es * ‖e‖)
    (c : ι → ℝ) (e : X) :
    ‖fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)
        (incidenceFiniteDirection (Y := Y) d a c e) -
      ((∑ i, c i • principal i) + (0, D e))‖ ≤
        (Fintype.card ι : ℝ) * ep * ‖c‖ + es * ‖e‖ := by
  let J := fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)
  have hp : ∀ i, ‖J (d i, 0, 0) - principal i‖ ≤ ep := by
    intro i
    simpa only [J, jointScaledIncidence_parameter_column B F H equation sigma a
      u x y (d i) hJ] using hparam i
  have hs : ‖J (0, a • e, 0) - (0, D e)‖ ≤ es * ‖e‖ := by
    simpa only [J, fderiv_joint_first_source_column _ u x y hJ,
      jointScaledIncidence] using hsource e
  change ‖J (incidenceFiniteDirection (Y := Y) d a c e) - _‖ ≤ _
  rw [incidenceFiniteDirection_response]
  have heq : (∑ i, c i • J (d i, 0, 0)) + J (0, a • e, 0) -
      ((∑ i, c i • principal i) + (0, D e)) =
      (∑ i, c i • (J (d i, 0, 0) - principal i)) +
        (J (0, a • e, 0) - (0, D e)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_incidence_finite_column_error_le _ hep hp c) hs)

/-- Rank of the actual full derivative follows from its actual finite errors
relative to a frame selected in the geometric principal map. There is no
assumption asserting the desired rank of this derivative. -/
theorem jointScaledIncidence_rank_of_finite_principal_frame {k : ℕ}
    [FiniteDimensional ℝ R] [FiniteDimensional ℝ V]
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a : ℝ) (u : P) (x : X) (y : Y)
    (hJ : DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y))
    (d : ι → P) (principal : ι → R × V) (D : X →L[ℝ] V)
    (c : Fin k → ι → ℝ) (e : Fin k → X)
    (m ep es b : ℝ) (hep : 0 ≤ ep) (hb : 0 ≤ b)
    (hframe : ∀ z : Fin k → ℝ,
      m * ‖z‖ ≤ ‖∑ j, z j • ((∑ i, c j i • principal i) + (0, D (e j)))‖)
    (hparam : ∀ i,
      ‖fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u (d i) -
        principal i‖ ≤ ep)
    (hsource : ∀ v,
      ‖fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • v) -
        (0, D v)‖ ≤ es * ‖v‖)
    (herror : ∀ j, (Fintype.card ι : ℝ) * ep * ‖c j‖ + es * ‖e j‖ ≤ b)
    (hsmall : (k : ℝ) * b < m) :
    k ≤ Module.finrank ℝ
      (fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)).range := by
  apply finrank_range_ge_of_close_finite_columns
    (fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y))
    (ContinuousLinearMap.id ℝ (R × V))
    (fun j ↦ incidenceFiniteDirection (Y := Y) d a (c j) (e j))
    (fun j ↦ (∑ i, c j i • principal i) + (0, D (e j))) hb hframe
  · intro j
    exact (norm_jointScaledIncidence_finite_error_le B F H equation sigma a u x y
      hJ d principal D ep es hep hparam hsource (c j) (e j)).trans (herror j)
  · exact hsmall

/-- Choose the single finite response tolerance before the actual perturbed
family or the fast-angle vectors. The fixed source preimages may already
include the inverse of the selected atlas frame at the packet center.
This is internal coefficient bookkeeping for the two actual incidence branches. -/
theorem exists_universal_joint_scaled_rank_tolerance {k : ℕ}
    [FiniteDimensional ℝ R] [FiniteDimensional ℝ V]
    (principal : ι → R × V) (D : X →L[ℝ] V)
    (c : Fin k → ι → ℝ) (e : Fin k → X) (m : ℝ) (hm : 0 < m)
    (hframe : ∀ z : Fin k → ℝ,
      m * ‖z‖ ≤ ‖∑ j, z j • ((∑ i, c j i • principal i) + (0, D (e j)))‖) :
    ∃ eps > 0,
      ∀ (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P],
      ∀ (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
        (sigma a : ℝ) (u : P) (x : X) (y : Y),
      DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y) →
      ∀ d : ι → P,
      (∀ i, ‖fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u (d i) -
        principal i‖ ≤ eps) →
      (∀ v, ‖fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • v) -
        (0, D v)‖ ≤ eps * ‖v‖) →
      k ≤ Module.finrank ℝ
        (fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)).range := by
  obtain ⟨C, hC⟩ := Finite.exists_le
    (fun j : Fin k ↦ (Fintype.card ι : ℝ) * ‖c j‖ + ‖e j‖)
  let b := m / (2 * ((k : ℝ) + 1))
  have hb : 0 < b := div_pos hm (by positivity)
  let eps := b / (|C| + 1)
  have heps : 0 < eps := div_pos hb (by positivity)
  have hsmall : (k : ℝ) * b < m := by
    dsimp [b]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * ((k : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have herror (j : Fin k) :
      (Fintype.card ι : ℝ) * eps * ‖c j‖ + eps * ‖e j‖ ≤ b := by
    calc
      _ = eps * ((Fintype.card ι : ℝ) * ‖c j‖ + ‖e j‖) := by ring
      _ ≤ eps * (|C| + 1) := mul_le_mul_of_nonneg_left
        ((hC j).trans ((le_abs_self C).trans (by linarith))) heps.le
      _ = b := div_mul_cancel₀ b (by positivity : |C| + 1 ≠ 0)
  refine ⟨eps, heps, ?_⟩
  intro P instP instPR B F H equation sigma a u x y hJ d hp hs
  exact jointScaledIncidence_rank_of_finite_principal_frame B F H equation sigma a
    u x y hJ d principal D c e m eps eps b heps.le hb.le hframe hp hs herror hsmall

/-- Specialization of the parameter-independent tolerance to a chosen parameter space. -/
theorem exists_joint_scaled_rank_tolerance {k : ℕ}
    [FiniteDimensional ℝ R] [FiniteDimensional ℝ V]
    (principal : ι → R × V) (D : X →L[ℝ] V)
    (c : Fin k → ι → ℝ) (e : Fin k → X) (m : ℝ) (hm : 0 < m)
    (hframe : ∀ z : Fin k → ℝ,
      m * ‖z‖ ≤ ‖∑ j, z j • ((∑ i, c j i • principal i) + (0, D (e j)))‖) :
    ∃ eps > 0,
      ∀ (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
        (sigma a : ℝ) (u : P) (x : X) (y : Y),
      DifferentiableAt ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y) →
      ∀ d : ι → P,
      (∀ i, ‖fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u (d i) -
        principal i‖ ≤ eps) →
      (∀ v, ‖fderiv ℝ (fun z ↦ scaledIncidence B F H equation sigma a u z y) x (a • v) -
        (0, D v)‖ ≤ eps * ‖v‖) →
      k ≤ Module.finrank ℝ
        (fderiv ℝ (jointScaledIncidence B F H equation sigma a) (u, x, y)).range := by
  obtain ⟨eps, heps, htol⟩ := exists_universal_joint_scaled_rank_tolerance
    (T := T) (Y := Y) principal D c e m hm hframe
  exact ⟨eps, heps, htol P⟩

end GlobalEmbedding.Upgrade
