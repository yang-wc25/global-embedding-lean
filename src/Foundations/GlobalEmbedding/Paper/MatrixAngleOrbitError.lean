import GlobalEmbedding.Paper.MatrixAngleNativeSmoothFlat
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The original scaled orbit error of the actual angle ansatz

Source: `main.tex`, `prop:matrix`, equation(3.3), lines311–323.
DAG node: `matrix-angle-orbit-error`; exclusive owner W2.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Set Filter

namespace GlobalEmbedding.Paper

variable {C : ℕ}

/-- The fixed actual sine field, including the actual curvature cutoff. -/
def matrixAngleSinField (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients :=
  matrixAngleCutoff κ z •
    (-EuclideanSpace.single 0 (1 : ℝ) -
      orbitDeriv planarHopfFlow f z 0 • EuclideanSpace.single 2 (1 : ℝ))

/-- The fixed actual cosine field, including the actual curvature cutoff. -/
def matrixAngleCosField (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients :=
  matrixAngleCutoff κ z •
    (orbitDeriv planarHopfFlow f z 1 • EuclideanSpace.single 1 (1 : ℝ) +
      matrixAngleNormalPosition f z • EuclideanSpace.single 3 (1 : ℝ))

/-- The actual oscillatory direction is a sine/cosine combination of two fixed fields. -/
theorem matrixAngleBaseProfile_decompose (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C) :
    matrixAngleCutoff κ z • matrixAngleBaseProfile f T z =
      Real.sin (T * orbitDeriv planarHopfFlow f z 1) • matrixAngleSinField f κ z +
        Real.cos (T * orbitDeriv planarHopfFlow f z 1) • matrixAngleCosField f κ z := by
  ext i
  fin_cases i <;>
    simp [matrixAngleBaseProfile, matrixAngleMomentDirection, matrixAngleSinField,
      matrixAngleCosField, EuclideanSpace.single, mul_comm, mul_assoc]

/-- The actual phase error is the scalar sine/cosine combination of these actual fields. -/
theorem matrixAngleAnsatz_error_decompose (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (a : MatrixAngleCoefficients)
    (z : PlanarHopfSphere C) :
    matrixAngleAnsatz f κ T a z - T * orbitDeriv planarHopfFlow f z 1 =
      Real.sin (T * orbitDeriv planarHopfFlow f z 1) * ⟪matrixAngleSinField f κ z, a⟫ +
        Real.cos (T * orbitDeriv planarHopfFlow f z 1) * ⟪matrixAngleCosField f κ z, a⟫ := by
  calc
    _ = ⟪matrixAngleCutoff κ z • matrixAngleBaseProfile f T z, a⟫ := by
      simp [matrixAngleAnsatz, real_inner_smul_left]
    _ = _ := by rw [matrixAngleBaseProfile_decompose]; simp only [inner_add_left, real_inner_smul_left]

variable [Fact (0 < C)]

/-- Both fixed weighted fields are native smooth, independently of frequency. -/
theorem matrixAngleFixedFields_contMDiff (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) :
    ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ (matrixAngleSinField f κ) ∧
      ContMDiff (planarHopfModel C) 𝓘(ℝ, MatrixAngleCoefficients) ∞ (matrixAngleCosField f κ) := by
  obtain ⟨hs, ht, hb, _⟩ := matrix_planar_data_contMDiff f hf
  have hρ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ (matrixAngleCutoff κ) :=
    expNegInvGlue.contDiff.contMDiff.comp (hκ.pow 2)
  exact ⟨hρ.smul (contMDiff_const.sub (hs.smul contMDiff_const)),
    hρ.smul ((ht.smul contMDiff_const).add (hb.smul contMDiff_const))⟩

/-- The actual orbit derivative of the phase error contains no coefficient derivative:
the supplied coefficient field is constant on the actual orbit. -/
theorem matrixAngleAnsatz_error_orbitDeriv
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) (T : ℝ)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hbasic : ∀ z s, c (planarHopfFlow s z) = c z) (z : PlanarHopfSphere C) :
    orbitDeriv planarHopfFlow
        (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) z =
      (Real.cos (T * orbitDeriv planarHopfFlow f z 1) *
        (T * orbitDeriv planarHopfFlow (matrixPlanarT f) z)) * ⟪matrixAngleSinField f κ z, c z⟫ +
      Real.sin (T * orbitDeriv planarHopfFlow f z 1) *
        ⟪orbitDeriv planarHopfFlow (matrixAngleSinField f κ) z, c z⟫ +
      ((-Real.sin (T * orbitDeriv planarHopfFlow f z 1)) *
        (T * orbitDeriv planarHopfFlow (matrixPlanarT f) z)) * ⟪matrixAngleCosField f κ z, c z⟫ +
      Real.cos (T * orbitDeriv planarHopfFlow f z 1) *
        ⟪orbitDeriv planarHopfFlow (matrixAngleCosField f κ) z, c z⟫ := by
  obtain ⟨hA, hB⟩ := matrixAngleFixedFields_contMDiff f hf κ hκ
  have hcd : HasDerivAt (fun s : ℝ ↦ c (planarHopfFlow s z)) 0 0 := by
    have he : (fun s : ℝ ↦ c (planarHopfFlow s z)) = (fun _ : ℝ ↦ c z) :=
      funext (hbasic z)
    rw [he]
    exact hasDerivAt_const 0 (c z)
  have hAd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add _ hA 0 z).inner ℝ hcd
  have hBd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add _ hB 0 z).inner ℝ hcd
  have htd := (hasDerivAt_orbit planarHopfFlow (planarHopfFlow_contMDiff C)
    planarHopfFlow_add (matrixPlanarT f) (matrix_planar_data_contMDiff f hf).2.1 0 z).const_mul T
  have hd := (htd.sin.fun_mul hAd).fun_add (htd.cos.fun_mul hBd)
  have he : (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) =
      (fun w ↦ Real.sin (T * matrixPlanarT f w) * ⟪matrixAngleSinField f κ w, c w⟫ +
        Real.cos (T * matrixPlanarT f w) * ⟪matrixAngleCosField f κ w, c w⟫) :=
    funext fun w ↦ matrixAngleAnsatz_error_decompose f κ T (c w) w
  rw [he]
  simpa only [orbitDeriv, matrixPlanarT, planarHopfFlow_zero, inner_zero_right, zero_add,
    add_assoc] using hd.deriv

private theorem abs_sum_four_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| :=
  (abs_add_le (a + b + c) d).trans (add_le_add
    ((abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) (le_refl |c|)))
    (le_refl |d|))

/-- Pointwise fixed-field bounds control the original C0 plus scaled-X angle error.
Only the actual basicness of the coefficients is used; no transverse derivative bound occurs. -/
theorem matrixAngleAnsatz_scaled_error_le_of_bounds
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (T M : ℝ) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (c : PlanarHopfSphere C → MatrixAngleCoefficients)
    (hbasic : ∀ z s, c (planarHopfFlow s z) = c z) (z : PlanarHopfSphere C)
    (hA : ‖matrixAngleSinField f κ z‖ ≤ M)
    (hB : ‖matrixAngleCosField f κ z‖ ≤ M)
    (hXA : ‖orbitDeriv planarHopfFlow (matrixAngleSinField f κ) z‖ ≤ M)
    (hXB : ‖orbitDeriv planarHopfFlow (matrixAngleCosField f κ) z‖ ≤ M)
    (hphase : |orbitDeriv planarHopfFlow (matrixPlanarT f) z| ≤ M) :
    |matrixAngleAnsatz f κ T (c z) z - T * orbitDeriv planarHopfFlow f z 1| +
        T⁻¹ * |orbitDeriv planarHopfFlow
          (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) z| ≤
      (4 * M + 2 * M ^ 2) * ‖c z‖ := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hi (v : MatrixAngleCoefficients) (hv : ‖v‖ ≤ M) : |⟪v, c z⟫| ≤ M * ‖c z‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  have ht (u q : ℝ) (hu : |u| ≤ 1) (hq : |q| ≤ M * ‖c z‖) :
      |u * q| ≤ M * ‖c z‖ := by
    rw [abs_mul]
    exact (mul_le_mul hu hq (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hfreq (u q : ℝ) (hu : |u| ≤ 1) (hq : |q| ≤ M * ‖c z‖) :
      |(u * (T * orbitDeriv planarHopfFlow (matrixPlanarT f) z)) * q| ≤
        T * M ^ 2 * ‖c z‖ := by
    simp only [abs_mul, abs_of_pos hTpos]
    calc
      |u| * (T * |orbitDeriv planarHopfFlow (matrixPlanarT f) z|) * |q|
          ≤ 1 * (T * M) * (M * ‖c z‖) := by gcongr
      _ = T * M ^ 2 * ‖c z‖ := by ring
  have hzero : |matrixAngleAnsatz f κ T (c z) z - T * orbitDeriv planarHopfFlow f z 1| ≤
      2 * M * ‖c z‖ := by
    rw [matrixAngleAnsatz_error_decompose]
    exact (abs_add_le _ _).trans ((add_le_add
      (ht _ _ (Real.abs_sin_le_one _) (hi _ hA))
      (ht _ _ (Real.abs_cos_le_one _) (hi _ hB))).trans_eq (by ring))
  have hder : |orbitDeriv planarHopfFlow
      (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) z| ≤
      (2 * T * M ^ 2 + 2 * M) * ‖c z‖ := by
    rw [matrixAngleAnsatz_error_orbitDeriv f hf κ hκ T c hbasic z]
    apply (abs_sum_four_le _ _ _ _).trans
    exact (add_le_add (add_le_add (add_le_add
      (hfreq _ _ (Real.abs_cos_le_one _) (hi _ hA))
      (ht _ _ (Real.abs_sin_le_one _) (hi _ hXA)))
      (hfreq _ _ (by simpa only [abs_neg] using (Real.abs_sin_le_one
        (T * orbitDeriv planarHopfFlow f z 1))) (hi _ hB)))
      (ht _ _ (Real.abs_cos_le_one _) (hi _ hXB))).trans_eq (by ring)
  have hinv : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have hscaled : T⁻¹ * |orbitDeriv planarHopfFlow
      (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) z| ≤
      (2 * M ^ 2 + 2 * M) * ‖c z‖ := by
    calc
      _ ≤ T⁻¹ * ((2 * T * M ^ 2 + 2 * M) * ‖c z‖) :=
        mul_le_mul_of_nonneg_left hder (inv_nonneg.mpr hTpos.le)
      _ = (2 * M ^ 2 + 2 * T⁻¹ * M) * ‖c z‖ := by
        field_simp
      _ ≤ (2 * M ^ 2 + 2 * M) * ‖c z‖ := by gcongr; linarith
  exact (add_le_add hzero hscaled).trans_eq (by ring)

/-- Compactness supplies the fixed bound in the original scaled orbit estimate. -/
theorem matrixAngleAnsatz_uniform_scaled_error_bound
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T : ℝ), 1 ≤ T →
      ∀ c : PlanarHopfSphere C → MatrixAngleCoefficients,
      (∀ z s, c (planarHopfFlow s z) = c z) → ∀ z,
      |matrixAngleAnsatz f κ T (c z) z - T * orbitDeriv planarHopfFlow f z 1| +
          T⁻¹ * |orbitDeriv planarHopfFlow
            (fun w ↦ matrixAngleAnsatz f κ T (c w) w - T * orbitDeriv planarHopfFlow f w 1) z| ≤
        B * ‖c z‖ := by
  obtain ⟨hA, hB⟩ := matrixAngleFixedFields_contMDiff f hf κ hκ
  have hXA := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hA
  have hXB := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C) _ hB
  have hXt := contMDiff_orbitDeriv planarHopfFlow (planarHopfFlow_contMDiff C)
    (matrixPlanarT f) (matrix_planar_data_contMDiff f hf).2.1
  let g : PlanarHopfSphere C → ℝ := fun z ↦
    ‖matrixAngleSinField f κ z‖ + ‖matrixAngleCosField f κ z‖ +
    ‖orbitDeriv planarHopfFlow (matrixAngleSinField f κ) z‖ +
    ‖orbitDeriv planarHopfFlow (matrixAngleCosField f κ) z‖ +
    |orbitDeriv planarHopfFlow (matrixPlanarT f) z|
  have hg : Continuous g :=
    (((hA.continuous.norm.add hB.continuous.norm).add hXA.continuous.norm).add
      hXB.continuous.norm).add hXt.continuous.abs
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set (PlanarHopfSphere C)))
    |>.exists_bound_of_continuousOn hg.continuousOn
  let m := max M 0
  have hm : 0 ≤ m := le_max_right _ _
  have hsum (z : PlanarHopfSphere C) : g z ≤ m :=
    (le_abs_self _).trans ((hM z (mem_univ z)).trans (le_max_left _ _))
  refine ⟨4 * m + 2 * m ^ 2, by positivity, ?_⟩
  intro T hT c hbasic z
  have hz := hsum z
  dsimp [g] at hz
  apply matrixAngleAnsatz_scaled_error_le_of_bounds f hf κ hκ T m hT hm c hbasic z
  all_goals linarith [norm_nonneg (matrixAngleSinField f κ z),
    norm_nonneg (matrixAngleCosField f κ z),
    norm_nonneg (orbitDeriv planarHopfFlow (matrixAngleSinField f κ) z),
    norm_nonneg (orbitDeriv planarHopfFlow (matrixAngleCosField f κ) z),
    abs_nonneg (orbitDeriv planarHopfFlow (matrixPlanarT f) z)]

/-- For actual basic coefficient families tending uniformly to zero, the original C0 and
scaled orbit errors tend uniformly to zero together, exactly equation(3.3). -/
theorem matrixAngleAnsatz_scaled_error_tendstoUniformly
    (f : PlanarHopfSphere C → Planar)
    (hf : ContMDiff (planarHopfModel C) 𝓘(ℝ, Planar) ∞ f)
    (κ : PlanarHopfSphere C → ℝ)
    (hκ : ContMDiff (planarHopfModel C) 𝓘(ℝ, ℝ) ∞ κ)
    (c : ℝ → PlanarHopfSphere C → MatrixAngleCoefficients)
    (hbasic : ∀ᶠ T : ℝ in atTop, ∀ z s, c T (planarHopfFlow s z) = c T z)
    (hc : TendstoUniformly c (fun _ ↦ (0 : MatrixAngleCoefficients)) atTop) :
    TendstoUniformly
      (fun T z ↦ |matrixAngleAnsatz f κ T (c T z) z - T * orbitDeriv planarHopfFlow f z 1| +
        T⁻¹ * |orbitDeriv planarHopfFlow
          (fun w ↦ matrixAngleAnsatz f κ T (c T w) w - T * orbitDeriv planarHopfFlow f w 1) z|)
      (fun _ ↦ (0 : ℝ)) atTop := by
  obtain ⟨B, hB, hbound⟩ := matrixAngleAnsatz_uniform_scaled_error_bound f hf κ hκ
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hBp : 0 < B + 1 := by linarith
  have hcoeff := (Metric.tendstoUniformly_iff.mp hc) (ε / (B + 1)) (div_pos hε hBp)
  filter_upwards [hbasic, hcoeff, eventually_ge_atTop (1 : ℝ)] with T hT hcT hlarge z
  have hcn : ‖c T z‖ < ε / (B + 1) := by
    simpa only [dist_zero_left, norm_neg] using hcT z
  have hlt : B * ‖c T z‖ < ε := by
    calc
      _ ≤ (B + 1) * ‖c T z‖ := by gcongr; linarith
      _ < (B + 1) * (ε / (B + 1)) := mul_lt_mul_of_pos_left hcn hBp
      _ = ε := by field_simp
  have hnonneg : 0 ≤
      |matrixAngleAnsatz f κ T (c T z) z - T * orbitDeriv planarHopfFlow f z 1| +
        T⁻¹ * |orbitDeriv planarHopfFlow
          (fun w ↦ matrixAngleAnsatz f κ T (c T w) w - T * orbitDeriv planarHopfFlow f w 1) z| := by
    positivity
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hnonneg] using
    (hbound T hlarge (c T) hT z).trans_lt hlt

end GlobalEmbedding.Paper
