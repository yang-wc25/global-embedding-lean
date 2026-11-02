import Smoothing.IntegrationSpatialWeighted

/-!
# Original anisotropic gain from the genuine spatial C2 input

The input is the order-zero spatial packet, containing values, first spatial
derivatives and second spatial derivatives only. No parameter derivative is
included in that input norm. Joint output derivatives are bounded after the
actual smoothing operation. This file performs only the exact norm transfer
and finite weighted summation needed by the global geometric construction.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff ENNReal BigOperators

namespace GlobalEmbedding.Continuation

attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

theorem parameterSpatialNativeFactor_mono (n d q : ℕ) {k j : ℕ} (hkj : k ≤ j) :
    parameterSpatialNativeFactor n d q k ≤ parameterSpatialNativeFactor n d q j := by
  unfold parameterSpatialNativeFactor
  exact mul_le_mul_of_nonneg_left (nativeCoordinateFactor_mono _ hkj)
    (spatialJetReconstructionConstant_nonneg n q)

/-- The same original weighted source norm controls every native spatial-jet
derivative with its own weight, retaining only dimension/order conversion costs. -/
theorem parameterSpatialWeighted_native_jet_le
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) (t : ℝ) (ht : 0 < t)
    (f : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O S : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hfinite : parameterSpatialWeighted (n := n) (d := d) m t f O S ≠ ⊤)
    (i : ι) {j k : ℕ} (hjm : j ≤ m) (hkj : k ≤ j)
    {z : (Fin d → ℝ) × (Fin n → ℝ)} (hz : sourceFirstCoordinates n d z ∈ S i) :
    t ^ j * ‖iteratedFDeriv ℝ k (spatialNativeJet (f i ∘ sourceFirstCoordinates n d)) z‖ ≤
      parameterSpatialNativeFactor n d q m *
        (parameterSpatialWeighted (n := n) (d := d) m t f O S).toReal := by
  have hfinj := parameterSpatialWeighted_Cj_ne_top m ht f O S hfinite hjm
  have hn := parameterSpatialCj_native_jet_le j f O S hO hSO hf hfinj i hkj hz
  have hterm : t ^ j * (parameterSpatialCj (n := n) (d := d) j f O S).toReal ≤
      (parameterSpatialWeighted (n := n) (d := d) m t f O S).toReal := by
    rw [parameterSpatialWeighted_toReal m t ht.le f O S hfinite]
    exact Finset.single_le_sum (s := Finset.range (m+1)) (a := j)
      (f := fun a => t ^ a * (parameterSpatialCj (n := n) (d := d) a f O S).toReal)
      (fun a _ => mul_nonneg (pow_nonneg ht.le a) ENNReal.toReal_nonneg)
      (by simpa using hjm)
  calc
    _ ≤ t ^ j * (parameterSpatialNativeFactor n d q j *
        (parameterSpatialCj (n := n) (d := d) j f O S).toReal) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg ht.le j)
    _ = parameterSpatialNativeFactor n d q j *
        (t ^ j * (parameterSpatialCj (n := n) (d := d) j f O S).toReal) := by ring
    _ ≤ parameterSpatialNativeFactor n d q m *
        (parameterSpatialWeighted (n := n) (d := d) m t f O S).toReal :=
      mul_le_mul (parameterSpatialNativeFactor_mono n d q hjm) hterm
        (mul_nonneg (pow_nonneg ht.le j) ENNReal.toReal_nonneg)
        (parameterSpatialNativeFactor_nonneg n d q m)

/-- Original weighted smoothing gain from native gain bounds for the same
actual map. The source is the literal spatial C2 packet at joint order zero. -/
theorem parameterSpatialWeighted_gain_of_native
    {ι : Type*} [Fintype ι] {n d q : ℕ}
    (m : ℕ) (f s : ι → (Fin (n+d) → ℝ) → Fin q → ℝ)
    (O U V : ι → Set (Fin (n+d) → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hUO : ∀ i, U i ⊆ O i)
    (hs : ∀ i, ContDiffOn ℝ ∞ (s i) (O i))
    (_hfinite0 : parameterSpatialCj (n := n) (d := d) 0 f O V ≠ ⊤)
    (ell tau G : ℝ) (hell : 0 < ell) (htau : 0 ≤ tau) (htaul : tau ≤ ell) (hG : 0 ≤ G)
    (hgain : ∀ j ≤ m, ∀ i, ∀ k ≤ j,
      ∀ z : (Fin d → ℝ) × (Fin n → ℝ), sourceFirstCoordinates n d z ∈ U i →
        ‖iteratedFDeriv ℝ k (spatialNativeJet (s i ∘ sourceFirstCoordinates n d)) z‖ ≤
          G * (ell ^ j)⁻¹ * (parameterSpatialCj (n := n) (d := d) 0 f O V).toReal) :
    parameterSpatialWeighted (n := n) (d := d) m tau s O U ≠ ⊤ ∧
      (parameterSpatialWeighted (n := n) (d := d) m tau s O U).toReal ≤
        ((m+1 : ℕ) : ℝ) * parameterSpatialCoordinateFactor n d q m * G *
          (parameterSpatialCj (n := n) (d := d) 0 f O V).toReal := by
  let I := (parameterSpatialCj (n := n) (d := d) 0 f O V).toReal
  have hI : 0 ≤ I := ENNReal.toReal_nonneg
  have hb (j : ℕ) (hj : j ≤ m) :=
    parameterSpatialCj_finite_and_bound_of_native j s O U hO hUO hs
      (G * (ell ^ j)⁻¹ * I) (by positivity) (hgain j hj)
  have hout := parameterSpatialWeighted_ne_top_of_Cj m tau s O U (fun j hj => (hb j hj).1)
  have hscaled (j : ℕ) (hj : j ≤ m) :
      ell ^ j * (parameterSpatialCj (n := n) (d := d) j s O U).toReal ≤
        parameterSpatialCoordinateFactor n d q m * G * I := by
    have hn : ell ^ j ≠ 0 := pow_ne_zero j hell.ne'
    calc
      _ ≤ ell ^ j * (parameterSpatialCoordinateFactor n d q j * (G * (ell ^ j)⁻¹ * I)) :=
        mul_le_mul_of_nonneg_left (hb j hj).2 (pow_nonneg hell.le j)
      _ = parameterSpatialCoordinateFactor n d q j * G * I := by field_simp
      _ ≤ parameterSpatialCoordinateFactor n d q m * G * I :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (parameterSpatialCoordinateFactor_mono n d q hj) hG) hI
  refine ⟨hout, ?_⟩
  rw [parameterSpatialWeighted_toReal m tau htau s O U hout]
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), parameterSpatialCoordinateFactor n d q m * G * I := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := by simpa using hj
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ htau htaul j)
        ENNReal.toReal_nonneg).trans (hscaled j hjm)
    _ = _ := by simp [I, Finset.sum_const, nsmul_eq_mul, mul_assoc]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterSpatialWeighted_native_jet_le
#print axioms GlobalEmbedding.Continuation.parameterSpatialWeighted_gain_of_native
