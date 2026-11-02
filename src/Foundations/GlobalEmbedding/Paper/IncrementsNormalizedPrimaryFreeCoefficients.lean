import GlobalEmbedding.Paper.IncrementsPositiveReserveAmplitude
import GlobalEmbedding.Paper.IncrementsMeanQuadraticCoefficients

/-!
# Actual normalized free primary coefficients

Source: original `lem:increments`, main.tex638–661. The free amplitude is the
canonical positive-reserve construction, with delta set to one before estimating.
The slow derivative is an actual component of the primary error, not the whole
reconstructed error. All correction terms remain separate original obligations.
-/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- The fixed native complex coordinate of the original Euclidean amplitude.
Source: component coefficients in original main.tex645–661. -/
def incrementsFreeComplexCoordinate {N : ℕ} (c : Fin N) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj c)

/-- The original normalized leading coefficient is the same actual free amplitude
at delta=tau=1, multiplied by the phase covector and i. No norm is identified.
Source: original main.tex644–646. -/
theorem increments_normalized_leading_from_free {n N : ℕ} {I : Type*}
    (b : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin n)) (xi : I → ℝ) (i : I) (c : Fin N) :
    incrementsLeadingCoefficient 1 (b x) (normal x) xi i c =
      Complex.I * (xi i : ℂ) *
        incrementsFreeComplexCoordinate c (incrementsPrimaryFreeAmplitude 1 1 b normal x) := by
  change Complex.I * (Real.sqrt 2 * 1 * b x * normal x c * xi i : ℝ) =
    Complex.I * (xi i : ℂ) * ((Real.sqrt 2 * 1 * 1 * b x * normal x c : ℝ) : ℂ)
  push_cast
  ring

/-- With correction fields zero, the literal canonical error is exactly the
derivative of the same free amplitude, including both amplitude and normal terms.
This identifies only the free slow part, without asserting corrections vanish.
Source: original main.tex645–651. -/
theorem increments_primary_error_free_slow_eq {A : Type*} [Fintype A] {n N : ℕ}
    (tau : ℝ) (b phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (c : Fin N)
    (hb : DifferentiableAt ℝ b x) (hn : DifferentiableAt ℝ normal x) :
    incrementsPrimaryErrorCoefficient (A := A) 1 tau b phi normal
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) x v c =
      incrementsFreeComplexCoordinate c
        (fderiv ℝ (incrementsPrimaryFreeAmplitude 1 tau b normal) x v) := by
  rw [increments_primary_free_amplitude_first_jet 1 tau b normal x v hb hn]
  simp [incrementsPrimaryErrorCoefficient, incrementsPrimaryDerivativeCoefficient,
    incrementsFreeComplexCoordinate, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_add]
  ring

/-- Original reserve inputs produce the actual normalized free amplitude and its
slow derivative-field size and SAME input difference. The constant is chosen before
the fields and tau, delta is exactly one, and the derivative costs only one original
input order. Source: original main.tex638–661. Corrections are not bounded here. -/
theorem increments_normalized_free_amplitude_firstjet_bounds
    (j : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (O S : Set (EuclideanSpace ℝ (Fin n))) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : EuclideanSpace ℝ (Fin n) → E →L[ℝ] ℝ)
        (A B : EuclideanSpace ℝ (Fin n) → E)
        (cutoff : EuclideanSpace ℝ (Fin n) → ℝ)
        (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
        (_hL : ContDiffOn ℝ ∞ L O) (_hA : ContDiffOn ℝ ∞ A O)
        (_hB : ContDiffOn ℝ ∞ B O) (_hcutoff : ContDiffOn ℝ ∞ cutoff O)
        (_hnormal : ContDiffOn ℝ ∞ normal O)
        (ell Delta tau : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S, c ≤ L x (A x) ∧ c ≤ L x (B x))
        (_hLb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M)
        (_hAb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
        (_hBb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
        (_hcutoffb : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ M)
        (_hnormalb : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ M)
        (_hdiff : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ A y - B y) x‖ ≤ Delta),
      let vA := incrementsPrimaryFreeAmplitude 1 tau
        (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal
      let vB := incrementsPrimaryFreeAmplitude 1 tau
        (fun y ↦ cutoff y * Real.sqrt (L y (B y))) normal
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k vA x‖ ≤ C * |tau|) ∧
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ vA y - vB y) x‖ ≤ C * |tau| * Delta) ∧
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k (fderiv ℝ vA) x‖ ≤
        C * |tau| / ell) ∧
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ fderiv ℝ vA y - fderiv ℝ vB y) x‖ ≤ (C * |tau| / ell) * Delta) := by
  obtain ⟨C, hC, hb⟩ := increments_primary_free_amplitude_scaled_bounds (j + 1) c M hc hM
  refine ⟨C, hC, ?_⟩
  intro n N E _ _ O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
    ell Delta tau hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hdiff
  let vA := incrementsPrimaryFreeAmplitude 1 tau
    (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal
  let vB := incrementsPrimaryFreeAmplitude 1 tau
    (fun y ↦ cutoff y * Real.sqrt (L y (B y))) normal
  have hval := hb O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
    ell Delta 1 tau hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hdiff
  have hvs : ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k vA x‖ ≤ C * |tau| := by
    simpa only [abs_one, mul_one] using hval.1
  have hvd : ∀ k ≤ j + 1, ∀ x ∈ S,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ vA y - vB y) x‖ ≤ C * |tau| * Delta := by
    simpa only [abs_one, mul_one] using hval.2
  have hAs : ∀ x ∈ S, ContDiffAt ℝ ∞ vA x := by
    intro x hx
    have ha := increments_positive_reserve_amplitude_contDiffAt O hO L A cutoff normal
      hL hA hcutoff hnormal (hSO hx) (hc.trans_le (hreserve x hx).1)
    convert ha.const_smul (Real.sqrt 2 * (1 : ℝ) * tau) using 1
    funext y
    simp [vA, incrementsPrimaryFreeAmplitude, smul_smul]
  have hBs : ∀ x ∈ S, ContDiffAt ℝ ∞ vB x := by
    intro x hx
    have hb := increments_positive_reserve_amplitude_contDiffAt O hO L B cutoff normal
      hL hB hcutoff hnormal (hSO hx) (hc.trans_le (hreserve x hx).2)
    convert hb.const_smul (Real.sqrt 2 * (1 : ℝ) * tau) using 1
    funext y
    simp [vB, incrementsPrimaryFreeAmplitude, smul_smul]
  refine ⟨fun k hk x hx ↦ hvs k (by omega) x hx,
    fun k hk x hx ↦ hvd k (by omega) x hx, ?_, ?_⟩
  · intro k hk x hx
    apply (le_div_iff₀ hell).2
    rw [norm_iteratedFDeriv_fderiv]
    calc
      _ = ell ^ (k + 1) * ‖iteratedFDeriv ℝ (k + 1) vA x‖ := by rw [pow_succ]; ring
      _ ≤ C * |tau| := hvs (k + 1) (by omega) x hx
  · intro k hk x hx
    have hAs1 : ContDiffAt ℝ 1 vA x := (hAs x hx).of_le (by simp)
    have hBs1 : ContDiffAt ℝ 1 vB x := (hBs x hx).of_le (by simp)
    have he : (fun y ↦ fderiv ℝ vA y - fderiv ℝ vB y) =ᶠ[𝓝 x]
        fderiv ℝ (fun y ↦ vA y - vB y) := by
      filter_upwards [hAs1.eventually (by norm_num), hBs1.eventually (by norm_num)]
        with y ha hb
      exact (fderiv_fun_sub (ha.differentiableAt (by norm_num))
        (hb.differentiableAt (by norm_num))).symm
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, norm_iteratedFDeriv_fderiv]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hell).2
    calc
      _ = ell ^ (k + 1) * ‖iteratedFDeriv ℝ (k + 1)
          (fun y ↦ vA y - vB y) x‖ := by rw [pow_succ]; ring
      _ ≤ C * |tau| * Delta := hvd (k + 1) (by omega) x hx

/-- Actual canonical leading coefficients inherit all scaled jets and SAME input
difference from the original reserve data and original phase-gradient jets. Geometry
is fixed when the tensor input varies. Source: original main.tex644–661. -/
theorem increments_normalized_primary_leading_scaled_bounds {n N : ℕ}
    (coord : Fin N) (v : EuclideanSpace ℝ (Fin n))
    (j : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        (O S : Set (EuclideanSpace ℝ (Fin n))) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : EuclideanSpace ℝ (Fin n) → E →L[ℝ] ℝ)
        (A B : EuclideanSpace ℝ (Fin n) → E)
        (cutoff phi : EuclideanSpace ℝ (Fin n) → ℝ)
        (normal : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
        (_hL : ContDiffOn ℝ ∞ L O) (_hA : ContDiffOn ℝ ∞ A O)
        (_hB : ContDiffOn ℝ ∞ B O) (_hcutoff : ContDiffOn ℝ ∞ cutoff O)
        (_hphi : ContDiffOn ℝ ∞ phi O) (_hnormal : ContDiffOn ℝ ∞ normal O)
        (ell Delta : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S, c ≤ L x (A x) ∧ c ≤ L x (B x))
        (_hLb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M)
        (_hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
        (_hBb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
        (_hcutoffb : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ M)
        (_hnormalb : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ M)
        (_hphib : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ fderiv ℝ phi y v) x‖ ≤ M)
        (_hdiff : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ A y - B y) x‖ ≤ Delta),
      let leadA := fun y ↦ incrementsLeadingCoefficient 1
        (cutoff y * Real.sqrt (L y (A y))) (normal y)
        (fun _ : Unit ↦ fderiv ℝ phi y v) () coord
      let leadB := fun y ↦ incrementsLeadingCoefficient 1
        (cutoff y * Real.sqrt (L y (B y))) (normal y)
        (fun _ : Unit ↦ fderiv ℝ phi y v) () coord
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k leadA x‖ ≤ C) ∧
      (∀ k ≤ j, ∀ x ∈ S,
        ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ leadA y - leadB y) x‖ ≤ C * Delta) := by
  obtain ⟨Ca, hCa, hbound⟩ := increments_primary_free_amplitude_scaled_bounds j c M hc hM
  let P : EuclideanSpace ℝ (Fin N) →L[ℝ] ℂ :=
    Complex.I • incrementsFreeComplexCoordinate coord
  let H : ℝ →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℂ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight P
  refine ⟨2 ^ j * (‖H‖ * M) * Ca, by positivity, ?_⟩
  intro E _ _ O S hO hSO L A B cutoff phi normal hL hA hB hcutoff hphi hnormal
    ell Delta hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hphib hdiff
  let a := fun y ↦ L y (A y)
  let b := fun y ↦ L y (B y)
  let U := (O ∩ a ⁻¹' Set.Ioi 0) ∩ (O ∩ b ⁻¹' Set.Ioi 0)
  have ha : ContDiffOn ℝ ∞ a O := hL.clm_apply hA
  have hb : ContDiffOn ℝ ∞ b O := hL.clm_apply hB
  have hU : IsOpen U :=
    (ha.continuousOn.isOpen_inter_preimage hO isOpen_Ioi).inter
      (hb.continuousOn.isOpen_inter_preimage hO isOpen_Ioi)
  have hUO : U ⊆ O := fun _ hy ↦ hy.1.1
  have hSU : S ⊆ U := fun y hy ↦
    ⟨⟨hSO hy, hc.trans_le (hreserve y hy).1⟩,
      ⟨hSO hy, hc.trans_le (hreserve y hy).2⟩⟩
  let vA := incrementsPrimaryFreeAmplitude 1 1
    (fun y ↦ cutoff y * Real.sqrt (a y)) normal
  let vB := incrementsPrimaryFreeAmplitude 1 1
    (fun y ↦ cutoff y * Real.sqrt (b y)) normal
  have hvA : ContDiffOn ℝ ∞ vA U := by
    have hs := ((hcutoff.mono hUO).mul
      ((ha.mono hUO).sqrt (fun _ hy ↦ hy.1.2.ne'))).smul (hnormal.mono hUO)
    convert hs.const_smul (Real.sqrt 2) using 1
    funext y
    simp [vA, incrementsPrimaryFreeAmplitude, smul_smul]
  have hvB : ContDiffOn ℝ ∞ vB U := by
    have hs := ((hcutoff.mono hUO).mul
      ((hb.mono hUO).sqrt (fun _ hy ↦ hy.2.2.ne'))).smul (hnormal.mono hUO)
    convert hs.const_smul (Real.sqrt 2) using 1
    funext y
    simp [vB, incrementsPrimaryFreeAmplitude, smul_smul]
  let g := fun y ↦ fderiv ℝ phi y v
  have hg : ContDiffOn ℝ ∞ g O :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp_contDiffOn
      (hphi.fderiv_of_isOpen hO (by simp))
  have hAg : ContDiffOn ℝ ∞ (fun y ↦ H (g y)) U :=
    (H.contDiff.comp_contDiffOn hg).mono hUO
  have hgj : ∀ i ≤ j, ∀ x ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ H (g y)) x‖ ≤ ‖H‖ * M := by
    intro i hi x hx
    have hs := hg.contDiffAt (hO.mem_nhds (hSO hx))
    rw [show (fun y ↦ H (g y)) = H ∘ g from rfl,
      H.iteratedFDeriv_comp_left hs (by simp)]
    calc
      _ ≤ ell ^ i * (‖H‖ * ‖iteratedFDeriv ℝ i g x‖) :=
        mul_le_mul_of_nonneg_left (H.norm_compContinuousMultilinearMap_le _) (by positivity)
      _ = ‖H‖ * (ell ^ i * ‖iteratedFDeriv ℝ i g x‖) := by ring
      _ ≤ ‖H‖ * M := mul_le_mul_of_nonneg_left (hphib i hi x hx) (norm_nonneg H)
  have hval := hbound O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
    ell Delta 1 1 hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hdiff
  have heA : (fun y ↦ incrementsLeadingCoefficient 1
      (cutoff y * Real.sqrt (L y (A y))) (normal y)
      (fun _ : Unit ↦ fderiv ℝ phi y v) () coord) = (fun y ↦ H (g y) (vA y)) := by
    funext y
    rw [increments_normalized_leading_from_free
      (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal y
      (fun _ : Unit ↦ fderiv ℝ phi y v) () coord]
    change Complex.I * (g y : ℂ) * incrementsFreeComplexCoordinate coord (vA y) =
      g y • (Complex.I * incrementsFreeComplexCoordinate coord (vA y))
    simp only [Complex.real_smul]
    ring
  have heB : (fun y ↦ incrementsLeadingCoefficient 1
      (cutoff y * Real.sqrt (L y (B y))) (normal y)
      (fun _ : Unit ↦ fderiv ℝ phi y v) () coord) = (fun y ↦ H (g y) (vB y)) := by
    funext y
    rw [increments_normalized_leading_from_free
      (fun y ↦ cutoff y * Real.sqrt (L y (B y))) normal y
      (fun _ : Unit ↦ fderiv ℝ phi y v) () coord]
    change Complex.I * (g y : ℂ) * incrementsFreeComplexCoordinate coord (vB y) =
      g y • (Complex.I * incrementsFreeComplexCoordinate coord (vB y))
    simp only [Complex.real_smul]
    ring
  dsimp only
  simp_rw [congrFun heA, congrFun heB]
  constructor
  · intro k hk x hx
    have hh := scaled_clm_apply U hU (fun y ↦ H (g y)) vA hAg hvA
      k 0 ell (‖H‖ * M) Ca hell.le
      (fun i hi ↦ hgj i (hi.trans hk) x hx)
      (fun i hi ↦ by simpa [vA, a] using hval.1 i (hi.trans hk) x hx) (hSU hx)
    calc
      _ ≤ 2 ^ k * (‖H‖ * M) * Ca := by simpa using hh
      _ ≤ 2 ^ j * (‖H‖ * M) * Ca := by gcongr; norm_num
  · intro k hk x hx
    have he : (fun y ↦ H (g y) (vA y) - H (g y) (vB y)) =
        (fun y ↦ H (g y) (vA y - vB y)) := funext fun y ↦ (map_sub _ _ _).symm
    rw [he]
    have hh := scaled_clm_apply U hU (fun y ↦ H (g y)) (fun y ↦ vA y - vB y)
      hAg (hvA.sub hvB) k 0 ell (‖H‖ * M) (Ca * Delta) hell.le
      (fun i hi ↦ hgj i (hi.trans hk) x hx)
      (fun i hi ↦ by simpa [vA, vB, a, b] using hval.2 i (hi.trans hk) x hx) (hSU hx)
    calc
      _ ≤ 2 ^ k * (‖H‖ * M) * (Ca * Delta) := by simpa using hh
      _ ≤ 2 ^ j * (‖H‖ * M) * (Ca * Delta) := by gcongr; norm_num
      _ = (2 ^ j * (‖H‖ * M) * Ca) * Delta := by ring

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.incrementsFreeComplexCoordinate
#print axioms GlobalEmbedding.Paper.increments_normalized_free_amplitude_firstjet_bounds
#print axioms GlobalEmbedding.Paper.increments_normalized_leading_from_free
#print axioms GlobalEmbedding.Paper.increments_primary_error_free_slow_eq

#print axioms GlobalEmbedding.Paper.increments_normalized_primary_leading_scaled_bounds
