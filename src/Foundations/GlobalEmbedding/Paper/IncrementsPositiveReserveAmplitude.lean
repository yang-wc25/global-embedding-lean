import GlobalEmbedding.Paper.IncrementsPrimaryWaveFirstJet
import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact

/-!
# Original positive-reserve primary amplitudes

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines594–609 and638–673.
Exclusive child: `increments-positive-reserve-amplitude-estimates`, worker W5.
All bounds concern actual native functions and iterated Fréchet derivatives. The
compact sets used below are scalar operation ranges, never source domains.
-/

open scoped ContDiff Topology
open Set

namespace GlobalEmbedding.Paper

/-- The literal two-input divided-difference factor for the positive square root.
This is a scalar operation on actual values, not a replacement amplitude or norm. -/
noncomputable def incrementsSqrtDifferenceFactor (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt p.1 + Real.sqrt p.2)⁻¹

/-- The divided difference is smooth where both original arguments are positive. -/
theorem incrementsSqrtDifferenceFactor_contDiffOn :
    ContDiffOn ℝ ∞ incrementsSqrtDifferenceFactor (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sqrt p.1)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    contDiffOn_fst.sqrt (fun _ h ↦ h.1.ne')
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ Real.sqrt p.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    contDiffOn_snd.sqrt (fun _ h ↦ h.2.ne')
  exact (h1.add h2).inv (fun p h ↦
    (add_pos (Real.sqrt_pos.2 h.1) (Real.sqrt_pos.2 h.2)).ne')

/-- Exact rationalization retains the actual input difference. No cutoff is divided. -/
theorem incrementsSqrtDifferenceFactor_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt a - Real.sqrt b = (a - b) * incrementsSqrtDifferenceFactor (a, b) := by
  have hn : Real.sqrt a + Real.sqrt b ≠ 0 :=
    (add_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb)).ne'
  simp only [incrementsSqrtDifferenceFactor]
  apply (eq_mul_inv_iff_mul_eq₀ hn).2
  nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]

-- Local application of native compactness and native composition estimates.
-- No derivative carrier or alternate norm is introduced.
private theorem operation_jets_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
  have hi (i : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    have hc := hg.continuousOn_iteratedFDerivWithin (m := i) (by simp) hU.uniqueDiffOn
    exact (hc.mono hKU).congr (fun x hx ↦
      (iteratedFDerivWithin_of_isOpen i hU (hKU hx)).symm)
  induction j with
  | zero =>
      obtain ⟨C, hC⟩ := hi 0
      refine ⟨max 0 C, le_max_left _ _, ?_⟩
      intro i hi x hx
      have : i = 0 := by omega
      subst i
      exact (hC x hx).trans (le_max_right _ _)
  | succ j ih =>
      obtain ⟨C, hC, hCb⟩ := ih
      obtain ⟨T, hT⟩ := hi (j + 1)
      refine ⟨max C T, hC.trans (le_max_left _ _), ?_⟩
      intro i hi x hx
      by_cases hij : i ≤ j
      · exact (hCb i hij x hx).trans (le_max_left _ _)
      · have : i = j + 1 := by omega
        subst i
        exact (hT x hx).trans (le_max_right _ _)

/-- All required derivatives of the actual square-root operation are bounded on
its original scalar reserve interval, including the zeroth derivative. -/
theorem increments_sqrt_reserve_operation_bounds (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ a ∈ Icc c M,
      ‖iteratedFDeriv ℝ i Real.sqrt a‖ ≤ C := by
  exact operation_jets_on_compact Real.sqrt (Ioi 0) (Icc c M) isOpen_Ioi isCompact_Icc
    (fun _ h ↦ hc.trans_le h.1) (fun a ha ↦ (Real.contDiffAt_sqrt ha.ne').contDiffWithinAt) j

/-- The same scalar reserve controls every required derivative of the exact
square-root divided-difference factor on the actual pair of input values. -/
theorem increments_sqrt_difference_operation_bounds (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ p ∈ Icc c M ×ˢ Icc c M,
      ‖iteratedFDeriv ℝ i incrementsSqrtDifferenceFactor p‖ ≤ C := by
  exact operation_jets_on_compact incrementsSqrtDifferenceFactor
    (Ioi 0 ×ˢ Ioi 0) (Icc c M ×ˢ Icc c M) (isOpen_Ioi.prod isOpen_Ioi)
    (isCompact_Icc.prod isCompact_Icc)
    (fun _ h ↦ ⟨hc.trans_le h.1.1, hc.trans_le h.2.1⟩)
    incrementsSqrtDifferenceFactor_contDiffOn j

private theorem operation_scaled_composition
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (f : D → E) (U : Set E) (O : Set D)
    (hU : IsOpen U) (hO : IsOpen O) (hg : ContDiffOn ℝ ∞ g U)
    (hf : ContDiffOn ℝ ∞ f O) (hmap : MapsTo f O U)
    (k : ℕ) (ell M C : ℝ) (hell : 0 < ell) (hM : 1 ≤ M)
    {x : D} (hx : x ∈ O)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hfb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    ell ^ k * ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ k.factorial * C * M ^ k := by
  have hD : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDerivWithin ℝ i f O x‖ ≤ (M / ell) ^ i := by
    intro i hi hik
    rw [iteratedFDerivWithin_of_isOpen i hO hx]
    have hMi : M ≤ M ^ i := le_self_pow₀ hM (by omega)
    calc
      _ ≤ M / ell ^ i := (le_div_iff₀ (pow_pos hell i)).2 (by nlinarith [hfb i hik])
      _ ≤ M ^ i / ell ^ i := div_le_div_of_nonneg_right hMi (by positivity)
      _ = (M / ell) ^ i := (div_pow M ell i).symm
  have hb := norm_iteratedFDerivWithin_comp_le hg hf (n := k) (by simp)
    hU.uniqueDiffOn hO.uniqueDiffOn hmap hx
    (fun i hi ↦ by rw [iteratedFDerivWithin_of_isOpen i hU (hmap hx)]; exact hC i hi) hD
  rw [iteratedFDerivWithin_of_isOpen k hO hx] at hb
  calc
    _ ≤ ell ^ k * (k.factorial * C * (M / ell) ^ k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = k.factorial * C * M ^ k := by rw [div_pow]; field_simp

/-- Genuine local all-order square-root jet bounds from the original scalar reserve
and actual input jets. No compactness of S or positivity away from S is assumed.
Constants are independent of the scale and of the member of the input family. -/
theorem increments_sqrt_reserve_scaled_jets (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O) (a : D → ℝ)
        (_ha : ContDiffOn ℝ ∞ a O) (ell : ℝ) (_hell : 0 < ell)
        (_hreserve : ∀ x ∈ S, c ≤ a x)
        (_hab : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i a x‖ ≤ M),
      ∀ k ≤ j, ∀ x ∈ S,
        ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ Real.sqrt (a y)) x‖ ≤ C := by
  obtain ⟨C, hC, hCb⟩ := increments_sqrt_reserve_operation_bounds j c M hc
  let T := max 1 M
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨j.factorial * C * T ^ j, by positivity, ?_⟩
  intro D _ _ O S hO hSO a ha ell hell hreserve hab k hk x hx
  let P := O ∩ a ⁻¹' Ioi 0
  have hP : IsOpen P := ha.continuousOn.isOpen_inter_preimage hO isOpen_Ioi
  have hxP : x ∈ P := ⟨hSO hx, hc.trans_le (hreserve x hx)⟩
  have haM : a x ≤ M := (le_abs_self _).trans (by simpa using hab 0 (by omega) x hx)
  have hb := operation_scaled_composition Real.sqrt a (Ioi 0) P isOpen_Ioi hP
    (fun z hz ↦ (Real.contDiffAt_sqrt hz.ne').contDiffWithinAt)
    (ha.mono inter_subset_left) (fun _ hy ↦ hy.2) k ell T C hell hT hxP
    (fun i hi ↦ hCb i (hi.trans hk) _ ⟨hreserve x hx, haM⟩)
    (fun i hi ↦ (hab i (hi.trans hk) x hx).trans (le_max_right _ _))
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hC)
    (pow_le_pow_right₀ hT hk) (by positivity) (by positivity)

/-- All-order scaled jets of the actual square-root divided-difference factor.
Only the two original scalar input reserves and input jets are required. -/
theorem increments_sqrt_difference_factor_scaled_jets (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O) (a b : D → ℝ)
        (_ha : ContDiffOn ℝ ∞ a O) (_hb : ContDiffOn ℝ ∞ b O)
        (ell : ℝ) (_hell : 0 < ell)
        (_hreserve : ∀ x ∈ S, c ≤ a x ∧ c ≤ b x)
        (_hab : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i a x‖ ≤ M)
        (_hbb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ M),
      ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ incrementsSqrtDifferenceFactor (a y, b y)) x‖ ≤ C := by
  obtain ⟨C, hC, hCb⟩ := increments_sqrt_difference_operation_bounds j c M hc
  let T := max 1 M
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨j.factorial * C * T ^ j, by positivity, ?_⟩
  intro D _ _ O S hO hSO a b ha hb ell hell hreserve hab hbb k hk x hx
  let f : D → ℝ × ℝ := fun y ↦ (a y, b y)
  let U := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  let P := O ∩ f ⁻¹' U
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_Ioi
  have hf : ContDiffOn ℝ ∞ f O := ha.prodMk hb
  have hP : IsOpen P := hf.continuousOn.isOpen_inter_preimage hO hU
  have hxP : x ∈ P := ⟨hSO hx, hc.trans_le (hreserve x hx).1,
    hc.trans_le (hreserve x hx).2⟩
  have haM : a x ≤ M := (le_abs_self _).trans (by simpa using hab 0 (by omega) x hx)
  have hbM : b x ≤ M := (le_abs_self _).trans (by simpa using hbb 0 (by omega) x hx)
  have hfb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ T := by
    intro i hi
    rw [iteratedFDeriv_prodMk (ha.contDiffAt (hO.mem_nhds (hSO hx)))
      (hb.contDiffAt (hO.mem_nhds (hSO hx))) (by simp : (i : WithTop ℕ∞) ≤ ∞),
      ContinuousMultilinearMap.opNorm_prod, mul_max_of_nonneg _ _ (by positivity : 0 ≤ ell ^ i)]
    exact max_le ((hab i (hi.trans hk) x hx).trans (le_max_right _ _))
      ((hbb i (hi.trans hk) x hx).trans (le_max_right _ _))
  have hbound := operation_scaled_composition incrementsSqrtDifferenceFactor f U P hU hP
    incrementsSqrtDifferenceFactor_contDiffOn (hf.mono inter_subset_left)
    (fun _ hy ↦ hy.2) k ell T C hell hT hxP
    (fun i hi ↦ hCb i (hi.trans hk) _
      ⟨⟨(hreserve x hx).1, haM⟩, ⟨(hreserve x hx).2, hbM⟩⟩) hfb
  apply hbound.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hC)
    (pow_le_pow_right₀ hT hk) (by positivity) (by positivity)

/-- Native all-order product estimate for the EXACT square-root input difference.
Every summand retains a derivative of a-b; the second factor is the actual smooth
positive-reserve divided difference, whose jets were bounded above. -/
theorem increments_sqrt_difference_jet_le
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (O : Set D) (hO : IsOpen O) (a b : D → ℝ)
    (ha : ContDiffOn ℝ ∞ a O) (hb : ContDiffOn ℝ ∞ b O)
    (k : ℕ) {x : D} (hx : x ∈ O) (hax : 0 < a x) (hbx : 0 < b x) :
    ‖iteratedFDeriv ℝ k (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y ↦ a y - b y) x‖ *
        ‖iteratedFDeriv ℝ (k - i)
          (fun y ↦ incrementsSqrtDifferenceFactor (a y, b y)) x‖ := by
  let f : D → ℝ × ℝ := fun y ↦ (a y, b y)
  let P := O ∩ f ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  have hP : IsOpen P := (ha.prodMk hb).continuousOn.isOpen_inter_preimage hO
    (isOpen_Ioi.prod isOpen_Ioi)
  have hxP : x ∈ P := ⟨hx, hax, hbx⟩
  have hfactor : ContDiffOn ℝ ∞
      (fun y ↦ incrementsSqrtDifferenceFactor (a y, b y)) P :=
    incrementsSqrtDifferenceFactor_contDiffOn.comp
      ((ha.prodMk hb).mono inter_subset_left) (fun _ hy ↦ hy.2)
  have heq : (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) =ᶠ[𝓝 x]
      (fun y ↦ (a y - b y) * incrementsSqrtDifferenceFactor (a y, b y)) :=
    Filter.eventually_of_mem (hP.mem_nhds hxP) (fun _ hy ↦
      incrementsSqrtDifferenceFactor_identity hy.2.1 hy.2.2)
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  have h := norm_iteratedFDerivWithin_mul_le (s := P) ((ha.sub hb).mono inter_subset_left)
    hfactor hP.uniqueDiffOn hxP (n := k) (by simp)
  have hder (i : ℕ) (g : D → ℝ) :
      iteratedFDerivWithin ℝ i g P x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_of_isOpen i hP hxP
  simp only [hder] at h
  exact h

private theorem scalar_clm_scaled_jet
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : Set D) (hO : IsOpen O) (f : D → ℝ) (hf : ContDiffOn ℝ ∞ f O)
    (k : ℕ) (ell M : ℝ) (hell : 0 ≤ ell) {x : D} (hx : x ∈ O)
    (hfb : ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ M) :
    ell ^ k * ‖iteratedFDeriv ℝ k
      (fun y ↦ (ContinuousLinearMap.lsmul ℝ ℝ (f y) : F →L[ℝ] F)) x‖ ≤ M := by
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have he := L.iteratedFDeriv_comp_left (hf.contDiffAt (hO.mem_nhds hx))
    (i := k) (by simp)
  change ell ^ k * ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ M
  rw [he]
  calc
    _ ≤ ell ^ k * (‖L‖ * ‖iteratedFDeriv ℝ k f x‖) :=
      mul_le_mul_of_nonneg_left (L.norm_compContinuousMultilinearMap_le _) (by positivity)
    _ ≤ ell ^ k * (1 * ‖iteratedFDeriv ℝ k f x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (norm_nonneg _))
        (by positivity)
    _ ≤ M := by simpa using hfb

/-- The actual original linear tensor coefficient has the native jet bound. In
particular a fixed decomposition functional needs only its given operator norm,
not a new collection of coefficient-field derivative assumptions. -/
theorem increments_fixed_linear_coefficient_scaled_jet
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (O : Set D) (hO : IsOpen O) (A : D → E)
    (hA : ContDiffOn ℝ ∞ A O) (k : ℕ) (ell M : ℝ) (hell : 0 ≤ ell)
    {x : D} (hx : x ∈ O) (hAb : ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ M) :
    ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ L (A y)) x‖ ≤ ‖L‖ * M := by
  have h := L.iteratedFDeriv_comp_left (hA.contDiffAt (hO.mem_nhds hx))
    (i := k) (by simp)
  change ell ^ k * ‖iteratedFDeriv ℝ k (L ∘ A) x‖ ≤ _
  rw [h]
  calc
    _ ≤ ell ^ k * (‖L‖ * ‖iteratedFDeriv ℝ k A x‖) :=
      mul_le_mul_of_nonneg_left (L.norm_compContinuousMultilinearMap_le _) (by positivity)
    _ = ‖L‖ * (ell ^ k * ‖iteratedFDeriv ℝ k A x‖) := by ring
    _ ≤ ‖L‖ * M := mul_le_mul_of_nonneg_left hAb (norm_nonneg _)

/-- Actual positive-reserve amplitude smoothness at each relevant point. The source
may be the full source/parameter product; zero cutoffs and zero output spaces are
allowed. There is no desired amplitude or solution as an input. -/
theorem increments_positive_reserve_amplitude_contDiffAt
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : Set D) (hO : IsOpen O) (L : D → E →L[ℝ] ℝ) (A : D → E)
    (cutoff : D → ℝ) (normal : D → F)
    (hL : ContDiffOn ℝ ∞ L O) (hA : ContDiffOn ℝ ∞ A O)
    (hcutoff : ContDiffOn ℝ ∞ cutoff O) (hnormal : ContDiffOn ℝ ∞ normal O)
    {x : D} (hx : x ∈ O) (hreserve : 0 < L x (A x)) :
    ContDiffAt ℝ ∞ (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) x := by
  exact ((hcutoff.contDiffAt (hO.mem_nhds hx)).mul
    (((hL.clm_apply hA).contDiffAt (hO.mem_nhds hx)).sqrt hreserve.ne')).smul
    (hnormal.contDiffAt (hO.mem_nhds hx))

/-- Literal amplitude support is contained in the original cutoff support. This is
native support calculus, with no positivity or division of the cutoff. -/
theorem increments_positive_reserve_amplitude_support
    {D E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : D → E →L[ℝ] ℝ) (A : D → E) (cutoff : D → ℝ) (normal : D → F) :
    Function.support (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) ⊆
      Function.support cutoff :=
  (Function.support_smul_subset_left _ _).trans (Function.support_mul_subset_left _ _)

private theorem amplitude_scaled_smul
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : Set D) (hO : IsOpen O) (f : D → ℝ) (g : D → F)
    (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (k : ℕ) (ell M K : ℝ) (hell : 0 ≤ ell) {x : D} (hx : x ∈ O)
    (hfb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hgb : ∀ i ≤ k, ell ^ i * ‖iteratedFDeriv ℝ i g x‖ ≤ K) :
    ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ f y • g y) x‖ ≤ 2 ^ k * M * K := by
  have h := scaled_clm_apply O hO
    (fun y ↦ (ContinuousLinearMap.lsmul ℝ ℝ (f y) : F →L[ℝ] F)) g
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).contDiff.comp_contDiffOn hf)
    hg k 0 ell M K hell
    (fun i hi ↦ scalar_clm_scaled_jet O hO f hf i ell M hell hx (hfb i hi))
    (fun i hi ↦ by simpa using hgb i hi) hx
  simpa using h

/-- Original positive-reserve square roots retain the SAME input-difference bound
at every order. The constant uses only the observation order, reserve and original
input-size bound; no additional derivative loss or source compactness occurs. -/
theorem increments_sqrt_reserve_difference_scaled_jets (j : ℕ) (c M : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O) (a b : D → ℝ)
        (_ha : ContDiffOn ℝ ∞ a O) (_hb : ContDiffOn ℝ ∞ b O)
        (ell Delta : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S, c ≤ a x ∧ c ≤ b x)
        (_hab : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i a x‖ ≤ M)
        (_hbb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i b x‖ ≤ M)
        (_hdiff : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ a y - b y) x‖ ≤ Delta),
      ∀ k ≤ j, ∀ x ∈ S,
        ell ^ k * ‖iteratedFDeriv ℝ k
          (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) x‖ ≤ C * Delta := by
  obtain ⟨C, hC, hCb⟩ := increments_sqrt_difference_factor_scaled_jets j c M hc
  refine ⟨2 ^ j * C, by positivity, ?_⟩
  intro D _ _ O S hO hSO a b ha hb ell Delta hell hDelta hreserve hab hbb hdiff k hk x hx
  let f : D → ℝ × ℝ := fun y ↦ (a y, b y)
  let P := O ∩ f ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  have hP : IsOpen P := (ha.prodMk hb).continuousOn.isOpen_inter_preimage hO
    (isOpen_Ioi.prod isOpen_Ioi)
  have hxP : x ∈ P := ⟨hSO hx, hc.trans_le (hreserve x hx).1,
    hc.trans_le (hreserve x hx).2⟩
  have hfactor : ContDiffOn ℝ ∞
      (fun y ↦ incrementsSqrtDifferenceFactor (a y, b y)) P :=
    incrementsSqrtDifferenceFactor_contDiffOn.comp
      ((ha.prodMk hb).mono inter_subset_left) (fun _ hy ↦ hy.2)
  have heq : (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) =ᶠ[𝓝 x]
      (fun y ↦ (a y - b y) * incrementsSqrtDifferenceFactor (a y, b y)) :=
    Filter.eventually_of_mem (hP.mem_nhds hxP) (fun _ hy ↦
      incrementsSqrtDifferenceFactor_identity hy.2.1 hy.2.2)
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  have hprod := amplitude_scaled_smul P hP (fun y ↦ a y - b y)
    (fun y ↦ incrementsSqrtDifferenceFactor (a y, b y))
    ((ha.sub hb).mono inter_subset_left) hfactor k ell Delta C hell.le hxP
    (fun i hi ↦ hdiff i (hi.trans hk) x hx)
    (fun i hi ↦ hCb O S hO hSO a b ha hb ell hell hreserve hab hbb i (hi.trans hk) x hx)
  change ell ^ k * ‖iteratedFDeriv ℝ k
    (fun y ↦ (a y - b y) • incrementsSqrtDifferenceFactor (a y, b y)) x‖ ≤ _
  apply hprod.trans
  have hp : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hk
  calc
    _ = (2 ^ k * C) * Delta := by ring
    _ ≤ (2 ^ j * C) * Delta :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hC) hDelta

/-- Actual coefficient-field/cutoff/normal amplitude SIZE from ORIGINAL input jets.
The linear tensor coefficient is evaluated internally; no amplitude estimate,
desired mean/remainder bound, cutoff positivity or source compactness is an input. -/
theorem increments_positive_reserve_amplitude_scaled_jets
    (j : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → E →L[ℝ] ℝ) (A : D → E) (cutoff : D → ℝ) (normal : D → F)
        (_hL : ContDiffOn ℝ ∞ L O) (_hA : ContDiffOn ℝ ∞ A O)
        (_hcutoff : ContDiffOn ℝ ∞ cutoff O) (_hnormal : ContDiffOn ℝ ∞ normal O)
        (ell : ℝ) (_hell : 0 < ell) (_hreserve : ∀ x ∈ S, c ≤ L x (A x))
        (_hLb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M)
        (_hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
        (_hcutoffb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ M)
        (_hnormalb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ M),
      ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) x‖ ≤ C := by
  let T : ℝ := 2 ^ j * M * M
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C, hC, hCb⟩ := increments_sqrt_reserve_scaled_jets j c T hc
  refine ⟨2 ^ j * C * T, by positivity, ?_⟩
  intro D E F _ _ _ _ _ _ O S hO hSO L A cutoff normal hL hA hcutoff hnormal
    ell hell hreserve hLb hAb hcutoffb hnormalb k hk x hx
  let a : D → ℝ := fun y ↦ L y (A y)
  let N : D → F := fun y ↦ cutoff y • normal y
  have ha : ContDiffOn ℝ ∞ a O := hL.clm_apply hA
  have hN : ContDiffOn ℝ ∞ N O := hcutoff.smul hnormal
  have hab : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i a z‖ ≤ T := by
    intro i hi z hz
    have hb := scaled_clm_apply O hO L A hL hA i 0 ell M M hell.le
      (fun r hr ↦ hLb r (hr.trans hi) z hz)
      (fun r hr ↦ by simpa using hAb r (hr.trans hi) z hz) (hSO hz)
    calc
      _ ≤ 2 ^ i * M * M := by simpa using hb
      _ ≤ T := by dsimp [T]; gcongr; norm_num
  have hNb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i N z‖ ≤ T := by
    intro i hi z hz
    calc
      _ ≤ 2 ^ i * M * M := amplitude_scaled_smul O hO cutoff normal hcutoff hnormal
        i ell M M hell.le (hSO hz) (fun r hr ↦ hcutoffb r (hr.trans hi) z hz)
          (fun r hr ↦ hnormalb r (hr.trans hi) z hz)
      _ ≤ T := by dsimp [T]; gcongr; norm_num
  let P := O ∩ a ⁻¹' Ioi 0
  have hP : IsOpen P := ha.continuousOn.isOpen_inter_preimage hO isOpen_Ioi
  have hxP : x ∈ P := ⟨hSO hx, hc.trans_le (hreserve x hx)⟩
  have hsqrt : ContDiffOn ℝ ∞ (fun y ↦ Real.sqrt (a y)) P :=
    (ha.mono inter_subset_left).sqrt (fun _ hy ↦ hy.2.ne')
  have hb := amplitude_scaled_smul P hP (fun y ↦ Real.sqrt (a y)) N
    hsqrt (hN.mono inter_subset_left) k ell C T hell.le hxP
    (fun i hi ↦ hCb O S hO hSO a ha ell hell hreserve hab i (hi.trans hk) x hx)
    (fun i hi ↦ hNb i (hi.trans hk) x hx)
  have heq : (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y) =
      (fun y ↦ Real.sqrt (a y) • N y) := by
    funext y
    simp only [N, a, smul_smul, mul_comm]
  rw [heq]
  apply hb.trans
  gcongr; norm_num

/-- SAME-input-difference bound for the literal original amplitude, derived from
actual tensor input differences by the SAME linear coefficient field. Geometry,
cutoff and normal are fixed. No cutoff division or desired output bound is assumed. -/
theorem increments_positive_reserve_amplitude_difference_scaled_jets
    (j : ℕ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
        [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        (O S : Set D) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : D → E →L[ℝ] ℝ) (A B : D → E) (cutoff : D → ℝ) (normal : D → F)
        (_hL : ContDiffOn ℝ ∞ L O) (_hA : ContDiffOn ℝ ∞ A O)
        (_hB : ContDiffOn ℝ ∞ B O) (_hcutoff : ContDiffOn ℝ ∞ cutoff O)
        (_hnormal : ContDiffOn ℝ ∞ normal O)
        (ell Delta : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S, c ≤ L x (A x) ∧ c ≤ L x (B x))
        (_hLb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M)
        (_hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
        (_hBb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
        (_hcutoffb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ M)
        (_hnormalb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ M)
        (_hdiff : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ A y - B y) x‖ ≤ Delta),
      ∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y -
          (cutoff y * Real.sqrt (L y (B y))) • normal y) x‖ ≤ C * Delta := by
  let T : ℝ := 2 ^ j * M * M
  let V : ℝ := 2 ^ j * M
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨C, hC, hCb⟩ := increments_sqrt_reserve_difference_scaled_jets j c T hc
  refine ⟨2 ^ j * C * V * T, by positivity, ?_⟩
  intro D E F _ _ _ _ _ _ O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
    ell Delta hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hdiff k hk x hx
  let a : D → ℝ := fun y ↦ L y (A y)
  let b : D → ℝ := fun y ↦ L y (B y)
  let N : D → F := fun y ↦ cutoff y • normal y
  have ha : ContDiffOn ℝ ∞ a O := hL.clm_apply hA
  have hb : ContDiffOn ℝ ∞ b O := hL.clm_apply hB
  have hN : ContDiffOn ℝ ∞ N O := hcutoff.smul hnormal
  have hab : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i a z‖ ≤ T := by
    intro i hi z hz
    have h := scaled_clm_apply O hO L A hL hA i 0 ell M M hell.le
      (fun r hr ↦ hLb r (hr.trans hi) z hz)
      (fun r hr ↦ by simpa using hAb r (hr.trans hi) z hz) (hSO hz)
    calc
      _ ≤ 2 ^ i * M * M := by simpa using h
      _ ≤ T := by dsimp [T]; gcongr; norm_num
  have hbb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i b z‖ ≤ T := by
    intro i hi z hz
    have h := scaled_clm_apply O hO L B hL hB i 0 ell M M hell.le
      (fun r hr ↦ hLb r (hr.trans hi) z hz)
      (fun r hr ↦ by simpa using hBb r (hr.trans hi) z hz) (hSO hz)
    calc
      _ ≤ 2 ^ i * M * M := by simpa using h
      _ ≤ T := by dsimp [T]; gcongr; norm_num
  have hdiffab : ∀ i ≤ j, ∀ z ∈ S,
      ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ a y - b y) z‖ ≤ V * Delta := by
    intro i hi z hz
    have heq : (fun y ↦ a y - b y) = (fun y ↦ L y (A y - B y)) :=
      funext fun y ↦ (map_sub (L y) (A y) (B y)).symm
    rw [heq]
    have h := scaled_clm_apply O hO L (fun y ↦ A y - B y) hL (hA.sub hB)
      i 0 ell M Delta hell.le (fun r hr ↦ hLb r (hr.trans hi) z hz)
      (fun r hr ↦ by simpa using hdiff r (hr.trans hi) z hz) (hSO hz)
    calc
      _ ≤ 2 ^ i * M * Delta := by simpa using h
      _ ≤ V * Delta := by dsimp [V]; gcongr; norm_num
  have hNb : ∀ i ≤ j, ∀ z ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i N z‖ ≤ T := by
    intro i hi z hz
    calc
      _ ≤ 2 ^ i * M * M := amplitude_scaled_smul O hO cutoff normal hcutoff hnormal
        i ell M M hell.le (hSO hz) (fun r hr ↦ hcutoffb r (hr.trans hi) z hz)
          (fun r hr ↦ hnormalb r (hr.trans hi) z hz)
      _ ≤ T := by dsimp [T]; gcongr; norm_num
  let P := O ∩ (fun y ↦ (a y, b y)) ⁻¹' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
  have hP : IsOpen P := (ha.prodMk hb).continuousOn.isOpen_inter_preimage hO
    (isOpen_Ioi.prod isOpen_Ioi)
  have hxP : x ∈ P := ⟨hSO hx, hc.trans_le (hreserve x hx).1,
    hc.trans_le (hreserve x hx).2⟩
  have hrootdiff : ContDiffOn ℝ ∞ (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) P :=
    ((ha.mono inter_subset_left).sqrt (fun _ hy ↦ hy.2.1.ne')).sub
      ((hb.mono inter_subset_left).sqrt (fun _ hy ↦ hy.2.2.ne'))
  have hprod := amplitude_scaled_smul P hP
    (fun y ↦ Real.sqrt (a y) - Real.sqrt (b y)) N hrootdiff (hN.mono inter_subset_left)
    k ell (C * (V * Delta)) T hell.le hxP
    (fun i hi ↦ hCb O S hO hSO a b ha hb ell (V * Delta) hell (by positivity)
      hreserve hab hbb hdiffab i (hi.trans hk) x hx)
    (fun i hi ↦ hNb i (hi.trans hk) x hx)
  have heq : (fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y -
      (cutoff y * Real.sqrt (L y (B y))) • normal y) =
      (fun y ↦ (Real.sqrt (a y) - Real.sqrt (b y)) • N y) := by
    funext y
    dsimp only [N, a, b]
    rw [sub_smul, smul_smul, smul_smul]
    simp only [mul_comm]
  rw [heq]
  apply hprod.trans
  calc
    _ = (2 ^ k * C * V * T) * Delta := by ring
    _ ≤ (2 ^ j * C * V * T) * Delta := by gcongr; norm_num

private theorem amplitude_const_scaled_jet
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : D → F) (k : ℕ) (ell K s : ℝ) (_hell : 0 ≤ ell) {x : D}
    (hf : ContDiffAt ℝ ∞ f x)
    (hb : ell ^ k * ‖iteratedFDeriv ℝ k f x‖ ≤ K) :
    ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ s • f y) x‖ ≤ |s| * K := by
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)), norm_smul, Real.norm_eq_abs]
  calc
    _ = |s| * (ell ^ k * ‖iteratedFDeriv ℝ k f x‖) := by ring
    _ ≤ |s| * K := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- The SAME canonical original free amplitude has actual uniform size and
same-input-difference jets. Constants are chosen BEFORE delta, tau, scale, fields,
or the input-difference size. All inputs are ORIGINAL coefficient/cutoff/normal
and tensor jet bounds plus positive argument reserve. No reconstructed error or
mean estimate is supplied. Zero dimensions and delta=0 or tau=0 are included. -/
theorem increments_primary_free_amplitude_scaled_bounds
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
        (ell Delta delta tau : ℝ) (_hell : 0 < ell) (_hDelta : 0 ≤ Delta)
        (_hreserve : ∀ x ∈ S, c ≤ L x (A x) ∧ c ≤ L x (B x))
        (_hLb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ M)
        (_hAb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i A x‖ ≤ M)
        (_hBb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i B x‖ ≤ M)
        (_hcutoffb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ M)
        (_hnormalb : ∀ i ≤ j, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i normal x‖ ≤ M)
        (_hdiff : ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ A y - B y) x‖ ≤ Delta),
      let vA := incrementsPrimaryFreeAmplitude delta tau
        (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal
      let vB := incrementsPrimaryFreeAmplitude delta tau
        (fun y ↦ cutoff y * Real.sqrt (L y (B y))) normal
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k vA x‖ ≤ C * |delta| * |tau|) ∧
      (∀ k ≤ j, ∀ x ∈ S, ell ^ k * ‖iteratedFDeriv ℝ k
        (fun y ↦ vA y - vB y) x‖ ≤ C * |delta| * |tau| * Delta) := by
  obtain ⟨Cs, hCs, hsize⟩ := increments_positive_reserve_amplitude_scaled_jets j c M hc hM
  obtain ⟨Cd, hCd, hdiff⟩ :=
    increments_positive_reserve_amplitude_difference_scaled_jets j c M hc hM
  refine ⟨max Cs Cd * Real.sqrt 2, by positivity, ?_⟩
  intro n N E _ _ O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
    ell Delta delta tau hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hAB
  let fA := fun y ↦ (cutoff y * Real.sqrt (L y (A y))) • normal y
  let fB := fun y ↦ (cutoff y * Real.sqrt (L y (B y))) • normal y
  let s := Real.sqrt 2 * delta * tau
  have hsabs : |s| = Real.sqrt 2 * |delta| * |tau| := by
    dsimp [s]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hfa : ∀ x ∈ S, ContDiffAt ℝ ∞ fA x := fun x hx ↦
    increments_positive_reserve_amplitude_contDiffAt O hO L A cutoff normal
      hL hA hcutoff hnormal (hSO hx) (hc.trans_le (hreserve x hx).1)
  have hfb : ∀ x ∈ S, ContDiffAt ℝ ∞ fB x := fun x hx ↦
    increments_positive_reserve_amplitude_contDiffAt O hO L B cutoff normal
      hL hB hcutoff hnormal (hSO hx) (hc.trans_le (hreserve x hx).2)
  have hvA : incrementsPrimaryFreeAmplitude delta tau
      (fun y ↦ cutoff y * Real.sqrt (L y (A y))) normal = (fun y ↦ s • fA y) := by
    funext y
    simp only [incrementsPrimaryFreeAmplitude, s, fA, smul_smul]
  have hvB : incrementsPrimaryFreeAmplitude delta tau
      (fun y ↦ cutoff y * Real.sqrt (L y (B y))) normal = (fun y ↦ s • fB y) := by
    funext y
    simp only [incrementsPrimaryFreeAmplitude, s, fB, smul_smul]
  dsimp only
  rw [hvA, hvB]
  constructor
  · intro k hk x hx
    have hb := amplitude_const_scaled_jet fA k ell Cs s hell.le (hfa x hx)
      (hsize O S hO hSO L A cutoff normal hL hA hcutoff hnormal ell hell
        (fun z hz ↦ (hreserve z hz).1) hLb hAb hcutoffb hnormalb k hk x hx)
    calc
      _ ≤ |s| * Cs := hb
      _ = (Cs * Real.sqrt 2) * |delta| * |tau| := by rw [hsabs]; ring
      _ ≤ (max Cs Cd * Real.sqrt 2) * |delta| * |tau| := by gcongr; exact le_max_left _ _
  · intro k hk x hx
    have heq : (fun y ↦ s • fA y - s • fB y) = (fun y ↦ s • (fA y - fB y)) :=
      funext fun _ ↦ (smul_sub _ _ _).symm
    rw [heq]
    have hb := amplitude_const_scaled_jet (fun y ↦ fA y - fB y) k ell (Cd * Delta) s
      hell.le ((hfa x hx).sub (hfb x hx))
      (hdiff O S hO hSO L A B cutoff normal hL hA hB hcutoff hnormal
        ell Delta hell hDelta hreserve hLb hAb hBb hcutoffb hnormalb hAB k hk x hx)
    calc
      _ ≤ |s| * (Cd * Delta) := hb
      _ = (Cd * Real.sqrt 2) * |delta| * |tau| * Delta := by rw [hsabs]; ring
      _ ≤ (max Cs Cd * Real.sqrt 2) * |delta| * |tau| * Delta := by
        gcongr
        exact le_max_right _ _

#print axioms incrementsSqrtDifferenceFactor
#print axioms incrementsSqrtDifferenceFactor_contDiffOn
#print axioms incrementsSqrtDifferenceFactor_identity
#print axioms increments_sqrt_reserve_operation_bounds
#print axioms increments_sqrt_difference_operation_bounds
#print axioms increments_sqrt_reserve_scaled_jets
#print axioms increments_sqrt_difference_factor_scaled_jets
#print axioms increments_sqrt_difference_jet_le
#print axioms increments_fixed_linear_coefficient_scaled_jet
#print axioms increments_positive_reserve_amplitude_contDiffAt
#print axioms increments_positive_reserve_amplitude_support
#print axioms increments_sqrt_reserve_difference_scaled_jets
#print axioms increments_positive_reserve_amplitude_scaled_jets
#print axioms increments_positive_reserve_amplitude_difference_scaled_jets
#print axioms increments_primary_free_amplitude_scaled_bounds

end GlobalEmbedding.Paper
