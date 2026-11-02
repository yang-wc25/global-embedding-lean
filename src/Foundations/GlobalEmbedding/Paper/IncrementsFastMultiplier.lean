import GlobalEmbedding.Paper.IncrementsFastMultiplierProduct
import GlobalEmbedding.Paper.IncrementsFastPhaseJet
import GlobalEmbedding.Paper.IncrementsWeightedFirstOrder
import GlobalEmbedding.Paper.PaperCoordinateNormBridge

/-!
# The actual fast multiplier in the original cumulative weighted norms

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:increments`,
lines 669–675. Reuse the actual phase theorem and the sole native product estimate.
Only positive-order slow phase jets enter. Differentiation remains on the original
open domain, separately from the SUP domain; every source/parameter coordinate remains.
-/

noncomputable section
open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- One finite constant for the actual fast multiplier, independent of both scales and
of the phase value. Source: the finite Leibniz sum in `lem:increments`. -/
def incrementsFastMultiplierConstant (j : ℕ) (M : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (n + 1),
    (n.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a)

/-- The genuine multiplier constant is positive, including j=0 and negative M.
Source: `lem:increments`, no bound on the phase value at order zero. -/
theorem incrementsFastMultiplierConstant_pos (j : ℕ) (M : ℝ) :
    0 < incrementsFastMultiplierConstant j M := by
  unfold incrementsFastMultiplierConstant
  positivity

/-- The same constant bounds the coefficient sum at EVERY required derivative order.
Source: the original finite weighted multiplier estimate. -/
theorem incrementsFastMultiplierConstant_controls (j n : ℕ) (M : ℝ) (hn : n ≤ j) :
    (∑ a ∈ Finset.range (n + 1),
      (n.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a)) ≤
        incrementsFastMultiplierConstant j M := by
  have h : (∑ a ∈ Finset.range (n + 1),
      (n.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a)) ≤
      ∑ b ∈ Finset.range (j + 1), ∑ a ∈ Finset.range (b + 1),
        (b.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a) := by
    apply Finset.single_le_sum (a := n)
      (f := fun b : ℕ ↦ ∑ a ∈ Finset.range (b + 1),
        (b.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a))
    · intro b hb
      exact Finset.sum_nonneg (fun a ha ↦ by positivity)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

/-- The literal original fast phase is smooth on the original open domain.
Source: `lem:increments`, genuine local smooth phase, without global extension. -/
theorem increments_fast_phase_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set E) (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ O) (τ : ℝ) :
    ContDiffOn ℝ ∞
      (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ))) O := by
  have hdiv : ContDiffOn ℝ ∞ (fun y ↦ ψ y / τ) O := hψ.div_const τ
  have hreal : ContDiffOn ℝ ∞ (fun y ↦ ((ψ y / τ : ℝ) : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hdiv
  exact (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).comp_contDiffOn
    (contDiffOn_const.mul hreal)

/-- Actual scaled jets of the literal multiplier. The accepted phase theorem internally
supplies every phase bound, while K is an honest bound on the actual scaled source jets.
Source: `lem:increments`, the original nonzero-mode multiplier estimate. -/
theorem increments_fast_multiplier_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (z : E → F)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (x : E) (hx : x ∈ O) (τ ℓ M K : ℝ)
    (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1) (hK : 0 ≤ K)
    (hjet : ∀ k < j, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hzjet : ∀ b ≤ j, ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n
      (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) x‖ ≤
        incrementsFastMultiplierConstant j M * K := by
  have hp := increments_fast_phase_jet_bound O hO ψ hψ x hx j τ ℓ M hτ hτℓ hℓ hjet
  have hw := increments_fast_phase_contDiffOn O ψ hψ τ
  apply (increments_fast_smul_jet_bound O hO _ z hw hz x hx j n hn τ ℓ hτ hτℓ
    (fun a ↦ (a.factorial : ℝ) * (max 1 |M|) ^ a) hp).trans
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1),
        ((n.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a)) * K := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ n := by simpa using ha
      have h := hzjet (n - a) ((Nat.sub_le n a).trans hn)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h
        (by positivity : 0 ≤ (n.choose a : ℝ) *
          ((a.factorial : ℝ) * (max 1 |M|) ^ a))
    _ = (∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * ((a.factorial : ℝ) * (max 1 |M|) ^ a)) * K := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (incrementsFastMultiplierConstant_controls j n M hn) hK

/-- The ACTUAL fast multiplier under fixed native coordinate equivalences retains both
true operator norms. In particular the PiSUP/EuclideanL2 changes are not called isometries.
This is a direct consumer of the accepted paper coordinate-change jet theorem.
Source: `lem:increments`, full source/parameter coordinate norm comparison. -/
theorem increments_fast_multiplier_coordinate_jet_bound
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : X ≃L[ℝ] E) (b : F ≃L[ℝ] G)
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (z : E → F)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (x : X) (hx : a x ∈ O) (τ ℓ M K : ℝ)
    (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1) (hK : 0 ≤ K)
    (hjet : ∀ k < j, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ (a x)‖ ≤ M)
    (hzjet : ∀ r ≤ j, ℓ ^ r * ‖iteratedFDeriv ℝ r z (a x)‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n
      (b ∘ (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) ∘ a) x‖ ≤
        (‖b.toContinuousLinearMap‖ * ‖a.toContinuousLinearMap‖ ^ n) *
          (incrementsFastMultiplierConstant j M * K) := by
  have hc := paper_coordinate_change_jet_bound a b
    (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) x n
  have hm := increments_fast_multiplier_jet_bound j n hn O hO ψ z hψ hz
    (a x) hx τ ℓ M K hτ hτℓ hℓ hK hjet hzjet
  calc
    _ ≤ τ ^ n * (‖b.toContinuousLinearMap‖ *
        ‖iteratedFDeriv ℝ n
          (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) (a x)‖ *
          ‖a.toContinuousLinearMap‖ ^ n) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hτ.le n)
    _ = (‖b.toContinuousLinearMap‖ * ‖a.toContinuousLinearMap‖ ^ n) *
        (τ ^ n * ‖iteratedFDeriv ℝ n
          (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) (a x)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm
      (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) n))

/-- The actual phase and actual complex-module field obey the complete weighted exact-order
jet sum estimate. No supplied desired phase bound is present in this conclusion's inputs.
Source: `lem:increments`, the original multiplier before cumulative SUP norms. -/
theorem increments_fast_multiplier_weighted_sum_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (j : ℕ) (O : Set E) (hO : IsOpen O) (ψ : E → ℝ) (z : E → F)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (x : E) (hx : x ∈ O) (τ ℓ M : ℝ)
    (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1)
    (hjet : ∀ k < j, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M) :
    (∑ n ∈ Finset.range (j + 1), τ ^ n * ‖iteratedFDeriv ℝ n
      (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) x‖) ≤
      incrementsFastMultiplierConstant j M *
        ∑ b ∈ Finset.range (j + 1), ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖ := by
  have hp := increments_fast_phase_jet_bound O hO ψ hψ x hx j τ ℓ M hτ hτℓ hℓ hjet
  have hw := increments_fast_phase_contDiffOn O ψ hψ τ
  apply (increments_fast_smul_weighted_sum_bound O hO _ z hw hz x hx j τ ℓ hτ hτℓ
    (fun a ↦ (a.factorial : ℝ) * (max 1 |M|) ^ a) hp).trans
  apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
  exact Finset.sum_nonneg (fun b hb ↦ mul_nonneg
    (pow_nonneg (hτ.le.trans hτℓ) b) (norm_nonneg _))

/-- Real part of the ACTUAL multiplier has the same scaled bound. Native real-part
postcomposition is used with its actual Pi norm, including empty target coordinates.
Source: `lem:increments`, actual real displacement from a complex mode. -/
theorem increments_fast_multiplier_real_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (z : E → Fin N → ℂ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (x : E) (hx : x ∈ O) (τ ℓ M K : ℝ)
    (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1) (hK : 0 ≤ K)
    (hjet : ∀ k < j, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hzjet : ∀ b ≤ j, ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n
      (fun y i ↦ (Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) * z y i).re) x‖ ≤
        incrementsFastMultiplierConstant j M * K := by
  have hw := increments_fast_phase_contDiffOn O ψ hψ τ
  have hr := incrementsCoordinateRealPart_jet_bound N n O hO _ (hw.smul hz) x hx
  exact (mul_le_mul_of_nonneg_left hr (pow_nonneg hτ.le n)).trans
    (increments_fast_multiplier_jet_bound j n hn O hO ψ z hψ hz x hx τ ℓ M K
      hτ hτℓ hℓ hK hjet hzjet)

/-- The actual literal complex multiplier obeys the ORIGINAL cumulative weighted finite-Cj
estimate. Source boundedness is honest conditional-supremum boundedness; output boundedness
is derived. The accepted phase estimate is discharged internally, not assumed.
Source: `lem:increments`, cumulative weighted nonzero modes. -/
theorem increments_fast_multiplier_weighted_finiteCj
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (j : ℕ) (O S : Set E) (hO : IsOpen O) (hSO : S ⊆ O)
    (ψ : E → ℝ) (z : E → F)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (τ ℓ M : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1)
    (hjet : ∀ k < j, ∀ x ∈ S, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hfinite : ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k z x‖)) :
    let f := fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y
    (∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖)) ∧
      (∑ a ∈ Finset.range (j + 1), τ ^ a * finiteCjNorm a f S) ≤
        (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) *
          incrementsFastMultiplierConstant j M *
            ∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a z S := by
  let K := ∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a z S
  have hp := scaled_finiteCj_points j z S ℓ (hτ.le.trans hτℓ) hfinite
  have hout := scaled_finiteCj_sum_le j
    (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) • z y) S τ
    (incrementsFastMultiplierConstant j M * K) hτ (hτℓ.trans hℓ)
    (mul_nonneg (incrementsFastMultiplierConstant_pos j M).le hp.1)
    (fun k hk x hx ↦ increments_fast_multiplier_jet_bound j k hk O hO ψ z hψ hz x
      (hSO hx) τ ℓ M K hτ hτℓ hℓ hp.1
      (fun a ha ↦ hjet a ha x hx) (fun b hb ↦ hp.2 b hb x hx))
  exact ⟨hout.1, hout.2.trans_eq (by dsimp [K]; ring)⟩

/-- Actual real output has the same ORIGINAL cumulative weighted finite-Cj estimate.
All orders share the SAME functions and scales. Source: `lem:increments`, real multiplier. -/
theorem increments_fast_multiplier_real_weighted_finiteCj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N j : ℕ) (O S : Set E) (hO : IsOpen O) (hSO : S ⊆ O)
    (ψ : E → ℝ) (z : E → Fin N → ℂ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hz : ContDiffOn ℝ ∞ z O)
    (τ ℓ M : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1)
    (hjet : ∀ k < j, ∀ x ∈ S, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hfinite : ∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k z x‖)) :
    let f := fun y i ↦ (Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) * z y i).re
    (∀ k ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖)) ∧
      (∑ a ∈ Finset.range (j + 1), τ ^ a * finiteCjNorm a f S) ≤
        (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) *
          incrementsFastMultiplierConstant j M *
            ∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a z S := by
  let K := ∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a z S
  have hp := scaled_finiteCj_points j z S ℓ (hτ.le.trans hτℓ) hfinite
  have hout := scaled_finiteCj_sum_le j
    (fun y i ↦ (Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) * z y i).re) S τ
    (incrementsFastMultiplierConstant j M * K) hτ (hτℓ.trans hℓ)
    (mul_nonneg (incrementsFastMultiplierConstant_pos j M).le hp.1)
    (fun k hk x hx ↦ increments_fast_multiplier_real_jet_bound N j k hk O hO ψ z hψ hz x
      (hSO hx) τ ℓ M K hτ hτℓ hℓ hp.1
      (fun a ha ↦ hjet a ha x hx) (fun b hb ↦ hp.2 b hb x hx))
  exact ⟨hout.1, hout.2.trans_eq (by dsimp [K]; ring)⟩

/-- The actual native componentwise embedding used by the existing complex modes.
Source: `lem:increments`, real and imaginary coefficient fields, with their original Pi norms. -/
def incrementsCoordinateComplex (N : ℕ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

/-- Native component complexification has norm at most one, including the empty target.
Source: the actual original real/complex coordinate comparison in `lem:increments`. -/
theorem incrementsCoordinateComplex_norm_le (N : ℕ) :
    ‖incrementsCoordinateComplex N‖ ≤ 1 := by
  apply (incrementsCoordinateComplex N).opNorm_le_bound zero_le_one
  intro z
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  change ‖(z i : ℂ)‖ ≤ ‖z‖
  rw [Complex.norm_real]
  exact norm_le_pi_norm z i

/-- The literal complex coefficient from its two original real fields is smooth.
Source: `lem:increments`, actual real and imaginary coefficient fields. -/
theorem increments_coordinate_complex_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (O : Set E) (P Q : E → Fin N → ℝ)
    (hP : ContDiffOn ℝ ∞ P O) (hQ : ContDiffOn ℝ ∞ Q O) :
    ContDiffOn ℝ ∞ (fun y i ↦ (P y i : ℂ) + Complex.I * (Q y i : ℂ)) O := by
  let C := incrementsCoordinateComplex N
  let L : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) := Complex.I • C
  have h := (C.contDiff.comp_contDiffOn hP).add (L.contDiff.comp_contDiffOn hQ)
  have heq : (fun y ↦ C (P y) + L (Q y)) =
      (fun y i ↦ (P y i : ℂ) + Complex.I * (Q y i : ℂ)) := by
    funext y i
    rfl
  change ContDiffOn ℝ ∞ (fun y ↦ C (P y) + L (Q y)) O at h
  rw [heq] at h
  exact h

/-- The actual mode z=P+iQ has its true real jet bounded by the sum of the original P,Q
jets. This only applies native linear postcomposition and addition, without a new norm.
Source: `lem:increments`, actual complex coefficient from its real and imaginary fields. -/
theorem increments_coordinate_complex_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N k : ℕ) (O : Set E) (hO : IsOpen O) (P Q : E → Fin N → ℝ)
    (hP : ContDiffOn ℝ ∞ P O) (hQ : ContDiffOn ℝ ∞ Q O) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ k (fun y i ↦ (P y i : ℂ) + Complex.I * (Q y i : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ k P x‖ + ‖iteratedFDeriv ℝ k Q x‖ := by
  let C := incrementsCoordinateComplex N
  let L : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) := Complex.I • C
  let p := fun y ↦ C (P y)
  let q := fun y ↦ L (Q y)
  have hp : ContDiffOn ℝ ∞ p O := C.contDiff.comp_contDiffOn hP
  have hq : ContDiffOn ℝ ∞ q O := L.contDiff.comp_contDiffOn hQ
  have hC : ‖C‖ ≤ 1 := incrementsCoordinateComplex_norm_le N
  have hL : ‖L‖ ≤ 1 := by simpa only [L, norm_smul, Complex.norm_I, one_mul] using hC
  have hpj := C.norm_iteratedFDerivWithin_comp_left (hP x hx) hO.uniqueDiffOn hx
    (by simp : (k : ℕ∞ω) ≤ ∞)
  have hqj := L.norm_iteratedFDerivWithin_comp_left (hQ x hx) hO.uniqueDiffOn hx
    (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at hpj hqj
  have hs := fun_iteratedFDerivWithin_add_apply (𝕜 := ℝ) (i := k)
    ((hp.of_le (by simp)).contDiffWithinAt hx) ((hq.of_le (by simp)).contDiffWithinAt hx)
    hO.uniqueDiffOn hx
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at hs
  have hnorm : ‖iteratedFDeriv ℝ k (fun y ↦ p y + q y) x‖ ≤
      ‖iteratedFDeriv ℝ k P x‖ + ‖iteratedFDeriv ℝ k Q x‖ := by
    rw [hs]
    exact (norm_add_le _ _).trans (add_le_add
      (hpj.trans (mul_le_of_le_one_left (norm_nonneg _) hC))
      (hqj.trans (mul_le_of_le_one_left (norm_nonneg _) hL)))
  have heq : (fun y ↦ p y + q y) =
      (fun y i ↦ (P y i : ℂ) + Complex.I * (Q y i : ℂ)) := by
    funext y i
    rfl
  rw [heq] at hnorm
  exact hnorm

/-- The paper-norm constant keeps the actual source-dimension comparison factor and has
no atlas-cardinality or scale dependence. Source: `lem:increments`, original norm estimate. -/
def incrementsFastPaperMultiplierConstant (j n : ℕ) (M : ℝ) : ℝ :=
  1 + ((j + 1 : ℕ) : ℝ) * (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) *
    incrementsFastMultiplierConstant j M * (∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k)

/-- The literal paper multiplier constant is strictly positive for all dimensions/orders.
Source: `lem:increments`, uniformity including empty coordinate spaces. -/
theorem incrementsFastPaperMultiplierConstant_pos (j n : ℕ) (M : ℝ) :
    0 < incrementsFastPaperMultiplierConstant j n M := by
  have h := incrementsFastMultiplierConstant_pos j M
  unfold incrementsFastPaperMultiplierConstant
  positivity

/-- Reuse the accepted first-order paper proof's actual uniform weighted-profile argument.
This transports genuine cumulative finite-Cj bounds to the SAME original atlas MAX, with
no chart-count factor. Source: `lem:increments`, original finite weighted atlas. -/
private theorem increments_fast_paper_transport
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (j : ℕ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (f : ι → (Fin n → ℝ) → Fin q → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (τ R : ℝ) (hτ : 0 < τ) (hR : 0 ≤ R)
    (hbdd : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (f i) x‖))
    (hbound : ∀ i, (∑ a ∈ Finset.range (j + 1),
      τ ^ a * finiteCjNorm a (f i) (S i)) ≤ R) :
    paperAtlasWeighted 0 j τ f O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j τ f O S).toReal ≤ ((j + 1 : ℕ) : ℝ) * R := by
  have hgfinite := paperAtlasWeighted_ne_top 0 j τ f O S hO hSO hf
    (by simpa only [Nat.add_zero] using hbdd)
  have hprofile : ∀ a ≤ j, ∀ i, finiteCjNorm a (f i) (S i) ≤ R / τ ^ a := by
    intro a ha i
    apply (le_div_iff₀ (pow_pos hτ a)).2
    have hterm : τ ^ a * finiteCjNorm a (f i) (S i) ≤
        ∑ b ∈ Finset.range (j + 1), τ ^ b * finiteCjNorm b (f i) (S i) := by
      apply Finset.single_le_sum (f := fun b : ℕ ↦ τ ^ b * finiteCjNorm b (f i) (S i))
      · intro b hb
        apply mul_nonneg (pow_nonneg hτ.le b)
        exact (finiteCjNorm_specification b (f i) (S i)
          (fun k hk ↦ hbdd i k (hk.trans (by simpa using hb)))).1
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
    simpa only [mul_comm] using hterm.trans (hbound i)
  have hout := paperAtlasWeighted_le_of_finiteCjNorm_bound 0 j τ hτ
    f O S hO hSO hf (by simpa only [Nat.add_zero] using hbdd) (fun a ↦ R / τ ^ a)
    (fun a ha ↦ div_nonneg hR (pow_nonneg hτ.le a))
    (by simpa only [Nat.add_zero] using hprofile)
  have hsum : (∑ a ∈ Finset.range (j + 1), τ ^ a * (R / τ ^ a)) =
      ((j + 1 : ℕ) : ℝ) * R := by
    calc
      _ = ∑ _a ∈ Finset.range (j + 1), R := by
        apply Finset.sum_congr rfl
        intro a ha
        field_simp
      _ = _ := by simp
  exact ⟨hgfinite, hout.trans_eq hsum⟩

/-- The ACTUAL multiplier obeys the SAME ORIGINAL cumulative weighted finite-atlas MAX
norm estimate. The original real/imaginary fields P,Q are used directly; no complex paper
norm or alternate carrier is introduced. Finiteness is proved for the actual real output.
Only positive-order slow phase jets are assumed, on S inside the OPEN differentiation
charts O. The full coordinate index n includes ALL compact-parameter derivatives.

Proof: reuse the sole actual phase/product bounds. The existing weighted finite-Cj point
lemma bounds the true P,Q jets by their actual cumulative norms. Native component
complexification bounds actual z=P+iQ jets. The original paper norm bridge supplies one
uniform chart bound with its true n-dependent comparison factor. The proved actual real
scaled multiplier jets and public scaled_finiteCj_sum_le give output boundedness/cumulative
bounds. Reuse the accepted first-order paper proof's uniform weighted-profile argument:
each nonnegative weighted term is below its chart sum, divide by its positive weight,
and apply the original atlas-MAX norm bridge. No sum over chart labels is taken.
Source: `lem:increments`, lines669–675. -/
theorem increments_fast_multiplier_paper_weighted
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (j : ℕ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (ψ : ι → (Fin n → ℝ) → ℝ) (P Q : ι → (Fin n → ℝ) → Fin q → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (O i))
    (hP : ∀ i, ContDiffOn ℝ ∞ (P i) (O i))
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) (O i))
    (τ ℓ M : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1)
    (hjet : ∀ i, ∀ k < j, ∀ x ∈ S i,
      ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) (ψ i) x‖ ≤ M)
    (hfiniteP : paperAtlasWeighted 0 j ℓ P O S ≠ ⊤)
    (hfiniteQ : paperAtlasWeighted 0 j ℓ Q O S ≠ ⊤) :
    let g := fun i y c ↦ (Complex.exp (Complex.I * ((ψ i y / τ : ℝ) : ℂ)) *
      ((P i y c : ℂ) + Complex.I * (Q i y c : ℂ))).re
    paperAtlasWeighted 0 j τ g O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j τ g O S).toReal ≤
        incrementsFastPaperMultiplierConstant j n M *
          ((paperAtlasWeighted 0 j ℓ P O S).toReal +
            (paperAtlasWeighted 0 j ℓ Q O S).toReal) := by
  let g := fun i y c ↦ (Complex.exp (Complex.I * ((ψ i y / τ : ℝ) : ℂ)) *
    ((P i y c : ℂ) + Complex.I * (Q i y c : ℂ))).re
  let z := fun i y c ↦ (P i y c : ℂ) + Complex.I * (Q i y c : ℂ)
  let Dn := ∑ k ∈ Finset.range (j + 1), (n : ℝ) ^ k
  let Vp := (paperAtlasWeighted 0 j ℓ P O S).toReal
  let Vq := (paperAtlasWeighted 0 j ℓ Q O S).toReal
  let K := Dn * (Vp + Vq)
  let T := incrementsFastMultiplierConstant j M * K
  let R := (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) * T
  have hℓ0 : 0 < ℓ := hτ.trans_le hτℓ
  have hK : 0 ≤ K := by dsimp [K, Dn, Vp, Vq]; positivity
  have hT : 0 ≤ T := mul_nonneg (incrementsFastMultiplierConstant_pos j M).le hK
  have hR : 0 ≤ R := mul_nonneg (Finset.sum_nonneg (fun a ha ↦ by positivity)) hT
  have hPf : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (P i) x‖) := by
    simpa only [Nat.add_zero] using
      (paperAtlasWeighted_ne_top_iff 0 j ℓ hℓ0 P O S hO hSO hP).1 hfiniteP
  have hQf : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (Q i) x‖) := by
    simpa only [Nat.add_zero] using
      (paperAtlasWeighted_ne_top_iff 0 j ℓ hℓ0 Q O S hO hSO hQ).1 hfiniteQ
  have hPn (i : ι) : (∑ a ∈ Finset.range (j + 1),
      ℓ ^ a * finiteCjNorm a (P i) (S i)) ≤ Dn * Vp := by
    simpa only [Nat.add_zero] using
      paperAtlasWeighted_finiteCjNorm_bound 0 j ℓ hℓ0 P O S hO hSO hP hfiniteP i
  have hQn (i : ι) : (∑ a ∈ Finset.range (j + 1),
      ℓ ^ a * finiteCjNorm a (Q i) (S i)) ≤ Dn * Vq := by
    simpa only [Nat.add_zero] using
      paperAtlasWeighted_finiteCjNorm_bound 0 j ℓ hℓ0 Q O S hO hSO hQ hfiniteQ i
  have hzs (i : ι) : ContDiffOn ℝ ∞ (z i) (O i) :=
    increments_coordinate_complex_contDiffOn q (O i) (P i) (Q i) (hP i) (hQ i)
  have hzjet (i : ι) (b : ℕ) (hb : b ≤ j) (x : Fin n → ℝ) (hx : x ∈ S i) :
      ℓ ^ b * ‖iteratedFDeriv ℝ b (z i) x‖ ≤ K := by
    have hp := scaled_finiteCj_points j (P i) (S i) ℓ hℓ0.le (hPf i)
    have hq := scaled_finiteCj_points j (Q i) (S i) ℓ hℓ0.le (hQf i)
    calc
      _ ≤ ℓ ^ b * (‖iteratedFDeriv ℝ b (P i) x‖ +
          ‖iteratedFDeriv ℝ b (Q i) x‖) := mul_le_mul_of_nonneg_left
        (increments_coordinate_complex_jet_bound q b (O i) (hO i) (P i) (Q i)
          (hP i) (hQ i) x (hSO i hx)) (pow_nonneg hℓ0.le b)
      _ = ℓ ^ b * ‖iteratedFDeriv ℝ b (P i) x‖ +
          ℓ ^ b * ‖iteratedFDeriv ℝ b (Q i) x‖ := mul_add _ _ _
      _ ≤ (∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a (P i) (S i)) +
          ∑ a ∈ Finset.range (j + 1), ℓ ^ a * finiteCjNorm a (Q i) (S i) :=
        add_le_add (hp.2 b hb x hx) (hq.2 b hb x hx)
      _ ≤ K := by
        dsimp [K]
        rw [mul_add]
        exact add_le_add (hPn i) (hQn i)
  have hgj (i : ι) (k : ℕ) (hk : k ≤ j) (x : Fin n → ℝ) (hx : x ∈ S i) :
      τ ^ k * ‖iteratedFDeriv ℝ k (g i) x‖ ≤ T :=
    increments_fast_multiplier_real_jet_bound q j k hk (O i) (hO i) (ψ i) (z i)
      (hψ i) (hzs i) x (hSO i hx) τ ℓ M K hτ hτℓ hℓ hK
      (fun a ha ↦ hjet i a ha x hx) (fun b hb ↦ hzjet i b hb x hx)
  have hgs (i : ι) : ContDiffOn ℝ ∞ (g i) (O i) := by
    have h := (incrementsCoordinateRealPart q).contDiff.comp_contDiffOn
      ((increments_fast_phase_contDiffOn (O i) (ψ i) (hψ i) τ).smul (hzs i))
    exact h
  have he := fun i ↦ scaled_finiteCj_sum_le j (g i) (S i) τ T hτ (hτℓ.trans hℓ) hT (hgj i)
  have hgb : ∀ i, ∀ k ≤ j,
      BddAbove (Set.range fun x : S i ↦ ‖iteratedFDeriv ℝ k (g i) x‖) := fun i ↦ (he i).1
  have hgn : ∀ i, (∑ a ∈ Finset.range (j + 1),
      τ ^ a * finiteCjNorm a (g i) (S i)) ≤ R := fun i ↦ (he i).2
  have hout := increments_fast_paper_transport j O S hO hSO g hgs τ R hτ hR hgb hgn
  refine ⟨hout.1, hout.2.trans ?_⟩
  have hbase : ((j + 1 : ℕ) : ℝ) * R =
      (((j + 1 : ℕ) : ℝ) * (∑ a ∈ Finset.range (j + 1), ((a + 1 : ℕ) : ℝ)) *
        incrementsFastMultiplierConstant j M * Dn) * (Vp + Vq) := by
    dsimp [R, T, K]
    ring
  rw [hbase]
  apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
  exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Native local smoothness gives honest derivative boundedness on the original compact
SUP set. Source: buffered compact chart norms in `lem:increments`. -/
theorem increments_fast_compact_jet_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O S : Set E) (hO : IsOpen O) (hSO : S ⊆ O) (hS : IsCompact S)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O) (k : ℕ) :
    BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ k f x‖) := by
  have h0 := hf.continuousOn_iteratedFDerivWithin (m := k) (by simp) hO.uniqueDiffOn
  have hc : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) S := by
    apply ((h0.mono hSO).norm).congr
    intro x hx
    change ‖iteratedFDeriv ℝ k f x‖ = ‖iteratedFDerivWithin ℝ k f O x‖
    rw [iteratedFDerivWithin_of_isOpen k hO (hSO hx)]
  obtain ⟨K, hK⟩ := hS.bddAbove_image hc
  refine ⟨K, ?_⟩
  rintro y ⟨x, rfl⟩
  exact hK ⟨x, x.property, rfl⟩

/-- On the ORIGINAL compact SUP buffers, input norm finiteness is internally derived from
local smoothness. This removes even a supplied input-finiteness premise from the original
paper multiplier endpoint. The OPEN differentiation charts and compact buffers remain
separate, including every source/parameter coordinate. No bound on psi itself is used.
Source: `lem:increments`, original finite buffered atlas, lines669–675. -/
theorem increments_fast_multiplier_paper_weighted_compact
    {ι : Type*} [Fintype ι] {n q : ℕ}
    (j : ℕ) (O S : ι → Set (Fin n → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i) (hS : ∀ i, IsCompact (S i))
    (ψ : ι → (Fin n → ℝ) → ℝ) (P Q : ι → (Fin n → ℝ) → Fin q → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (O i))
    (hP : ∀ i, ContDiffOn ℝ ∞ (P i) (O i))
    (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) (O i))
    (τ ℓ M : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (hℓ : ℓ ≤ 1)
    (hjet : ∀ i, ∀ k < j, ∀ x ∈ S i,
      ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) (ψ i) x‖ ≤ M) :
    let g := fun i y c ↦ (Complex.exp (Complex.I * ((ψ i y / τ : ℝ) : ℂ)) *
      ((P i y c : ℂ) + Complex.I * (Q i y c : ℂ))).re
    paperAtlasWeighted 0 j τ g O S ≠ ⊤ ∧
      (paperAtlasWeighted 0 j τ g O S).toReal ≤
        incrementsFastPaperMultiplierConstant j n M *
          ((paperAtlasWeighted 0 j ℓ P O S).toReal +
            (paperAtlasWeighted 0 j ℓ Q O S).toReal) := by
  have hPf := paperAtlasWeighted_ne_top 0 j ℓ P O S hO hSO hP
    (fun i k hk ↦ increments_fast_compact_jet_range
      (O i) (S i) (hO i) (hSO i) (hS i) (P i) (hP i) k)
  have hQf := paperAtlasWeighted_ne_top 0 j ℓ Q O S hO hSO hQ
    (fun i k hk ↦ increments_fast_compact_jet_range
      (O i) (S i) (hO i) (hSO i) (hS i) (Q i) (hQ i) k)
  exact increments_fast_multiplier_paper_weighted j O S hO hSO ψ P Q hψ hP hQ
    τ ℓ M hτ hτℓ hℓ hjet hPf hQf

end GlobalEmbedding.Paper
