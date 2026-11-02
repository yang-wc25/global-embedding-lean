import GlobalEmbedding.Paper.IncrementsModeFirstOrderCoefficients

/-!
# Actual complex scalar identities and original homogeneous source

Source: `main.tex`, lem:increments, (6.2), lines 620–643.
DAG: `increments-mode-complex-linearity-source-scaling`. Exclusive worker W2.
The coefficients are precisely the accepted geometric coefficient fields. No new
section carrier or complex normal bundle is used; weighted coefficient bounds remain open.
-/

noncomputable section
open Manifold
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Cdata" => Fin (m + 1) → ℂ

/-- Actual native real components of a complex multiple.
Source: component realization of the original complex system (6.2). -/
theorem incrementsModeRealPart_smul (α : ℂ) (z : Cdata) :
    incrementsModeRealPart (α • z) =
      α.re • incrementsModeRealPart z - α.im • incrementsModeImagPart z := by
  ext i
  simp [incrementsModeRealPart, incrementsModeImagPart, Complex.mul_re, smul_eq_mul]

/-- Actual native imaginary components of a complex multiple.
Source: component realization of the original complex system (6.2). -/
theorem incrementsModeImagPart_smul (α : ℂ) (z : Cdata) :
    incrementsModeImagPart (α • z) =
      α.re • incrementsModeImagPart z + α.im • incrementsModeRealPart z := by
  ext i
  simp [incrementsModeRealPart, incrementsModeImagPart, Complex.mul_im, smul_eq_mul]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- SAME actual zeroth-order B commutes with every complex scalar.
Proof: native real/imaginary multiplication followed by real CLM linearity.
Source: the complex-linear original mode operator of (6.2). -/
theorem incrementsModeComplexFirstOrderB_smul (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D)
    (α : ℂ) (z : Cdata) :
    incrementsModeComplexFirstOrderB F hF c x (α • z) =
      α • incrementsModeComplexFirstOrderB F hF c x z := by
  change incrementsModeComplexInclude
      (incrementsModeFirstOrderB F hF c x (incrementsModeRealPart (α • z))) +
    Complex.I • incrementsModeComplexInclude
      (incrementsModeFirstOrderB F hF c x (incrementsModeImagPart (α • z))) = _
  rw [incrementsModeRealPart_smul, incrementsModeImagPart_smul]
  simp only [map_sub, map_add, map_smul]
  ext i
  simp [incrementsModeComplexInclude, incrementsModeComplexFirstOrderB, Complex.real_smul,
    smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im α]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

/-- SAME actual first-jet A commutes with every complex scalar on the native jets.
Proof: the two composed channel jets obey native multiplication formulas, and the
accepted real coefficient is genuinely linear on those jets. Source: (6.2). -/
theorem incrementsModeComplexFirstOrderA_smul (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D)
    (α : ℂ) (jet : D →L[ℝ] Cdata) :
    incrementsModeComplexFirstOrderA F hF c x (α • jet) =
      α • incrementsModeComplexFirstOrderA F hF c x jet := by
  have hr : incrementsModeRealPart.comp (α • jet) =
      α.re • incrementsModeRealPart.comp jet - α.im • incrementsModeImagPart.comp jet := by
    ext v i
    exact congrArg (fun z : D ↦ z i) (incrementsModeRealPart_smul α (jet v))
  have hi : incrementsModeImagPart.comp (α • jet) =
      α.re • incrementsModeImagPart.comp jet + α.im • incrementsModeRealPart.comp jet := by
    ext v i
    exact congrArg (fun z : D ↦ z i) (incrementsModeImagPart_smul α (jet v))
  change incrementsModeComplexInclude
      (incrementsModeFirstOrderA F hF c x (incrementsModeRealPart.comp (α • jet))) +
    Complex.I • incrementsModeComplexInclude
      (incrementsModeFirstOrderA F hF c x (incrementsModeImagPart.comp (α • jet))) = _
  rw [hr, hi]
  simp only [map_sub, map_add, map_smul]
  ext i
  simp [incrementsModeComplexInclude, incrementsModeComplexFirstOrderA, Complex.real_smul,
    smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im α]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

/-- SAME B, now with its proved complex linearity and original continuity exposed.
Source: original complex mode operator (6.2); its underlying function is unchanged. -/
def incrementsModeComplexFirstOrderBCLM (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    Cdata →L[ℂ] Cdata where
  toFun := incrementsModeComplexFirstOrderB F hF c x
  map_add' := map_add _
  map_smul' α z := incrementsModeComplexFirstOrderB_smul F hF c x α z
  cont := (incrementsModeComplexFirstOrderB F hF c x).continuous

/-- SAME A, with proved complex linearity on the native real-spatial complex jets.
Source: original complex mode operator (6.2); no new jet or section carrier. -/
def incrementsModeComplexFirstOrderACLM (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D) :
    (D →L[ℝ] Cdata) →L[ℂ] Cdata where
  toFun := incrementsModeComplexFirstOrderA F hF c x
  map_add' := map_add _
  map_smul' α jet := incrementsModeComplexFirstOrderA_smul F hF c x α jet
  cont := (incrementsModeComplexFirstOrderA F hF c x).continuous

/-- The exposed complex CLM is literally SAME original B on every input.
Source: typed coefficient interface for the original finite mode reconstruction. -/
theorem incrementsModeComplexFirstOrderBCLM_apply (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D)
    (z : Cdata) :
    incrementsModeComplexFirstOrderBCLM F hF c x z =
      incrementsModeComplexFirstOrderB F hF c x z := rfl

/-- The exposed complex CLM is literally SAME original A on every native jet.
Source: typed coefficient interface for the original finite mode reconstruction. -/
theorem incrementsModeComplexFirstOrderACLM_apply (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M) (x : D)
    (jet : D →L[ℝ] Cdata) :
    incrementsModeComplexFirstOrderACLM F hF c x jet =
      incrementsModeComplexFirstOrderA F hF c x jet := rfl

/-- The SAME actual reduced L commutes with a complex scalar at a real-differentiability
point. Use the accepted actual first-order identity, the true scalar derivative rule,
and the proved coefficient scalar identities. No nonsmooth linearity is asserted.
Source: the finite complex reconstruction after (6.2). -/
theorem incrementsModeComplexReducedOperator_smul (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (u : D → Cdata) (x : D) (α : ℂ) (hu : DifferentiableAt ℝ u x) :
    incrementsModeComplexReducedOperator F hF c (fun y ↦ α • u y) x =
      α • incrementsModeComplexReducedOperator F hF c u x := by
  calc
    _ = incrementsModeComplexFirstOrderB F hF c x (α • u x) +
        incrementsModeComplexFirstOrderA F hF c x
          (fderiv ℝ (fun y ↦ α • u y) x) :=
      incrementsModeComplexReducedOperator_first_order F hF c
        (fun y ↦ α • u y) x (hu.const_smul α)
    _ = α • (incrementsModeComplexFirstOrderB F hF c x (u x) +
        incrementsModeComplexFirstOrderA F hF c x (fderiv ℝ u x)) := by
      rw [fderiv_fun_const_smul hu α, incrementsModeComplexFirstOrderB_smul,
        incrementsModeComplexFirstOrderA_smul, smul_add]
    _ = _ := congrArg (fun z : Cdata ↦ α • z)
      (incrementsModeComplexReducedOperator_first_order F hF c u x hu).symm

/-- The actual h=0 source is homogeneous in its SAME original real normal amplitude.
All real delta, including zero, are allowed. Native J(0)=0 and the real inner scalar
law give the identity with the ORIGINAL first/mixed row weights. Source: (6.2). -/
theorem incrementsModeSource_zero_smul (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (c : D → M)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) (δ : ℝ) :
    incrementsModeSource F hF c (fun _ _ _ ↦ 0) (fun y ↦ δ • vf y) x =
      δ • incrementsModeSource F hF c (fun _ _ _ ↦ 0) vf x := by
  have hz : incrementsModeTransverseSource (fun _ _ _ ↦ 0) x = 0 := rfl
  ext i
  refine Fin.cases ?_ (fun a ↦ ?_) i <;>
    simp [incrementsModeSource, hz, inner_smul_right] <;> ring

end GlobalEmbedding.Paper
