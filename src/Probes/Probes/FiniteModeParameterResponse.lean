import GlobalEmbedding.Paper.IncrementsActualModeSize
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual finite homogeneous solver: native parameter derivatives

Source: main.tex (6.2) and (8.3). The source below is the literal finite
real-parameter combination of smooth mode sources. We use the ORIGINAL
incrementsActualModeSum, not an unspecified solver. Native source differentiation
is justified on its original open domain before exposing the parameter-linear map.
This never asserts linearity of totalized differentiation on arbitrary functions.
-/

noncomputable section

open GlobalEmbedding.Paper Set Filter
open scoped ContDiff BigOperators Topology

namespace GlobalEmbedding.Continuation

variable {D E ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [Fintype ι]

/-- Additivity of the original finite differential polynomial on smooth local sources. -/
theorem actual_mode_sum_add
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k h : D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ContDiffOn ℝ ∞ k O) (hh : ContDiffOn ℝ ∞ h O)
    (x : D) (hx : x ∈ O) :
    incrementsActualModeSum A B alpha p (fun y ↦ k y + h y) x =
      incrementsActualModeSum A B alpha p k x + incrementsActualModeSum A B alpha p h x := by
  have he := increments_actual_mode_sum_sub A B alpha p (fun y ↦ k y + h y) k
    O hO hA hB (hk.add hh) hk hx
  have hfun : (fun y ↦ (k y + h y) - k y) = h := by funext y; abel
  rw [hfun] at he
  exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)

/-- The actual finite source family. -/
def finiteProbeSource (k : ι → D → E) (u : ι → ℝ) (x : D) : E :=
  ∑ i, u i • k i x

theorem finiteProbeSource_contDiffOn (k : ι → D → E) (O : Set D)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (u : ι → ℝ) :
    ContDiffOn ℝ ∞ (finiteProbeSource k u) O :=
  ContDiffOn.sum fun i _ ↦ (hk i).const_smul (u i)

theorem finiteProbeSource_add (k : ι → D → E) (u v : ι → ℝ) :
    finiteProbeSource k (u + v) = fun x ↦ finiteProbeSource k u x + finiteProbeSource k v x := by
  funext x
  simp only [finiteProbeSource, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem finiteProbeSource_smul (k : ι → D → E) (c : ℝ) (u : ι → ℝ) :
    finiteProbeSource k (c • u) = fun x ↦ c • finiteProbeSource k u x := by
  funext x
  simp only [finiteProbeSource, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- The ORIGINAL finite solver restricted to this finite smooth source span.
Every datum, scale, reconstruction length and observation point stays fixed. -/
def finiteModeParameterLinearMap
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) :
    (ι → ℝ) →ₗ[ℝ] E where
  toFun u := incrementsActualModeSum A B alpha p (finiteProbeSource k u) x
  map_add' u v := by
    rw [finiteProbeSource_add]
    exact actual_mode_sum_add A B alpha p _ _ O hO hA hB
      (finiteProbeSource_contDiffOn k O hk u) (finiteProbeSource_contDiffOn k O hk v) x hx
  map_smul' c u := by
    rw [finiteProbeSource_smul]
    exact increments_actual_mode_sum_real_smul A B alpha p (finiteProbeSource k u) c
      O hO hA hB (finiteProbeSource_contDiffOn k O hk u) hx

/-- Continuity uses only the actual finite-dimensional parameter domain. -/
def finiteModeParameterMap
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) :
    (ι → ℝ) →L[ℝ] E :=
  (finiteModeParameterLinearMap A B alpha p k O hO hA hB hk x hx).toContinuousLinearMap

theorem finiteModeParameterMap_apply
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    finiteModeParameterMap A B alpha p k O hO hA hB hk x hx u =
      incrementsActualModeSum A B alpha p (finiteProbeSource k u) x := rfl

/-- Actual first parameter differentiation commutes with this finite solver.
The derivative is independent of the parameter, including at zero. -/
theorem hasFDerivAt_finiteModeParameter
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    HasFDerivAt (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) x)
      (finiteModeParameterMap A B alpha p k O hO hA hB hk x hx) u :=
  (finiteModeParameterMap A B alpha p k O hO hA hB hk x hx).hasFDerivAt

/-- A literal parameter column is the finite reconstruction of that same source
column, with no numerical difference quotient or assumed response formula. -/
theorem fderiv_finiteModeParameter_column [DecidableEq ι]
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) (i : ι) :
    fderiv ℝ (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) x) u
      (Pi.single i 1) = incrementsActualModeSum A B alpha p (k i) x := by
  rw [(hasFDerivAt_finiteModeParameter A B alpha p k O hO hA hB hk x hx u).fderiv,
    finiteModeParameterMap_apply]
  congr 1
  funext y
  simp [finiteProbeSource, Pi.single_apply]

/-- Every real parameter direction is passed through the SAME finite solver. -/
theorem fderiv_finiteModeParameter_apply
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u v : ι → ℝ) :
    fderiv ℝ (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) x) u v =
      incrementsActualModeSum A B alpha p (finiteProbeSource k v) x := by
  rw [(hasFDerivAt_finiteModeParameter A B alpha p k O hO hA hB hk x hx u).fderiv]
  rfl

/-- Native mixed spatial/parameter derivatives retain the actual source.  The
germ is on the original open chart; no globally smooth extension is assumed. -/
theorem iteratedFDeriv_fderiv_finiteModeParameter_apply
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O)
    (u v : ι → ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ
      (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) y) u v) x =
    iteratedFDeriv ℝ j
      (incrementsActualModeSum A B alpha p (finiteProbeSource k v)) x := by
  have he : (fun y ↦ fderiv ℝ
      (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) y) u v)
      =ᶠ[𝓝 x] incrementsActualModeSum A B alpha p (finiteProbeSource k v) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact fderiv_finiteModeParameter_apply A B alpha p k O hO hA hB hk y hy u v
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- Literal finite expansion of the actual solved source, justified on the
smooth source span before using finite-dimensional parameter algebra. -/
theorem finiteModeParameter_eq_sum [DecidableEq ι]
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    incrementsActualModeSum A B alpha p (finiteProbeSource k u) x =
      ∑ i, u i • incrementsActualModeSum A B alpha p (k i) x := by
  let L := finiteModeParameterMap A B alpha p k O hO hA hB hk x hx
  have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  change L u = _
  calc
    L u = L (∑ i, u i • Pi.single i (1 : ℝ)) := congrArg L hu
    _ = ∑ i, u i • incrementsActualModeSum A B alpha p (k i) x := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      congr 1
      change incrementsActualModeSum A B alpha p (finiteProbeSource k (Pi.single i 1)) x = _
      congr 1
      funext y
      simp [finiteProbeSource, Pi.single_apply]

/-- The actual homogeneous solution is odd in the real probe parameters. -/
theorem finiteModeParameter_neg
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    incrementsActualModeSum A B alpha p (finiteProbeSource k (-u)) x =
      -incrementsActualModeSum A B alpha p (finiteProbeSource k u) x :=
  map_neg (finiteModeParameterMap A B alpha p k O hO hA hB hk x hx) u

/-- The actual second parameter derivative vanishes, with scales and finite
reconstruction length fixed once and for all. -/
theorem fderiv_fderiv_finiteModeParameter
    (A : D → (D →L[ℝ] E) →L[ℝ] E) (B : D → E →L[ℝ] E)
    (alpha : ℂ) (p : ℕ) (k : ι → D → E) (O : Set D) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (hk : ∀ i, ContDiffOn ℝ ∞ (k i) O) (x : D) (hx : x ∈ O) (u : ι → ℝ) :
    fderiv ℝ (fderiv ℝ
      (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) x)) u = 0 := by
  have he : fderiv ℝ
      (fun w ↦ incrementsActualModeSum A B alpha p (finiteProbeSource k w) x) =
      fun _ ↦ finiteModeParameterMap A B alpha p k O hO hA hB hk x hx :=
    funext fun w ↦ (hasFDerivAt_finiteModeParameter A B alpha p k O hO hA hB hk x hx w).fderiv
  simp only [he, fderiv_fun_const, Pi.zero_apply]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.hasFDerivAt_finiteModeParameter
#print axioms GlobalEmbedding.Continuation.fderiv_finiteModeParameter_column
#print axioms GlobalEmbedding.Continuation.iteratedFDeriv_fderiv_finiteModeParameter_apply
#print axioms GlobalEmbedding.Continuation.finiteModeParameter_eq_sum
#print axioms GlobalEmbedding.Continuation.fderiv_fderiv_finiteModeParameter
