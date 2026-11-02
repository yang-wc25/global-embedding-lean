import Probes.ActualFiniteProbeJets
import Probes.ActualProbeFirstBounds
import Probes.ActualProbeLocalScaleBounds

/-!
# Actual fixed-connection parameter response and the connection error budget

Source: prop:probes, B=D2F-Gamma(h0)DF. This file computes the native parameter
derivative of D2U-Gamma DU for the actual finite displacement. The connection
term is bounded from the already proved actual first derivative, giving the
additional sigma*tau error. ActualFixedMetricSecondForm identifies the same
expression with the original trueSecondForm when the full family has the
fixed induced metric; that metric property is not asserted for the leading
finite displacement alone.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p r : ℕ}

-- These are Mathlib's native operator norm instances, fixed explicitly to
-- keep nested operator topology elaboration coherent; no norm is changed.
private noncomputable local instance connectionBilinearSemi
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance connectionBilinearNormed
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance connectionBilinearNormedSpace
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace

/-- The fixed connection acts linearly on an actual first jet. -/
def probeConnectionComposition (Γ : E →L[ℝ] E →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] F)).flip Γ).comp
    (ContinuousLinearMap.compL ℝ E E F)

theorem probeConnectionComposition_apply (Γ : E →L[ℝ] E →L[ℝ] E)
    (L : E →L[ℝ] F) (v w : E) :
    probeConnectionComposition Γ L v w = L (Γ v w) := rfl

/-- Native operator estimate for the connection term, retaining its actual norm. -/
theorem norm_probeConnectionComposition_apply_le (Γ : E →L[ℝ] E →L[ℝ] E)
    (L : E →L[ℝ] F) : ‖probeConnectionComposition Γ L‖ ≤ ‖L‖ * ‖Γ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  change ‖L (Γ v w)‖ ≤ ‖L‖ * ‖Γ‖ * ‖v‖ * ‖w‖
  calc
    _ ≤ ‖L‖ * ‖Γ v w‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (‖Γ‖ * ‖v‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (Γ.le_opNorm₂ v w) (norm_nonneg _)
    _ = _ := by ring

/-- The actual native fixed-connection Hessian, with the original order/sign. -/
def probeFixedConnectionHessian (Γ : E →L[ℝ] E →L[ℝ] E) (f : E → F) (x : E) :
    E →L[ℝ] E →L[ℝ] F :=
  fderiv ℝ (fderiv ℝ f) x - probeConnectionComposition Γ (fderiv ℝ f x)

/-- Native first jet of the same finite family. -/
theorem actualFiniteProbeDisplacement_fderiv
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ 1 (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ 1 (amplitude i) x) :
    fderiv ℝ (actualFiniteProbeDisplacement label δ τ weight phase amplitude u) x =
      probePairedColumnMap label
        (fun i ↦ fderiv ℝ (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
        (fun i ↦ fderiv ℝ (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x) u := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T ↦ T ![v])
    (actualFiniteProbeDisplacement_iteratedFDeriv 1 label δ τ weight phase amplitude u x
      hphase hamplitude)
  simpa [probePairedColumnMap_apply, sum_apply, add_apply, smul_apply] using h

/-- Native parameter derivative of the actual first jet. -/
theorem hasFDerivAt_actualFiniteProbeFirstJet
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ 1 (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ 1 (amplitude i) x) :
    HasFDerivAt
      (fun w ↦ fderiv ℝ (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x)
      (probePairedColumnMap label
        (fun i ↦ fderiv ℝ (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
        (fun i ↦ fderiv ℝ (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x)) u := by
  have heq := funext (fun w ↦ actualFiniteProbeDisplacement_fderiv label δ τ
    weight phase amplitude w x hphase hamplitude)
  rw [heq]
  exact (probePairedColumnMap label _ _).hasFDerivAt

/-- The parameter derivative of the actual covariant Hessian is obtained
by differentiating the actual Hessian and the actual first jet. -/
theorem hasFDerivAt_actualFiniteProbeFixedConnectionHessian
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ 2 (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ 2 (amplitude i) x) :
    HasFDerivAt (fun w ↦ probeFixedConnectionHessian Γ
        (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x)
      ((probePairedColumnMap label
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i))) x)
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i))) x)) -
       (probeConnectionComposition Γ).comp (probePairedColumnMap label
        (fun i ↦ fderiv ℝ (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
        (fun i ↦ fderiv ℝ (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x))) u := by
  exact (hasFDerivAt_actualFiniteProbeHessian label δ τ weight phase amplitude u x
    hphase hamplitude).sub
      ((probeConnectionComposition (F := F) Γ).hasFDerivAt.comp u
        (hasFDerivAt_actualFiniteProbeFirstJet label δ τ weight phase amplitude u x
          (fun i ↦ (hphase i).of_le (by norm_num))
          (fun i ↦ (hamplitude i).of_le (by norm_num))))

/-- The actual cosine remainder after the fixed connection is included. -/
def actualProbeCosConnectionRemainder (Γ : E →L[ℝ] E →L[ℝ] E)
    (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  actualProbeCosRemainder δ τ lam ψ A x -
    probeConnectionComposition Γ (fderiv ℝ (actualProbeCosColumn δ τ lam ψ A) x)

/-- The matching sine remainder of the same fixed connection. -/
def actualProbeSinConnectionRemainder (Γ : E →L[ℝ] E →L[ℝ] E)
    (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  actualProbeSinRemainder δ τ lam ψ A x -
    probeConnectionComposition Γ (fderiv ℝ (actualProbeSinColumn δ τ lam ψ A) x)

/-- The true cosine parameter response of the actual finite covariant Hessian. -/
theorem actualFiniteProbeFixedConnectionHessian_cos_response
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ∀ k, ContDiffAt ℝ 2 (phase k) x)
    (hamplitude : ∀ k, ContDiffAt ℝ 2 (amplitude k) x) :
    fderiv ℝ (fun w ↦ probeFixedConnectionHessian Γ
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x) u
      (Pi.single (label (i, false)) 1) =
      ((δ / τ) * Real.cos (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeCosConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeFixedConnectionHessian Γ label δ τ weight phase amplitude u x
    hphase hamplitude).fderiv, sub_apply, ContinuousLinearMap.comp_apply,
    probePairedColumnMap_cos_column, probePairedColumnMap_cos_column,
    actualProbeCosColumn_hessian_at (hphase i) (hamplitude i) δ τ (weight i) hτ hw]
  simp only [actualProbeCosConnectionRemainder]
  abel

/-- The paired sine parameter response has the same native remainder budget. -/
theorem actualFiniteProbeFixedConnectionHessian_sin_response
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ∀ k, ContDiffAt ℝ 2 (phase k) x)
    (hamplitude : ∀ k, ContDiffAt ℝ 2 (amplitude k) x) :
    fderiv ℝ (fun w ↦ probeFixedConnectionHessian Γ
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x) u
      (Pi.single (label (i, true)) 1) =
      ((δ / τ) * Real.sin (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeSinConnectionRemainder Γ δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeFixedConnectionHessian Γ label δ τ weight phase amplitude u x
    hphase hamplitude).fderiv, sub_apply, ContinuousLinearMap.comp_apply,
    probePairedColumnMap_sin_column, probePairedColumnMap_sin_column,
    actualProbeSinColumn_hessian_at (hphase i) (hamplitude i) δ τ (weight i) hτ hw]
  simp only [actualProbeSinConnectionRemainder]
  abel

/-- The connection contribution has the actual O(delta) bound, hence size
sigma*tau. Both constants retain the actual slow amplitude/phase bounds. -/
theorem norm_actualProbeCosConnectionRemainder_slow_scale
    {ψ : E → ℝ} {A : E → F} (x : E)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (Γ : E →L[ℝ] E →L[ℝ] E) (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeCosConnectionRemainder Γ δ τ lam ψ A x‖ ≤
      (δ / τ) * ((τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) +
        τ * (K₁ / lam ^ 2 + P₁ * K₀ / lam) * ‖Γ‖) := by
  have hR := norm_actualProbeCosRemainder_slow_scale_at x hψ hA
    δ τ ell lam K₀ K₁ K₂ P₁ P₂ hδ hτ hlam hτell hK₀ hK₁ hK₂ hP₁ hP₂
    hA₀ hA₁ hA₂ hψ₁ hψ₂
  have hD := norm_fderiv_actualProbeCosColumn_slow_scale x
    (hψ.differentiableAt (by norm_num)) (hA.differentiableAt (by norm_num))
    δ τ ell lam K₀ K₁ P₁ hδ hτ hlam hτell hK₁ hP₁ hA₀ hA₁ hψ₁
  calc
    _ ≤ ‖actualProbeCosRemainder δ τ lam ψ A x‖ +
      ‖probeConnectionComposition Γ (fderiv ℝ (actualProbeCosColumn δ τ lam ψ A) x)‖ :=
      norm_sub_le _ _
    _ ≤ (δ / τ) * (τ / ell) *
        (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) +
      (δ * (K₁ / lam ^ 2 + P₁ * K₀ / lam)) * ‖Γ‖ :=
      add_le_add hR ((norm_probeConnectionComposition_apply_le Γ _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg Γ)))
    _ = _ := by field_simp

/-- The same sigma*(tau/ell+tau) bound for the sine partner. -/
theorem norm_actualProbeSinConnectionRemainder_slow_scale
    {ψ : E → ℝ} {A : E → F} (x : E)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (Γ : E →L[ℝ] E →L[ℝ] E) (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeSinConnectionRemainder Γ δ τ lam ψ A x‖ ≤
      (δ / τ) * ((τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) +
        τ * (K₁ / lam ^ 2 + P₁ * K₀ / lam) * ‖Γ‖) := by
  have hR := norm_actualProbeSinRemainder_slow_scale_at x hψ hA
    δ τ ell lam K₀ K₁ K₂ P₁ P₂ hδ hτ hlam hτell hK₀ hK₁ hK₂ hP₁ hP₂
    hA₀ hA₁ hA₂ hψ₁ hψ₂
  have hD := norm_fderiv_actualProbeSinColumn_slow_scale x
    (hψ.differentiableAt (by norm_num)) (hA.differentiableAt (by norm_num))
    δ τ ell lam K₀ K₁ P₁ hδ hτ hlam hτell hK₁ hP₁ hA₀ hA₁ hψ₁
  calc
    _ ≤ ‖actualProbeSinRemainder δ τ lam ψ A x‖ +
      ‖probeConnectionComposition Γ (fderiv ℝ (actualProbeSinColumn δ τ lam ψ A) x)‖ :=
      norm_sub_le _ _
    _ ≤ (δ / τ) * (τ / ell) *
        (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) +
      (δ * (K₁ / lam ^ 2 + P₁ * K₀ / lam)) * ‖Γ‖ :=
      add_le_add hR ((norm_probeConnectionComposition_apply_le Γ _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg Γ)))
    _ = _ := by field_simp

#print axioms actualFiniteProbeFixedConnectionHessian_cos_response
#print axioms actualFiniteProbeFixedConnectionHessian_sin_response
#print axioms norm_actualProbeCosConnectionRemainder_slow_scale
#print axioms norm_actualProbeSinConnectionRemainder_slow_scale
end GlobalEmbedding.Offline
