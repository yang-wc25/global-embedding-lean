import Probes.ActualFiniteProbeResponse
import Probes.ActualProbeLocalJets

/-!
# Native spatial jets and parameter response of the same finite probe family

Every derivative below is of `actualFiniteProbeDisplacement`; the coefficient
maps only package its proved finite derivative sums. In particular the native
parameter derivative of the actual Hessian is computed directly, without
assuming an interchange of derivatives or supplying the desired derivative as
an input. All smoothness hypotheses are pointwise germs on the original chart.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p r : ℕ}

/-- The continuous linear parameter map with a specified pair of columns for
each original dictionary element. This is used for values and every jet order. -/
def probePairedColumnMap (label : (Fin r × Bool) ↪ Fin p)
    (c s : Fin r → F) : (Fin p → ℝ) →L[ℝ] F :=
  ∑ i, ((ContinuousLinearMap.proj (label (i, false))).smulRight (c i) +
    (ContinuousLinearMap.proj (label (i, true))).smulRight (s i))

/-- Its literal finite parameter sum. -/
theorem probePairedColumnMap_apply
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F) (u : Fin p → ℝ) :
    probePairedColumnMap label c s u =
      ∑ i, (u (label (i, false)) • c i + u (label (i, true)) • s i) := by
  simp [probePairedColumnMap]

/-- Distinct actual labels isolate the cosine column. -/
theorem probePairedColumnMap_cos_column
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F) (i : Fin r) :
    probePairedColumnMap label c s (Pi.single (label (i, false)) 1) = c i := by
  classical
  simp [probePairedColumnMap, Pi.single_apply, label.injective.eq_iff]

/-- Distinct actual labels isolate the sine column. -/
theorem probePairedColumnMap_sin_column
    (label : (Fin r × Bool) ↪ Fin p) (c s : Fin r → F) (i : Fin r) :
    probePairedColumnMap label c s (Pi.single (label (i, true)) 1) = s i := by
  classical
  simp [probePairedColumnMap, Pi.single_apply, label.injective.eq_iff]

/-- Native smoothness of the actual cosine column at any finite order. -/
theorem contDiffAt_actualProbeCosColumn {n : ℕ} {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ n ψ x) (hA : ContDiffAt ℝ n A x) (δ τ lam : ℝ) :
    ContDiffAt ℝ n (actualProbeCosColumn δ τ lam ψ A) x :=
  (((hψ.const_smul (lam / τ)).cos).smul hA).const_smul (-(δ * τ / lam ^ 2))

/-- Native smoothness of the actual sine column. -/
theorem contDiffAt_actualProbeSinColumn {n : ℕ} {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ n ψ x) (hA : ContDiffAt ℝ n A x) (δ τ lam : ℝ) :
    ContDiffAt ℝ n (actualProbeSinColumn δ τ lam ψ A) x :=
  (((hψ.const_smul (lam / τ)).sin).smul hA).const_smul (-(δ * τ / lam ^ 2))

/-- The spatial jet of the literal finite family is its finite sum of native
wave jets. The parameter labels and original amplitudes are unchanged. -/
theorem actualFiniteProbeDisplacement_iteratedFDeriv
    (n : ℕ) (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ n (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ n (amplitude i) x) :
    iteratedFDeriv ℝ n (actualFiniteProbeDisplacement label δ τ weight phase amplitude u) x =
      probePairedColumnMap label
        (fun i ↦ iteratedFDeriv ℝ n
          (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
        (fun i ↦ iteratedFDeriv ℝ n
          (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x) u := by
  classical
  have hc i := contDiffAt_actualProbeCosColumn (hphase i) (hamplitude i) δ τ (weight i)
  have hs i := contDiffAt_actualProbeSinColumn (hphase i) (hamplitude i) δ τ (weight i)
  have heq : actualFiniteProbeDisplacement label δ τ weight phase amplitude u =
      fun z ↦ ∑ i, (u (label (i, false)) •
        actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i) z +
        u (label (i, true)) •
        actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i) z) := by
    funext z
    exact actualFiniteProbeDisplacement_eq_sum label δ τ weight phase amplitude u z
  rw [heq, iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((hc i).const_smul _).add ((hs i).const_smul _)), probePairedColumnMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fun_iteratedFDeriv_add_apply ((hc i).const_smul _) ((hs i).const_smul _),
    iteratedFDeriv_const_smul_apply' (hc i), iteratedFDeriv_const_smul_apply' (hs i)]

/-- The true parameter derivative AFTER taking any spatial jet. It is
independent of the base parameter, as proved for the actual finite family. -/
theorem hasFDerivAt_actualFiniteProbeSpatialJet
    (n : ℕ) (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ n (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ n (amplitude i) x) :
    HasFDerivAt
      (fun w ↦ iteratedFDeriv ℝ n
        (actualFiniteProbeDisplacement label δ τ weight phase amplitude w) x)
      (probePairedColumnMap label
        (fun i ↦ iteratedFDeriv ℝ n
          (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i)) x)
        (fun i ↦ iteratedFDeriv ℝ n
          (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i)) x)) u := by
  have heq := funext (fun w ↦ actualFiniteProbeDisplacement_iteratedFDeriv n label δ τ
    weight phase amplitude w x hphase hamplitude)
  rw [heq]
  exact (probePairedColumnMap label _ _).hasFDerivAt

/-- The same statement at the nested-continuous-linear-map Hessian used by
the original second fundamental form. -/
theorem actualFiniteProbeDisplacement_hessian
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ 2 (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ 2 (amplitude i) x) :
    fderiv ℝ (fderiv ℝ
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude u)) x =
      probePairedColumnMap label
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i))) x)
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i))) x) u := by
  classical
  ext v w
  have h := congrArg (fun T ↦ T ![v, w])
    (actualFiniteProbeDisplacement_iteratedFDeriv 2 label δ τ weight phase amplitude u x
      hphase hamplitude)
  simpa [probePairedColumnMap_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply,
    iteratedFDeriv_two_apply, Fin.sum_univ_two, sum_apply, add_apply, smul_apply] using h

/-- Native derivative of the actual Hessian with respect to the true finite
parameters, with no mixed-derivative interchange assumption. -/
theorem hasFDerivAt_actualFiniteProbeHessian
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E)
    (hphase : ∀ i, ContDiffAt ℝ 2 (phase i) x)
    (hamplitude : ∀ i, ContDiffAt ℝ 2 (amplitude i) x) :
    HasFDerivAt
      (fun w ↦ fderiv ℝ (fderiv ℝ
        (actualFiniteProbeDisplacement label δ τ weight phase amplitude w)) x)
      (probePairedColumnMap label
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeCosColumn δ τ (weight i) (phase i) (amplitude i))) x)
        (fun i ↦ fderiv ℝ (fderiv ℝ
          (actualProbeSinColumn δ τ (weight i) (phase i) (amplitude i))) x)) u := by
  have heq := funext (fun w ↦ actualFiniteProbeDisplacement_hessian label δ τ
    weight phase amplitude w x hphase hamplitude)
  rw [heq]
  exact (probePairedColumnMap label _ _).hasFDerivAt

/-- The actual cosine parameter derivative of the actual spatial Hessian has
the original sigma main term and the actual slow remainder. -/
theorem actualFiniteProbeHessian_cos_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ∀ k, ContDiffAt ℝ 2 (phase k) x)
    (hamplitude : ∀ k, ContDiffAt ℝ 2 (amplitude k) x) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w)) x) u
      (Pi.single (label (i, false)) 1) =
      ((δ / τ) * Real.cos (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeCosRemainder δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeHessian label δ τ weight phase amplitude u x
    hphase hamplitude).fderiv, probePairedColumnMap_cos_column]
  exact actualProbeCosColumn_hessian_at (hphase i) (hamplitude i) δ τ (weight i) hτ hw

/-- The paired sine derivative of the same actual Hessian. -/
theorem actualFiniteProbeHessian_sin_response
    (label : (Fin r × Bool) ↪ Fin p) (δ τ : ℝ) (weight : Fin r → ℝ)
    (phase : Fin r → E → ℝ) (amplitude : Fin r → E → F)
    (u : Fin p → ℝ) (x : E) (i : Fin r) (hτ : τ ≠ 0) (hw : weight i ≠ 0)
    (hphase : ∀ k, ContDiffAt ℝ 2 (phase k) x)
    (hamplitude : ∀ k, ContDiffAt ℝ 2 (amplitude k) x) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ
      (actualFiniteProbeDisplacement label δ τ weight phase amplitude w)) x) u
      (Pi.single (label (i, true)) 1) =
      ((δ / τ) * Real.sin (weight i * phase i x / τ)) •
          phaseRankOneHessian (phase i) (amplitude i) x +
      actualProbeSinRemainder δ τ (weight i) (phase i) (amplitude i) x := by
  rw [(hasFDerivAt_actualFiniteProbeHessian label δ τ weight phase amplitude u x
    hphase hamplitude).fderiv, probePairedColumnMap_sin_column]
  exact actualProbeSinColumn_hessian_at (hphase i) (hamplitude i) δ τ (weight i) hτ hw

#print axioms actualFiniteProbeDisplacement_iteratedFDeriv
#print axioms hasFDerivAt_actualFiniteProbeSpatialJet
#print axioms actualFiniteProbeHessian_cos_response
#print axioms actualFiniteProbeHessian_sin_response
end GlobalEmbedding.Offline
