import Probes.Round4ActualProbeBackgroundIteration
import Probes.Round4PrescribedGlobalWave
import Probes.ActualSecondaryCompleteMetricIdentity

/-! The real background wave and the complete prescribed sine/cosine probe
are assembled in one original primary array. The amplitudes include their
actual chart extensions. The disjoint labels preserve all mixed nonzero
quadratic forcing records; the selected opposite mean splits exactly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Pspace" => Fin p → ℝ

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
/-- The actual spatial differential commutes with constant physical scaling. -/
theorem round4Parameter_global_spatial_derivative_smul
    (f : Ep × M → V) (z : Ep × M) (delta : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ,V) (fun x => f (z.1,x)) z.2) :
    incrementsGlobalSpatialDerivative (I := I) (fun w => delta • f w) z =
      delta • incrementsGlobalSpatialDerivative (I := I) f z := by
  change mvfderiv I (fun x => delta • f (z.1,x)) z.2 =
    delta • mvfderiv I (fun x => f (z.1,x)) z.2
  have h := mvfderiv_fun_smul (I := I) (mdifferentiableAt_const (c := delta)) hf
  simpa [mvfderiv,mfderiv_const,Pi.smul_def] using h

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
/-- Both real channels scale by the same physical delta, with their actual
native derivatives and original phase retained. -/
theorem round4Parameter_native_coefficient_smul
    (imag : Bool) (phi : Ep × M → ℝ) (tau delta : ℝ)
    (R Q : Ep × M → V) (z : Ep × M)
    (hR : MDifferentiableAt I 𝓘(ℝ,V) (fun x => R (z.1,x)) z.2)
    (hQ : MDifferentiableAt I 𝓘(ℝ,V) (fun x => Q (z.1,x)) z.2) :
    round4PrescribedNativeCoefficient (I := I) imag phi tau
      (fun w => delta • R w) (fun w => delta • Q w) z =
      delta • round4PrescribedNativeCoefficient (I := I) imag phi tau R Q z := by
  cases imag <;> simp only [round4PrescribedNativeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  · rw [round4Parameter_global_spatial_derivative_smul R z delta hR]
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.smulRight_apply,smul_sub,smul_smul,mul_comm,mul_assoc]
  · rw [round4Parameter_global_spatial_derivative_smul Q z delta hQ]
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.smulRight_apply,smul_add,smul_smul,mul_comm,mul_assoc]

variable
    (F : Ep → M → EuclideanSpace ℝ (Fin N)) (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : Fin r → Ep → EuclideanSpace ℝ (Fin (m+1)) → M)
    (vf : (l : Fin r) → (b : Ep) → (x : EuclideanSpace ℝ (Fin (m+1))) → normalSpace (I := I) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × EuclideanSpace ℝ (Fin (m+1))))

/-- One actual amplitude array, with background and prescribed modes kept
as distinct primary labels. `imag=false` is the real reconstruction channel. -/
def round4ParameterProbeCombinedAmplitude
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (imag : Bool) : (Λ ⊕ Fin r) → Ep × M → V :=
  Sum.elim
    (fun nu z => delta • incrementsGlobalPrimaryAmplitude F hF g input backgroundLength tau (!imag) nu z)
    (fun l => round4PrescribedGlobalAmplitude imag label l F hF (c l) (vf l) tau probeLength (a l) u)

/-- The literal common phase-array wave, before any quadratic cancellation. -/
def round4ParameterProbeCombinedPrimary
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (z : Ep × M) : V :=
  let phi := Sum.elim g.phase phase
  let R := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
  let Q := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
  ∑ l, (Real.cos (phi l z/tau) • R l z - Real.sin (phi l z/tau) • Q l z)

omit [NormedSpace ℝ Ep] in
/-- The common array is exactly physical background plus the complete actual
probe, rather than just the leading trigonometric approximation. -/
theorem round4ParameterProbeCombinedPrimary_eq
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (z : Ep × M) :
    round4ParameterProbeCombinedPrimary F hF g label c vf phase tau delta backgroundLength probeLength a input u z =
      delta • incrementsGlobalPrimaryWave F hF g input backgroundLength tau z +
        round4PrescribedGlobalWave label F hF c vf phase tau probeLength a u z := by
  simp only [round4ParameterProbeCombinedPrimary,Fintype.sum_sum_type,
    round4ParameterProbeCombinedAmplitude,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    incrementsGlobalPrimaryWave,round4PrescribedGlobalWave,Finset.smul_sum,smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro nu _
  rw [smul_comm (Real.cos _),smul_comm (Real.sin _)]

/-- The actual selected native opposite mean for that same common array. -/
def round4ParameterProbeCombinedMean
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (b : Ep) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  let phi := Sum.elim g.phase phase
  let R := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u false
  let Q := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta backgroundLength probeLength a input u true
  (1/2 : ℝ) • ∑ l,
    (LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap)

/-- The same selected mean is physical background mean plus the entire
prescribed native mean. No cross term is discarded from the full metric:
cross-label terms belong to the nonzero secondary records. -/
theorem round4ParameterProbeCombinedMean_eq
    (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (u : Pspace) (b : Ep) (x : M)
    (hamp : ∀ nu ch, MDifferentiableAt I 𝓘(ℝ,V)
      (fun y => incrementsGlobalPrimaryAmplitude F hF g input backgroundLength tau ch nu (b,y)) x) :
    round4ParameterProbeCombinedMean F hF g label c vf phase tau delta backgroundLength probeLength a input u b x =
      delta^2 • incrementsGlobalPrimaryMean F hF g input backgroundLength tau b x +
        round4PrescribedNativeMean label F hF c vf phase tau probeLength a u b x := by
  have hcoef (imag : Bool) (nu : Λ) :
      round4PrescribedNativeCoefficient (I := I) imag (g.phase nu) tau
        (fun z => delta • incrementsGlobalPrimaryAmplitude F hF g input backgroundLength tau true nu z)
        (fun z => delta • incrementsGlobalPrimaryAmplitude F hF g input backgroundLength tau false nu z) (b,x) =
      delta • incrementsGlobalPrimaryCoefficient F hF g input backgroundLength tau (!imag) nu (b,x) := by
    rw [round4Parameter_native_coefficient_smul imag (g.phase nu) tau delta _ _ (b,x)
      (hamp nu true) (hamp nu false)]
    congr 1
    cases imag <;> rfl
  simp only [round4ParameterProbeCombinedMean,round4ParameterProbeCombinedAmplitude,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Bool.not_false,Bool.not_true,
    smul_add,hcoef]
  change (1/2 : ℝ) • (∑ nu : Λ, _) +
    round4PrescribedNativeMean label F hF c vf phase tau probeLength a u b x = _
  congr 1
  ext v w
  simp only [incrementsGlobalPrimaryMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_apply,real_inner_smul_left,real_inner_smul_right,smul_eq_mul,
    Finset.mul_sum,mul_add]
  apply Finset.sum_congr rfl
  intro nu _
  ring

/-- Substituting the actual background iterate in the common primary
array gives the exact same physical mean residual, as an equality of whole
native tensor fields. Both probe channels retain their reconstructed terms. -/
theorem round4ParameterProbeCombinedMean_actual_iterate_residual
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (hdelta : delta ≠ 0) (j : ℕ) (u : Pspace)
    (hamp : ∀ b x nu ch, MDifferentiableAt I 𝓘(ℝ,V)
      (fun y => incrementsGlobalPrimaryAmplitude F hF g
        (round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target
          (round4PrescribedNativeMean label F hF c vf phase tau probeLength a) (j+1) u)
        backgroundLength tau ch nu (b,y)) x) :
    let probe := round4PrescribedNativeMean label F hF c vf phase tau probeLength a
    let A := round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target probe
    (fun b x => round4ParameterProbeCombinedMean F hF g label c vf phase tau delta
      backgroundLength probeLength a (A (j+1) u) u b x) - delta^2 • target =
      delta^2 • (incrementsGlobalPrimaryMeanError F hF g (A (j+1) u) backgroundLength tau -
        incrementsGlobalPrimaryMeanError F hF g (A j u) backgroundLength tau) := by
  intro probe A
  have hid := round4ActualBackgroundMeanIterate_physical_residual F hF g
    backgroundLength tau delta hdelta target probe j u
  have hmean : (fun b x => round4ParameterProbeCombinedMean F hF g label c vf phase tau delta
      backgroundLength probeLength a (A (j+1) u) u b x) =
      delta^2 • (fun b x => incrementsGlobalPrimaryMean F hF g (A (j+1) u) backgroundLength tau b x) + probe u := by
    funext b x
    exact round4ParameterProbeCombinedMean_eq F hF g label c vf phase tau delta backgroundLength probeLength a
      (A (j+1) u) u b x (hamp b x)
  rw [hmean]
  exact hid

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4Parameter_global_spatial_derivative_smul
#print axioms GlobalEmbedding.Continuation.round4Parameter_native_coefficient_smul
#print axioms GlobalEmbedding.Continuation.round4ParameterProbeCombinedPrimary_eq
#print axioms GlobalEmbedding.Continuation.round4ParameterProbeCombinedMean_eq
#print axioms GlobalEmbedding.Continuation.round4ParameterProbeCombinedMean_actual_iterate_residual
