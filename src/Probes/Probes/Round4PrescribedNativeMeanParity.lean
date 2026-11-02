import Probes.Round4PrescribedGlobalParity

/-!
# The complete chart-extended prescribed mean as a native tensor field

This is the original opposite-phase quadratic expression in the actual native
coefficient maps of the complete amplitudes. Its evenness is derived from the
original finite solver, and holds as equality of entire fields. Identification
with the entire zero-germ selector additionally requires the genuine phase
noncriticality; it is not asserted by the algebraic parity theorem below.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set
open scoped ContDiff BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N p r : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Pspace" => Fin p → ℝ

/-- The same native opposite-phase mean, without replacing spatial derivatives
by pointwise coefficient surrogates. -/
def round4NativeOppositeMean
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ)
    (R Q : Fin r → Ep × M → V)
    (b : Ep) (x : M) : LinearMap.BilinForm ℝ (TangentSpace I x) :=
  (1/2 : ℝ) • ∑ l,
    (LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) false (phi l) tau (R l) (Q l) (b,x)).toLinearMap +
    LinearMap.BilinForm.comp (innerₗ V)
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap
      (round4PrescribedNativeCoefficient (I := I) true (phi l) tau (R l) (Q l) (b,x)).toLinearMap)

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
theorem round4NativeOppositeMean_neg
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V) :
    round4NativeOppositeMean (I := I) phi tau (-R) (-Q) =
      round4NativeOppositeMean (I := I) phi tau R Q := by
  funext b x
  ext v w
  simp only [round4NativeOppositeMean,Pi.neg_apply,round4PrescribedNativeCoefficient_neg]
  simp

omit [IsManifold I ∞ M] [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] in
theorem round4NativeOppositeMean_isSymm
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (R Q : Fin r → Ep × M → V)
    (b : Ep) (x : M) :
    (round4NativeOppositeMean (I := I) phi tau R Q b x).IsSymm := by
  constructor
  intro v w
  simp only [round4NativeOppositeMean,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.add_apply,LinearMap.BilinForm.comp_apply,ContinuousLinearMap.coe_coe,
    innerₗ_apply_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [real_inner_comm]
  congr 1
  exact real_inner_comm _ _

/-- The literal opposite mean of the actual prescribed global amplitudes. -/
def round4PrescribedNativeMean
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D)) (u : Pspace) :
    (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x) :=
  round4NativeOppositeMean (I := I) phi tau
    (fun l => round4PrescribedGlobalAmplitude false label l F hF (c l) (vf l) tau length (a l) u)
    (fun l => round4PrescribedGlobalAmplitude true label l F hF (c l) (vf l) tau length (a l) u)

theorem round4PrescribedNativeMean_even
    (label : (Fin r × Bool) ↪ Fin p)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c l b x))
    (phi : Fin r → Ep × M → ℝ) (tau : ℝ) (length : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
    (hA : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hB : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c l z.1) z.2) (a l).target)
    (hBR : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c l z.1) z.2 0 i : V)) (a l).target)
    (hvf : ∀ l, ContDiffOn ℝ ∞ (fun z : Ep × D => (vf l z.1 z.2 : V)) (a l).target)
    (u : Pspace) :
    round4PrescribedNativeMean label F hF c vf phi tau length a (-u) =
      round4PrescribedNativeMean label F hF c vf phi tau length a u := by
  unfold round4PrescribedNativeMean
  have hneg (ch : Bool) :
      (fun l => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) (-u)) =
        -(fun l => round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau length (a l) u) := by
    funext l
    exact round4PrescribedGlobalAmplitude_neg ch label l F hF (c l) (vf l) tau length (a l)
      (hA l) (hB l) (hBR l) (hvf l) u
  rw [hneg false,hneg true,round4NativeOppositeMean_neg]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4NativeOppositeMean_neg
#print axioms GlobalEmbedding.Continuation.round4NativeOppositeMean_isSymm
#print axioms GlobalEmbedding.Continuation.round4PrescribedNativeMean_even
