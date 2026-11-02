import GlobalEmbedding.Paper.CollarAnalyticUnitNormal
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Actual ambient Hopf coefficients of an analytic observable

Source: `main.tex`, prop:collar, lines522–534.
DAG: `collar-ambient-hopf-source-coefficients`; exclusive owner W2.
Only the previously proved literal ambient action is named. Original orbit
derivatives, first/sortedsecond indices, cofactor order and Gram are reused.
-/

noncomputable section
open Matrix
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A transparent name for the exact ambient exponential expression already
proved analytic in CollarNativeAnalyticHopfAction. Source: prop:collar, lines522–534. -/
def collarAmbientHopfAction {a : ℕ} (C : Fin a → ℕ) (y : Fin a → ℝ)
    (p : FreeHopfAmbientSpace C) : FreeHopfAmbientSpace C :=
  fun i ↦ Complex.exp ((2 * Real.pi * y i : ℝ) * Complex.I) • p i

/-- The named actual expression has its previously proved joint analytic regularity.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfAction_contDiff {a : ℕ} (C : Fin a → ℕ) :
    ContDiff ℝ ω (fun q : (Fin a → ℝ) × FreeHopfAmbientSpace C ↦
      collarAmbientHopfAction C q.1 q.2) :=
  collarHopfAmbientAction_contDiff_omega C

/-- The SAME ambient expression restricts to the original native action.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfAction_inclusion {a : ℕ} (C : Fin a → ℕ)
    (y : Fin a → ℝ) (x : FreeHopfProduct C) :
    collarAmbientHopfAction C y (freeHopfAmbientInclusion C x) =
      freeHopfAmbientInclusion C (freeHopfRealAction C y x) :=
  collarHopfAmbientAction_inclusion C y x

/-- Actual integer shifts preserve the ambient expression even at zero vectors.
Use Mathlib's original period-2pi complex-circle exponential identity.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfAction_integer_periodic {a : ℕ} (C : Fin a → ℕ)
    (p : FreeHopfAmbientSpace C) (y : Fin a → ℝ) (m : Fin a → ℤ) :
    collarAmbientHopfAction C (fun i ↦ y i + (m i : ℝ)) p =
      collarAmbientHopfAction C y p := by
  funext i
  change (Circle.exp (2 * Real.pi * (y i + (m i : ℝ))) : ℂ) • p i =
    (Circle.exp (2 * Real.pi * y i) : ℂ) • p i
  rw [mul_add, Circle.exp_add, Circle.exp_two_pi_mul_int, mul_one]

/-- The actual individual ambient flow is the literal factor-time restriction
of that same ambient expression. Source: prop:collar, lines522–534. -/
def collarAmbientHopfFlow {a : ℕ} (C : Fin a → ℕ) (i : Fin a) (t : ℝ)
    (p : FreeHopfAmbientSpace C) : FreeHopfAmbientSpace C :=
  collarAmbientHopfAction C (fun j ↦ if j = i then t else 0) p

/-- The actual original factor flow is the restriction of the SAME ambient flow.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfFlow_inclusion {a : ℕ} (C : Fin a → ℕ)
    (i : Fin a) (t : ℝ) (x : FreeHopfProduct C) :
    collarAmbientHopfFlow C i t (freeHopfAmbientInclusion C x) =
      freeHopfAmbientInclusion C (freeHopfProductFlow C i t x) :=
  collarAmbientHopfAction_inclusion C _ x

/-- Each actual ambient factor flow is jointly analytic by real linear time insertion.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfFlow_contDiff {a : ℕ} (C : Fin a → ℕ) (i : Fin a) :
    ContDiff ℝ ω (fun q : ℝ × FreeHopfAmbientSpace C ↦
      collarAmbientHopfFlow C i q.1 q.2) := by
  have ht : ContDiff ℝ ω (fun t : ℝ ↦ fun j : Fin a ↦ if j = i then t else 0) := by
    apply contDiff_pi.mpr
    intro j
    split_ifs
    · exact contDiff_id
    · exact contDiff_const
  have hp : ContDiff ℝ ω (fun q : ℝ × FreeHopfAmbientSpace C ↦
      ((fun j : Fin a ↦ if j = i then q.1 else 0), q.2)) :=
    (ht.comp contDiff_fst).prodMk contDiff_snd
  simpa only [collarAmbientHopfFlow, Function.comp_def] using
    (collarAmbientHopfAction_contDiff C).comp hp

/-- The actual first ambient orbit derivative of an analytic F is analytic.
Use the accepted genuine time-parameter derivative theorem at omega.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfDeriv_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (i : Fin a) : ContDiff ℝ ω (orbitDeriv (collarAmbientHopfFlow C i) F) := by
  have hg := hF.comp ((collarAmbientHopfFlow_contDiff C i).comp
    (contDiff_snd.prodMk contDiff_fst))
  have hgm : ContMDiff (𝓘(ℝ, FreeHopfAmbientSpace C).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω
      (fun q : FreeHopfAmbientSpace C × ℝ ↦ F (collarAmbientHopfFlow C i q.2 q.1)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    simpa only [Function.comp_def] using hg.contMDiff
  change ContDiff ℝ ω (fun p ↦ deriv (fun t : ℝ ↦ F (collarAmbientHopfFlow C i t p)) 0)
  exact (collar_parametric_deriv_zero_omega _ hgm).contDiff

/-- All actual first/sortedsecond ambient columns are analytic, with the original
index and literal derivative operation. Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfColumns_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (k : BalancedPairingIndex a) :
    ContDiff ℝ ω (fun p ↦ freeFlowColumns (collarAmbientHopfFlow C) F p k) := by
  cases k with
  | inl i => exact collarAmbientHopfDeriv_contDiff C F hF i
  | inr ij =>
    exact collarAmbientHopfDeriv_contDiff C _
      (collarAmbientHopfDeriv_contDiff C F hF ij.val.2) ij.val.1

/-- Actual first ambient and native derivatives agree on the original inclusion.
This follows from equality of the actual time curves, with no regularity premise.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfDeriv_inclusion {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (i : Fin a) (x : FreeHopfProduct C) :
    orbitDeriv (collarAmbientHopfFlow C i) F (freeHopfAmbientInclusion C x) =
      freeHopfDeriv C i (F ∘ freeHopfAmbientInclusion C) x := by
  change deriv (fun t : ℝ ↦ F (collarAmbientHopfFlow C i t
    (freeHopfAmbientInclusion C x))) 0 = _
  apply congrArg (fun f : ℝ → EuclideanSpace ℝ (Fin N) ↦ deriv f 0)
  funext t
  exact congrArg F (collarAmbientHopfFlow_inclusion C i t x)

/-- Every original ambient first/sortedsecond column restricts to the SAME original
native free column of H=F composed with inclusion. Apply the real curve identity
once or twice, retaining the exact original ordering.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfColumns_inclusion {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (x : FreeHopfProduct C) (k : BalancedPairingIndex a) :
    freeFlowColumns (collarAmbientHopfFlow C) F (freeHopfAmbientInclusion C x) k =
      freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x k := by
  cases k with
  | inl i => exact collarAmbientHopfDeriv_inclusion C F i x
  | inr ij =>
    change orbitDeriv (collarAmbientHopfFlow C ij.val.1)
      (orbitDeriv (collarAmbientHopfFlow C ij.val.2) F) (freeHopfAmbientInclusion C x) =
      freeHopfDeriv C ij.val.1 (freeHopfDeriv C ij.val.2 (F ∘ freeHopfAmbientInclusion C)) x
    have he : (orbitDeriv (collarAmbientHopfFlow C ij.val.2) F) ∘
        freeHopfAmbientInclusion C = freeHopfDeriv C ij.val.2 (F ∘ freeHopfAmbientInclusion C) :=
      funext (fun y ↦ collarAmbientHopfDeriv_inclusion C F ij.val.2 y)
    rw [collarAmbientHopfDeriv_inclusion, he]

/-- The actual row-coordinate pairing matrix, using the SAME existing enumeration
of first and sorted second columns. Source: prop:collar, lines522–534. -/
def collarAmbientHopfPairingMatrix {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (p : FreeHopfAmbientSpace C) :
    Matrix (Fin (freeSymmetricColumnCount a + a)) (Fin N) ℝ :=
  fun r j ↦ freeFlowColumns (collarAmbientHopfFlow C) F p
    ((freeCofactorColumnOrder a).symm r) j

/-- The actual OLD first-derivative Gram defect is literally Gamma(F)-I.
No sign or packing for the balanced source forcing is asserted here.
Source: prop:collar, lines522–534. -/
def collarAmbientHopfMetricDefect {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (p : FreeHopfAmbientSpace C) :
    Matrix (Fin a) (Fin a) ℝ :=
  Matrix.gram ℝ (fun i ↦ orbitDeriv (collarAmbientHopfFlow C i) F p) - 1

/-- The actual ambient pairing matrix is analytic in the whole ambient parameter.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (collarAmbientHopfPairingMatrix C F) := by
  apply contDiff_pi.mpr
  intro r
  apply contDiff_pi.mpr
  intro j
  exact (EuclideanSpace.proj j).contDiff.comp
    (collarAmbientHopfColumns_contDiff C F hF _)

/-- The literal old Gram defect is analytic, derived from the actual first columns.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfMetricDefect_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (collarAmbientHopfMetricDefect C F) := by
  apply ContDiff.sub _ contDiff_const
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (collarAmbientHopfDeriv_contDiff C F hF i).inner ℝ
    (collarAmbientHopfDeriv_contDiff C F hF j)

/-- The actual T_F(A_y p) is jointly analytic in ambient p and all real times y.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_joint_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (fun q : FreeHopfAmbientSpace C × (Fin a → ℝ) ↦
      collarAmbientHopfPairingMatrix C F (collarAmbientHopfAction C q.2 q.1)) := by
  simpa only [Function.comp_def] using (collarAmbientHopfPairingMatrix_contDiff C F hF).comp
    ((collarAmbientHopfAction_contDiff C).comp (contDiff_snd.prodMk contDiff_fst))

/-- The SAME old Gram defect along the actual action is jointly analytic.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfMetricDefect_joint_contDiff {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F) :
    ContDiff ℝ ω (fun q : FreeHopfAmbientSpace C × (Fin a → ℝ) ↦
      collarAmbientHopfMetricDefect C F (collarAmbientHopfAction C q.2 q.1)) := by
  simpa only [Function.comp_def] using (collarAmbientHopfMetricDefect_contDiff C F hF).comp
    ((collarAmbientHopfAction_contDiff C).comp (contDiff_snd.prodMk contDiff_fst))

/-- Both actual finite coefficient matrices are genuinely real analytic at every
joint parameter, not only smooth. Source: prop:collar, lines522–534. -/
theorem collarAmbientHopf_source_analyticAt {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (q : FreeHopfAmbientSpace C × (Fin a → ℝ)) :
    AnalyticAt ℝ (fun q : FreeHopfAmbientSpace C × (Fin a → ℝ) ↦
      collarAmbientHopfPairingMatrix C F (collarAmbientHopfAction C q.2 q.1)) q ∧
    AnalyticAt ℝ (fun q : FreeHopfAmbientSpace C × (Fin a → ℝ) ↦
      collarAmbientHopfMetricDefect C F (collarAmbientHopfAction C q.2 q.1)) q :=
  ⟨(collarAmbientHopfPairingMatrix_joint_contDiff C F hF).contDiffAt.analyticAt,
    (collarAmbientHopfMetricDefect_joint_contDiff C F hF).contDiffAt.analyticAt⟩

/-- Integer-periodicity of T_F(A_y p) follows from the actual ambient action,
including every ambient base parameter. Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_integer_periodic {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (p : FreeHopfAmbientSpace C) (y : Fin a → ℝ) (m : Fin a → ℤ) :
    collarAmbientHopfPairingMatrix C F
        (collarAmbientHopfAction C (fun i ↦ y i + (m i : ℝ)) p) =
      collarAmbientHopfPairingMatrix C F (collarAmbientHopfAction C y p) :=
  congrArg (collarAmbientHopfPairingMatrix C F)
    (collarAmbientHopfAction_integer_periodic C p y m)

/-- Integer-periodicity of the SAME old Gram defect along the actual ambient action.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfMetricDefect_integer_periodic {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (p : FreeHopfAmbientSpace C) (y : Fin a → ℝ) (m : Fin a → ℤ) :
    collarAmbientHopfMetricDefect C F
        (collarAmbientHopfAction C (fun i ↦ y i + (m i : ℝ)) p) =
      collarAmbientHopfMetricDefect C F (collarAmbientHopfAction C y p) :=
  congrArg (collarAmbientHopfMetricDefect C F)
    (collarAmbientHopfAction_integer_periodic C p y m)

/-- Actual matrix row coordinates at the inclusion are EXACTLY the original
native first/sortedsecond columns, with the original accepted enumeration.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_inclusion {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C)
    (r : Fin (freeSymmetricColumnCount a + a)) (j : Fin N) :
    collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x) r j =
      freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x
        ((freeCofactorColumnOrder a).symm r) j :=
  congrArg (fun v : EuclideanSpace ℝ (Fin N) ↦ v j)
    (collarAmbientHopfColumns_inclusion C F x _)

/-- The ambient old Gram defect restricts to the literal original native Gram
minus identity, without a sign or source-packing convention.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfMetricDefect_inclusion {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (x : FreeHopfProduct C) :
    collarAmbientHopfMetricDefect C F (freeHopfAmbientInclusion C x) =
      Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i (F ∘ freeHopfAmbientInclusion C) x) - 1 :=
  congrArg (fun v : Fin a → EuclideanSpace ℝ (Fin N) ↦ Matrix.gram ℝ v - 1)
    (funext (fun i ↦ collarAmbientHopfDeriv_inclusion C F i x))

/-- Multiplication by the actual matrix row is exactly the existing original
balanced pairing coordinate, under the SAME accepted enumeration. Thus the
coefficient matrix pairs with the true native generator derivatives of H.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_pairing {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (hF : ContDiff ℝ ω F)
    (x : FreeHopfProduct C) (u : EuclideanSpace ℝ (Fin N))
    (r : Fin (freeSymmetricColumnCount a + a)) :
    (collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x)).mulVec
        (fun j ↦ u j) r =
      balancedPairingMap (F ∘ freeHopfAmbientInclusion C) (freeHopfGenerator C) x u
        ((freeCofactorColumnOrder a).symm r) := by
  have hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞
      (F ∘ freeHopfAmbientInclusion C) :=
    (hF.of_le (by simp)).contMDiff.comp (freeHopfAmbientInclusion_contMDiff C)
  change (∑ j, collarAmbientHopfPairingMatrix C F (freeHopfAmbientInclusion C x) r j * u j) =
    inner ℝ (balancedPairingColumns (F ∘ freeHopfAmbientInclusion C)
      (freeHopfGenerator C) x ((freeCofactorColumnOrder a).symm r)) u
  rw [freeHopf_balanced_pairing_columns C _ hH x, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [collarAmbientHopfPairingMatrix_inclusion]
  exact mul_comm _ _

/-- The actual row Gram is the Gram of the SAME ordered ambient columns.
This elementary coordinate identity identifies the matrix used by the existing
analytic inverse chain. Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_gram {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N)) (p : FreeHopfAmbientSpace C) :
    collarAmbientHopfPairingMatrix C F p * (collarAmbientHopfPairingMatrix C F p)ᵀ =
      Matrix.gram ℝ (fun r ↦ freeFlowColumns (collarAmbientHopfFlow C) F p
        ((freeCofactorColumnOrder a).symm r)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial,
    collarAmbientHopfPairingMatrix]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The actual matrix Gram determinant is nonzero on EVERY real-time point of
the original included base fiber whenever the SAME native H has free columns.
No determinant, inverse, analytic-column or smallness premise is supplied.
This conditional rank input is later discharged by actual free-margin persistence.
Source: prop:collar, lines522–534. -/
theorem collarAmbientHopfPairingMatrix_fiber_det_ne_zero {a N : ℕ} (C : Fin a → ℕ)
    (F : FreeHopfAmbientSpace C → EuclideanSpace ℝ (Fin N))
    (hfree : ∀ x, LinearIndependent ℝ
      (freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C) x))
    (x : FreeHopfProduct C) (y : Fin a → ℝ) :
    (collarAmbientHopfPairingMatrix C F
        (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x)) *
      (collarAmbientHopfPairingMatrix C F
        (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x)))ᵀ).det ≠ 0 := by
  rw [collarAmbientHopfPairingMatrix_gram]
  have he : (fun r : Fin (freeSymmetricColumnCount a + a) ↦
      freeFlowColumns (collarAmbientHopfFlow C) F
        (collarAmbientHopfAction C y (freeHopfAmbientInclusion C x))
        ((freeCofactorColumnOrder a).symm r)) =
      (fun r ↦ freeFlowColumns (freeHopfProductFlow C) (F ∘ freeHopfAmbientInclusion C)
        (freeHopfRealAction C y x) ((freeCofactorColumnOrder a).symm r)) := by
    funext r
    rw [collarAmbientHopfAction_inclusion]
    exact collarAmbientHopfColumns_inclusion C F _ _
  rw [he]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    ((hfree (freeHopfRealAction C y x)).comp _ (freeCofactorColumnOrder a).symm.injective)

end GlobalEmbedding.Paper
