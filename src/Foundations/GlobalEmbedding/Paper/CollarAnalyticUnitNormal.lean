import GlobalEmbedding.Paper.CollarNativeAnalyticHopfAction
import GlobalEmbedding.Paper.FreeHopfUnitComplements

/-!
# The actual analytic oriented unit normal of analytic free Hopf columns

Source: `main.tex`, prop:collar, lines532–536.
DAG: `collar-analytic-unit-normal`; exclusive bounded proof owner W2.
Reuse: the existing native parameter-derivative proof and exact ordered-cofactor
formula, together with its accepted nonzero/unit/perpendicular specifications.
Only the genuinely missing omega regularity and original-H specialization are added.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

section ParameterDerivative

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine native analytic family of real curves has an analytic actual
derivative at zero. Reuse the accepted parameter-derivative proof with Mathlib's
arbitrary-order native mfderiv theorem at omega; no regularity of that derivative
is assumed. Source: the analytic free columns in prop:collar, lines532–536. -/
theorem collar_parametric_deriv_zero_omega (G : M × ℝ → F)
    (hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ω G) :
    ContMDiff I 𝓘(ℝ, F) ω (fun x ↦ deriv (fun t : ℝ ↦ G (x, t)) 0) := by
  intro x
  have hd := (hG (x, 0)).mfderiv (fun x t ↦ G (x, t)) (fun _ : M ↦ (0 : ℝ))
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ω (fun _ : M ↦ (0 : ℝ)) x)
    (show (ω : ℕ∞ω) + 1 ≤ ω by simp)
  have heq : inTangentCoordinates 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun _ : M ↦ (0 : ℝ))
      (fun y ↦ G (y, 0))
      (fun y ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun t : ℝ ↦ G (y, t)) 0) x =
      (fun y ↦ fderiv ℝ (fun t : ℝ ↦ G (y, t)) 0) := by
    funext y
    rw [inTangentCoordinates_eq_mfderiv_comp (by simp) (by simp)]
    simp only [mfld_simps, mvfderiv, mfderiv_eq_fderiv, mfderivWithin_eq_fderivWithin,
      fderivWithin_univ, fderiv_id]
    ext
    rfl
  rw [heq] at hd
  exact hd.clm_apply
    (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ω (fun _ : M ↦ (1 : ℝ)) x)

end ParameterDerivative

/-- The SAME original individual Hopf factor flow is jointly native analytic.
Compose the accepted actual analytic product action with the real linear
factor-time insertion; no new flow is defined. Source: prop:collar, lines532–536. -/
theorem collarHopfProductFlow_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (i : Fin a) :
    ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C)) (freeHopfModel C) ω
      (fun p : ℝ × FreeHopfProduct C ↦ freeHopfProductFlow C i p.1 p.2) := by
  have ht : ContDiff ℝ ω (fun t : ℝ ↦ fun j : Fin a ↦ if j = i then t else 0) := by
    apply contDiff_pi.mpr
    intro j
    split_ifs
    · exact contDiff_id
    · exact contDiff_const
  have hp : ContMDiff (𝓘(ℝ, ℝ).prod (freeHopfModel C))
      (𝓘(ℝ, Fin a → ℝ).prod (freeHopfModel C)) ω
      (fun p : ℝ × FreeHopfProduct C ↦
        ((fun j : Fin a ↦ if j = i then p.1 else 0), p.2)) :=
    (ht.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  simpa only [freeHopfProductFlow, Function.comp_def] using
    (collarHopfRealAction_omega C).comp hp

/-- An actual native analytic observable has actual analytic first Hopf
derivatives, by differentiating the SAME analytic action in its real time.
Source: prop:collar, lines532–536. -/
theorem collarHopfDeriv_omega {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F)
      (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ω f) (i : Fin a) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ω (freeHopfDeriv C i f) := by
  have : IsManifold (freeHopfModel C) ω (FreeHopfProduct C) :=
    collarHopfProduct_native_omega C
  have hs : ContMDiff ((freeHopfModel C).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (freeHopfModel C)) ω
      (fun p : FreeHopfProduct C × ℝ ↦ (p.2, p.1)) :=
    contMDiff_snd.prodMk contMDiff_fst
  have hg := hf.comp ((collarHopfProductFlow_omega C i).comp hs)
  change ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ω
    (fun x ↦ deriv (fun t : ℝ ↦ f (freeHopfProductFlow C i t x)) 0)
  simpa only [Function.comp_def] using
    collar_parametric_deriv_zero_omega _ hg

/-- All original first and once-indexed sorted second columns of analytic H are
native analytic. Differentiate the original observable once or twice according
to the SAME original index; no analytic-column hypothesis is added.
Source: prop:collar, lines532–536. -/
theorem collarHopf_free_columns_omega {a N : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)] (H : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
    (hH : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω H)
    (k : BalancedPairingIndex a) :
    ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ω
      (fun x ↦ freeFlowColumns (freeHopfProductFlow C) H x k) := by
  cases k with
  | inl i => exact collarHopfDeriv_omega C H hH i
  | inr ij =>
    exact collarHopfDeriv_omega C _ (collarHopfDeriv_omega C H hH ij.val.2) ij.val.1

section OrderedCofactor

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)

/-- The existing ordered cofactor is native analytic in analytic columns. Reuse
its actual continuous multilinear volume contraction and inverse real Riesz
isometry, at omega. No new cofactor formula is introduced.
Source: prop:collar, the normalized oriented cofactor at line536. -/
theorem collarOrderedCofactor_omega (d : ℕ) {v : M → Fin d → FreeCofactorSpace d}
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ω (fun x ↦ v x i)) :
    ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ω (fun x ↦ freeOrderedCofactor d (v x)) := by
  let R : StrongDual ℝ (FreeCofactorSpace d) →L[ℝ] FreeCofactorSpace d :=
    (InnerProductSpace.toDual ℝ (FreeCofactorSpace d)).symm.toLinearIsometry.toContinuousLinearMap
  apply R.contMDiff.comp
  exact ((freeOrderedVolume d).toContinuousMultilinearMap.curryRight.contDiff.contMDiff).comp
    (contMDiff_pi_module_iff.mpr hv)

/-- The SAME existing unit-complement formula is analytic. Its actual cofactor
is nonzero by the accepted linear-independence specification, so the true real
norm inverse is analytic. Unit/perpendicular algebra is reused separately.
Source: prop:collar, the normalized oriented cofactor at line536. -/
theorem collarOrderedUnitComplement_omega (d : ℕ) {v : M → Fin d → FreeCofactorSpace d}
    (hv : ∀ i, ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ω (fun x ↦ v x i))
    (hind : ∀ x, LinearIndependent ℝ (v x)) :
    ContMDiff I 𝓘(ℝ, FreeCofactorSpace d) ω
      (fun x ↦ freeOrderedUnitComplement d (v x)) := by
  have hc := collarOrderedCofactor_omega I d hv
  have hn : ContMDiff I 𝓘(ℝ, ℝ) ω (fun x ↦ ‖freeOrderedCofactor d (v x)‖) := by
    intro x
    exact (contDiffAt_norm ℝ (freeOrderedCofactor_ne_zero d (v x) (hind x))).comp_contMDiffAt
      (f := fun y : M ↦ freeOrderedCofactor d (v y)) (hc x)
  exact (hn.inv₀ (fun x ↦ norm_ne_zero_iff.mpr
    (freeOrderedCofactor_ne_zero d (v x) (hind x)))).smul hc

end OrderedCofactor

/-- From the original analytic H and its actual independent free columns,
construct the actual analytic unit normal in the exact original codimension-one
target. It is explicitly the SAME existing ordered unit complement under the
accepted enumeration, and is perpendicular to every original first/sortedsecond
column. All column analyticity is proved internally from H and the true action.
Source: prop:collar, analytic H and normalized oriented cofactor at line536. -/
theorem collarHopf_analytic_unit_normal {a : ℕ} (C : Fin a → ℕ)
    [∀ i, Fact (0 < C i)]
    (H : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hH : ContMDiff (freeHopfModel C)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ω H)
    (hfree : ∀ x, LinearIndependent ℝ (freeFlowColumns (freeHopfProductFlow C) H x)) :
    ∃ ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)),
      (∀ x, ν x = freeOrderedUnitComplement (freeSymmetricColumnCount a + a)
        (fun i ↦ freeFlowColumns (freeHopfProductFlow C) H x
          ((freeCofactorColumnOrder a).symm i))) ∧
      ContMDiff (freeHopfModel C)
        𝓘(ℝ, EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) ω ν ∧
      (∀ x, ‖ν x‖ = 1) ∧
      (∀ x k, inner ℝ (ν x) (freeFlowColumns (freeHopfProductFlow C) H x k) = 0) := by
  let v := fun x i ↦ freeFlowColumns (freeHopfProductFlow C) H x
    ((freeCofactorColumnOrder a).symm i)
  have hind (x : FreeHopfProduct C) : LinearIndependent ℝ (v x) :=
    (hfree x).comp _ (freeCofactorColumnOrder a).symm.injective
  refine ⟨fun x ↦ freeOrderedUnitComplement (freeSymmetricColumnCount a + a) (v x),
    fun _ ↦ rfl, ?_, ?_, ?_⟩
  · exact collarOrderedUnitComplement_omega (freeHopfModel C) _
      (fun i ↦ collarHopf_free_columns_omega C H hH _) hind
  · exact fun x ↦ (freeOrderedUnitComplement_spec _ (v x) (hind x)).1
  · intro x k
    simpa only [v, Equiv.symm_apply_apply] using
      (freeOrderedUnitComplement_spec _ (v x) (hind x)).2 (freeCofactorColumnOrder a k)

end GlobalEmbedding.Paper
