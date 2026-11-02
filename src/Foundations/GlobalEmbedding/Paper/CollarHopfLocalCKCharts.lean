import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import GlobalEmbedding.Paper.HopfCollarSquarePairing
import GlobalEmbedding.Paper.CollarAnalyticUnitNormal
import GlobalEmbedding.Paper.CollarCauchyKovalevskayaJetReduction

/-!
# The actual full-chart square-inverse collar Cauchy problem

Source: main.tex539–549, equation5.3. Reuse the native analytic sphere-product chart and all
transverse coordinates, actual Hopf flows, the accepted canonical normal, true square pairing,
native inverse analyticity and the accepted full second-order Cauchy theorem.
-/

noncomputable section
open scoped Topology Manifold ContDiff
namespace GlobalEmbedding.Paper

/-- The actual square pairing is invertible when its original full column family is
independent. Source: main.tex539–549. This converts the original square-column independence
supplied by the sole W4 Cauchy-data assembly into the true adjoint pairing inverse. No global
normal construction or cofactor basis completion is repeated here. -/
theorem collarHopfSquarePairing_invertible {a : ℕ}
    (c : Unit ⊕ BalancedPairingIndex a →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)))
    (hc : LinearIndependent ℝ c) :
    (freeColumnOperator c).adjoint.IsInvertible := by
  classical
  let A := freeColumnOperator c
  have hinj : Function.Injective A := (freeColumnOperator_injective_iff c).mpr hc
  have hcard : Fintype.card (BalancedPairingIndex a) = freeSymmetricColumnCount a + a := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (freeCofactorColumnOrder a)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Unit ⊕ BalancedPairingIndex a)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1))) := by
    rw [finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum, hcard]
    simp only [Fintype.card_unit, Fintype.card_fin]
    omega
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let e := (LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : e.toContinuousLinearMap = A := by
    ext u
    rfl
  change A.adjoint.IsInvertible
  rw [← he]
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := e.symm.toContinuousLinearMap.adjoint)
  · rw [← ContinuousLinearMap.adjoint_comp]
    simp [ContinuousLinearMap.adjoint_id]
  · rw [← ContinuousLinearMap.adjoint_comp]
    simp [ContinuousLinearMap.adjoint_id]

/-- Native finite linear coordinates for the FULL sphere-product chart model, retaining every
transverse coordinate. Source: main.tex549; use the existing finite basis and PiLp equivalence.
This equivalence is not asserted to be isometric. -/
def collarHopfChartCoordinates {a : ℕ} (C : Fin a → ℕ) :
    FreeHopfModelSpace C ≃L[ℝ] CKX (Module.finrank ℝ (FreeHopfModelSpace C)) :=
  (Module.finBasis ℝ (FreeHopfModelSpace C)).equivFunL.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm

/-- The actual native source chart followed only by its true full-dimensional linear
coordinates. Source: main.tex549. The original sphere-product atlas is unchanged. -/
def collarHopfFullChart {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) :
    OpenPartialHomeomorph (FreeHopfProduct C)
      (CKX (Module.finrank ℝ (FreeHopfModelSpace C))) :=
  (chartAt (FreeHopfModelSpace C) x₀).trans
    (collarHopfChartCoordinates C).toHomeomorph.toOpenPartialHomeomorph

/-- The full native chart is analytic at every actual point of its source.
Source: main.tex549. Apply the native analytic atlas theorem and the actual linear coordinates. -/
theorem collarHopfFullChart_omega {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ x : FreeHopfProduct C) (hx : x ∈ (collarHopfFullChart C x₀).source) :
    ContMDiffAt (freeHopfModel C)
      𝓘(ℝ, CKX (Module.finrank ℝ (FreeHopfModelSpace C))) ω (collarHopfFullChart C x₀) x := by
  have : IsManifold (freeHopfModel C) ω (FreeHopfProduct C) :=
    collarHopfProduct_native_omega C
  have hx' : x ∈ (chartAt (FreeHopfModelSpace C) x₀).source := hx.1
  have hc := (contMDiffOn_chart (I := freeHopfModel C) (n := ω) (x := x₀)).contMDiffAt
    ((chartAt (FreeHopfModelSpace C) x₀).open_source.mem_nhds hx')
  exact
    ((collarHopfChartCoordinates C).toContinuousLinearMap.contDiff.contMDiff.contMDiffAt).comp x hc

/-- The inverse full chart is analytic at every actual point of its target.
Source: main.tex549. Restrict to the genuine target before composing the native chart inverse. -/
theorem collarHopfFullChart_symm_omega {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    ContMDiffAt 𝓘(ℝ, CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
      (freeHopfModel C) ω (collarHopfFullChart C x₀).symm q := by
  have : IsManifold (freeHopfModel C) ω (FreeHopfProduct C) :=
    collarHopfProduct_native_omega C
  have hq' : (collarHopfChartCoordinates C).symm q ∈
      (chartAt (FreeHopfModelSpace C) x₀).target := hq.2
  have hc := (contMDiffOn_chart_symm (I := freeHopfModel C) (n := ω)
    (x := x₀)).contMDiffAt
      ((chartAt (FreeHopfModelSpace C) x₀).open_target.mem_nhds hq')
  exact hc.comp q
    (collarHopfChartCoordinates C).symm.toContinuousLinearMap.contDiff.contMDiff.contMDiffAt

/-- The SAME original Hopf flow expressed in the full native chart. Values outside its genuine
chart domain are merely total-function values; all identities below use actual chart germs. -/
def collarHopfChartFlow {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i : Fin a)
    (z : ℝ × CKX (Module.finrank ℝ (FreeHopfModelSpace C))) :
    CKX (Module.finrank ℝ (FreeHopfModelSpace C)) :=
  collarHopfFullChart C x₀
    (freeHopfProductFlow C i z.1 ((collarHopfFullChart C x₀).symm z.2))

/-- The actual coordinate Hopf flow is jointly analytic at time zero at every chart point.
Source: main.tex549. Both native chart maps are used only at points in their actual domains,
and the original flow is jointly native analytic; no globally valid chart identity is assumed. -/
theorem collarHopfChartFlow_analyticAt {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (collarHopfChartFlow C x₀ i) (0, q) := by
  have hb := collarHopfFullChart_symm_omega C x₀ q hq
  have hin := (collarHopfProductFlow_omega C i).contMDiffAt.comp (0, q)
    (contMDiffAt_fst.prodMk (hb.comp (0, q) contMDiffAt_snd))
  have hs : freeHopfProductFlow C i 0 ((collarHopfFullChart C x₀).symm q) ∈
      (collarHopfFullChart C x₀).source := by
    simpa only [freeHopfProductFlow_zero] using (collarHopfFullChart C x₀).map_target hq
  have hout := (collarHopfFullChart_omega C x₀ _ hs).comp (0, q) hin
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hout
  exact hout.contDiffAt.analyticAt

/-- The actual first chart velocity of the SAME native Hopf flow, with all spatial coordinates.
Source: main.tex549. This is the true derivative of the proved analytic coordinate flow. -/
def collarHopfChartA {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C))) :
    CKX (Module.finrank ℝ (FreeHopfModelSpace C)) :=
  fderiv ℝ (collarHopfChartFlow C x₀ i) (0, q) (1, 0)

/-- The actual derivative of the j-th chart velocity in the i-th flow direction.
Source: main.tex549, the first-order coefficient in the second Hopf derivative. -/
def collarHopfChartB {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i j : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C))) :
    CKX (Module.finrank ℝ (FreeHopfModelSpace C)) :=
  fderiv ℝ (collarHopfChartA C x₀ j) q (collarHopfChartA C x₀ i q)

/-- True coordinate Hopf velocities are analytic at every point of the actual chart target.
Source: main.tex549. Differentiate the genuine joint analytic flow and evaluate at time zero. -/
theorem collarHopfChartA_analyticAt {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (collarHopfChartA C x₀ i) q := by
  have hg := (collarHopfChartFlow_analyticAt C x₀ i q hq).fderiv
  have hi : AnalyticAt ℝ
      (fun y : CKX (Module.finrank ℝ (FreeHopfModelSpace C)) ↦ ((0 : ℝ), y)) q :=
    analyticAt_const.prod analyticAt_id
  exact ((ContinuousLinearMap.apply ℝ _ ((1, 0) :
    ℝ × CKX (Module.finrank ℝ (FreeHopfModelSpace C)))).analyticAt _).comp (hg.comp hi)

/-- The genuine second-direction chart coefficients are analytic.
Source: main.tex549. Use the actual derivative of the analytic velocity and actual
CLM evaluation. -/
theorem collarHopfChartB_analyticAt {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i j : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (collarHopfChartB C x₀ i j) q := by
  exact ((ContinuousLinearMap.apply ℝ
    (CKX (Module.finrank ℝ (FreeHopfModelSpace C)))).analyticAt_bilinear _).comp₂
      (collarHopfChartA_analyticAt C x₀ i q hq)
      (collarHopfChartA_analyticAt C x₀ j q hq).fderiv

/-- Every actual Hopf derivative is the true chart derivative in its actual coordinate velocity.
Source: main.tex549. Restrict the original flow to its genuine chart-source germ, use the true
inverse chart there, then apply the native derivative chain rule. No global chart identity or
desired derivative dictionary is assumed. Arbitrary total values outside the chart do not matter. -/
theorem collarHopfDeriv_fullChart {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F)
    (hf : DifferentiableAt ℝ (f ∘ (collarHopfFullChart C x₀).symm) q) :
    freeHopfDeriv C i f ((collarHopfFullChart C x₀).symm q) =
      fderiv ℝ (f ∘ (collarHopfFullChart C x₀).symm) q (collarHopfChartA C x₀ i q) := by
  let ψ := collarHopfFullChart C x₀
  have hg := collarHopfChartFlow_analyticAt C x₀ i q hq
  have hz : collarHopfChartFlow C x₀ i (0, q) = q := by
    simpa only [collarHopfChartFlow, freeHopfProductFlow_zero] using ψ.right_inv hq
  have hγ : HasDerivAt (fun t : ℝ ↦ collarHopfChartFlow C x₀ i (t, q))
      (collarHopfChartA C x₀ i q) 0 := by
    simpa only [collarHopfChartA, Function.comp_def, id_eq] using
      hg.differentiableAt.hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) q))
  have houter : HasFDerivAt (f ∘ ψ.symm) (fderiv ℝ (f ∘ ψ.symm) q)
      (collarHopfChartFlow C x₀ i (0, q)) := by
    rw [hz]
    exact hf.hasFDerivAt
  have hc : Continuous (fun t : ℝ ↦ freeHopfProductFlow C i t (ψ.symm q)) :=
    (collarHopfProductFlow_omega C i).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hs : ∀ᶠ t : ℝ in 𝓝 0, freeHopfProductFlow C i t (ψ.symm q) ∈ ψ.source := by
    apply hc.continuousAt.eventually
    change ψ.source ∈ 𝓝 (freeHopfProductFlow C i 0 (ψ.symm q))
    simpa only [freeHopfProductFlow_zero] using
      ψ.open_source.mem_nhds (ψ.map_target hq)
  have heq : (fun t : ℝ ↦ f (freeHopfProductFlow C i t (ψ.symm q))) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ (f ∘ ψ.symm) (collarHopfChartFlow C x₀ i (t, q))) := by
    filter_upwards [hs] with t ht
    simp only [Function.comp_apply, collarHopfChartFlow]
    rw [ψ.left_inv ht]
  change deriv (fun t : ℝ ↦ f (freeHopfProductFlow C i t (ψ.symm q))) 0 = _
  exact heq.deriv_eq.trans (houter.comp_hasDerivAt 0 hγ).deriv

/-- The true second Hopf derivative in the full chart includes BOTH the second derivative
of the unknown and the derivative of the chart velocity. Source: main.tex549. Apply the proved
actual first-derivative dictionary on a genuine target neighborhood, differentiate that germ,
and use the native derivative of CLM evaluation. No missing transverse or lower-order term. -/
theorem collarHopfSecondDeriv_fullChart {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) (i j : Fin a)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : FreeHopfProduct C → F)
    (hf : AnalyticAt ℝ (f ∘ (collarHopfFullChart C x₀).symm) q) :
    freeHopfDeriv C i (freeHopfDeriv C j f) ((collarHopfFullChart C x₀).symm q) =
      fderiv ℝ (fderiv ℝ (f ∘ (collarHopfFullChart C x₀).symm)) q
          (collarHopfChartA C x₀ i q) (collarHopfChartA C x₀ j q) +
        fderiv ℝ (f ∘ (collarHopfFullChart C x₀).symm) q (collarHopfChartB C x₀ i j q) := by
  let ψ := collarHopfFullChart C x₀
  have heq : (freeHopfDeriv C j f ∘ ψ.symm) =ᶠ[𝓝 q]
      (fun y ↦ fderiv ℝ (f ∘ ψ.symm) y (collarHopfChartA C x₀ j y)) := by
    filter_upwards [ψ.open_target.mem_nhds hq, hf.eventually_analyticAt] with y hy hfy
    exact collarHopfDeriv_fullChart C x₀ j y hy f hfy.differentiableAt
  have hA := (collarHopfChartA_analyticAt C x₀ j q hq).differentiableAt
  have hd := hf.fderiv.differentiableAt.clm_apply hA
  rw [collarHopfDeriv_fullChart C x₀ i q hq (freeHopfDeriv C j f)
    (heq.differentiableAt_iff.mpr hd), heq.fderiv_eq]
  rw [fderiv_clm_apply hf.fderiv.differentiableAt hA]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- Actual native analytic Cauchy data have analytic representatives in the SAME full chart.
Source: main.tex539–549. This applies to the already constructed H and its SAME normal,
without reconstructing either global datum. -/
theorem collarHopfChartData_analyticAt {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)]
    (x₀ : FreeHopfProduct C) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : FreeHopfProduct C → F) (hf : ContMDiff (freeHopfModel C) 𝓘(ℝ, F) ω f)
    (q : CKX (Module.finrank ℝ (FreeHopfModelSpace C)))
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (f ∘ (collarHopfFullChart C x₀).symm) q :=
  (hf.contMDiffAt.comp q (collarHopfFullChart_symm_omega C x₀ q hq)).contDiffAt.analyticAt

#print axioms collarHopfChartData_analyticAt
#print axioms collarHopfChartCoordinates
#print axioms collarHopfFullChart
#print axioms collarHopfChartFlow
#print axioms collarHopfSecondDeriv_fullChart
#print axioms collarHopfChartA
#print axioms collarHopfChartB
#print axioms collarHopfChartA_analyticAt
#print axioms collarHopfChartB_analyticAt
#print axioms collarHopfDeriv_fullChart
#print axioms collarHopfFullChart_omega
#print axioms collarHopfFullChart_symm_omega
#print axioms collarHopfChartFlow_analyticAt
#print axioms collarHopfSquarePairing_invertible
end GlobalEmbedding.Paper
