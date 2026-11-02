import GlobalEmbedding.Paper.CollarHopfLocalCKCharts
import GlobalEmbedding.Paper.CollarCauchyKovalevskayaSecondOrder
import GlobalEmbedding.Paper.CollarHopfAnalyticCauchyData
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual full-chart square-inverse collar Cauchy problem

Source: main.tex539–549, equation5.3. Reuse the native analytic sphere-product chart and all
transverse coordinates, actual Hopf flows, the accepted canonical normal, true square pairing,
native inverse analyticity and the accepted full second-order Cauchy theorem.
-/

noncomputable section
open scoped Topology Manifold ContDiff
namespace GlobalEmbedding.Paper

section ChartJet
variable {a : ℕ} (C : Fin a → ℕ) [∀ i, Fact (0 < C i)] (x₀ : FreeHopfProduct C)
local notation "d" => Module.finrank ℝ (FreeHopfModelSpace C)
local notation "N" => freeSymmetricColumnCount a + a + 1
local notation "J" => CKForcingInput d N
local notation "L" => EuclideanSpace ℝ (Fin N)
local notation "V" => CKVal N

/-- The original first Hopf column evaluated on the FULL spatial jet. Source: main.tex5.3.
The coefficients are the actual native-chart Hopf velocities, not supplied arrays. -/
def collarHopfJetFirst (z : J) (i : Fin a) : L :=
  ∑ k, (collarHopfChartA C x₀ i z.1 k) • WithLp.toLp 2 (z.2.2.2.1 k)

/-- The original sorted second Hopf column evaluated on the FULL first and second spatial jet.
Source: main.tex5.3. The genuine derivative-of-velocity lower-order term is retained. -/
def collarHopfJetSecond (z : J) (i j : Fin a) : L :=
  (∑ k, ∑ l, (collarHopfChartA C x₀ i z.1 k * collarHopfChartA C x₀ j z.1 l) •
    WithLp.toLp 2 (z.2.2.2.2.1 k l)) +
      ∑ l, (collarHopfChartB C x₀ i j z.1 l) • WithLp.toLp 2 (z.2.2.2.1 l)

/-- The original first Hopf derivative of G_r evaluated on its full mixed spatial/time jet.
Source: main.tex5.3. Only one normal derivative occurs in this actual RHS argument. -/
def collarHopfJetMixed (z : J) (i : Fin a) : L :=
  ∑ k, (collarHopfChartA C x₀ i z.1 k) • WithLp.toLp 2 (z.2.2.2.2.2.2 k)

/-- The literal original square column order on actual second-order jet arguments.
Source: main.tex5.3. Reuse Unit followed by the existing first/sorted-second index. -/
def collarHopfJetColumns (z : J) : Unit ⊕ BalancedPairingIndex a → L :=
  Sum.elim (fun _ ↦ WithLp.toLp 2 z.2.2.2.2.2.1)
    (Sum.elim (collarHopfJetFirst C x₀ z)
      (fun ij ↦ collarHopfJetSecond C x₀ z ij.val.1 ij.val.2))

/-- The literal 0/0/mixed-inner-product forcing of the original square equation.
Source: main.tex5.3. This is subsequently identified with hopfCollarSquareForcing on actual jets. -/
def collarHopfJetForcing (z : J) : EuclideanSpace ℝ (Unit ⊕ BalancedPairingIndex a) :=
  WithLp.toLp 2 (Sum.elim (fun _ : Unit ↦ 0)
    (Sum.elim (fun _ : Fin a ↦ 0)
      (fun ij ↦ inner ℝ (collarHopfJetMixed C x₀ z ij.val.1)
        (collarHopfJetMixed C x₀ z ij.val.2))))

/-- The actual square inverse RHS as a function on the EXISTING full CKForcingInput.
Source: main.tex5.3. No second normal derivative, desired local solution or abstract dictionary
is part of this function; all spatial and mixed jets remain present. -/
def collarHopfLocalRHS (z : J) : V :=
  WithLp.ofLp ((freeColumnOperator (collarHopfJetColumns C x₀ z)).adjoint.inverse
    (collarHopfJetForcing C x₀ z))

/-- The genuine first Hopf jet columns depend analytically on the original full CK jet.
Source: main.tex549. Actual chart coefficients and the original jet projections are analytic. -/
theorem collarHopfJetFirst_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) (i : Fin a) :
    AnalyticAt ℝ (fun w : J ↦ collarHopfJetFirst C x₀ w i) z := by
  unfold collarHopfJetFirst
  apply Finset.analyticAt_fun_sum
  intro k _
  have hA := ((EuclideanSpace.proj k : CKX d →L[ℝ] ℝ).analyticAt _).comp
    ((collarHopfChartA_analyticAt C x₀ i z.1 hz).comp analyticAt_fst)
  have hp : AnalyticAt ℝ (fun w : J ↦ w.2.2.2.1 k) z :=
    ((ContinuousLinearMap.proj k : (Fin d → V) →L[ℝ] V).analyticAt _).comp
      (analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  have hp' := (e.toContinuousLinearMap.analyticAt _).comp hp
  exact hA.smul hp'

/-- The actual mixed Hopf jet columns are analytic functions of the full original CK jet.
Source: main.tex549. The original mixed first-time derivatives are simple analytic projections. -/
theorem collarHopfJetMixed_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) (i : Fin a) :
    AnalyticAt ℝ (fun w : J ↦ collarHopfJetMixed C x₀ w i) z := by
  unfold collarHopfJetMixed
  apply Finset.analyticAt_fun_sum
  intro k _
  have hA := ((EuclideanSpace.proj k : CKX d →L[ℝ] ℝ).analyticAt _).comp
    ((collarHopfChartA_analyticAt C x₀ i z.1 hz).comp analyticAt_fst)
  have hp : AnalyticAt ℝ (fun w : J ↦ w.2.2.2.2.2.2 k) z :=
    ((ContinuousLinearMap.proj k : (Fin d → V) →L[ℝ] V).analyticAt _).comp
      (analyticAt_snd.comp (analyticAt_snd.comp (analyticAt_snd.comp
        (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))))
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  exact hA.smul ((e.toContinuousLinearMap.analyticAt _).comp hp)

/-- Actual second Hopf jet columns are analytic in all full first/second spatial jet arguments.
Source: main.tex549. Use the already proved actual analytic A/B coefficients and finite sums. -/
theorem collarHopfJetSecond_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) (i j : Fin a) :
    AnalyticAt ℝ (fun w : J ↦ collarHopfJetSecond C x₀ w i j) z := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  have hA (t : Fin a) (k : Fin d) :
      AnalyticAt ℝ (fun w : J ↦ collarHopfChartA C x₀ t w.1 k) z :=
    ((EuclideanSpace.proj k : CKX d →L[ℝ] ℝ).analyticAt _).comp
      ((collarHopfChartA_analyticAt C x₀ t z.1 hz).comp analyticAt_fst)
  unfold collarHopfJetSecond
  apply AnalyticAt.add
  · apply Finset.analyticAt_fun_sum
    intro k _
    apply Finset.analyticAt_fun_sum
    intro l _
    have hh : AnalyticAt ℝ (fun w : J ↦ w.2.2.2.2.1 k l) z :=
      ((ContinuousLinearMap.proj l : (Fin d → V) →L[ℝ] V).analyticAt _).comp
        (((ContinuousLinearMap.proj k :
          (Fin d → Fin d → V) →L[ℝ] (Fin d → V)).analyticAt _).comp
            (analyticAt_fst.comp (analyticAt_snd.comp
              (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))))
    exact ((hA i k).mul (hA j l)).smul ((e.toContinuousLinearMap.analyticAt _).comp hh)
  · apply Finset.analyticAt_fun_sum
    intro l _
    have hB := ((EuclideanSpace.proj l : CKX d →L[ℝ] ℝ).analyticAt _).comp
      ((collarHopfChartB_analyticAt C x₀ i j z.1 hz).comp analyticAt_fst)
    have hp : AnalyticAt ℝ (fun w : J ↦ w.2.2.2.1 l) z :=
      ((ContinuousLinearMap.proj l : (Fin d → V) →L[ℝ] V).analyticAt _).comp
        (analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
    exact hB.smul ((e.toContinuousLinearMap.analyticAt _).comp hp)

/-- The entire literal normal/first/sorted-second column family is analytic in actual CK jets.
Source: main.tex5.3. Every original column is present, with the true normal-velocity argument. -/
theorem collarHopfJetColumns_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (collarHopfJetColumns C x₀) z := by
  apply AnalyticAt.pi
  intro k
  cases k with
  | inl k =>
    have hv : AnalyticAt ℝ (fun w : J ↦ w.2.2.2.2.2.1) z :=
      analyticAt_fst.comp (analyticAt_snd.comp (analyticAt_snd.comp
        (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))))
    let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
    exact (e.toContinuousLinearMap.analyticAt _).comp hv
  | inr k =>
    cases k with
    | inl i => exact collarHopfJetFirst_analyticAt C x₀ z hz i
    | inr ij => exact collarHopfJetSecond_analyticAt C x₀ z hz ij.val.1 ij.val.2

/-- The literal original mixed-inner-product RHS is analytic at every genuine chart jet.
Source: main.tex5.3. Real inner products are native continuous bilinear maps. -/
theorem collarHopfJetForcing_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ (collarHopfJetForcing C x₀) z := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Unit ⊕ BalancedPairingIndex a ↦ ℝ)).symm
  apply (e.toContinuousLinearMap.analyticAt _).comp
  apply AnalyticAt.pi
  intro k
  cases k with
  | inl k => exact analyticAt_const
  | inr k =>
    cases k with
    | inl i => exact analyticAt_const
    | inr ij =>
      exact ((innerSL ℝ (E := L)).analyticAt_bilinear _).comp
        ((collarHopfJetMixed_analyticAt C x₀ z hz ij.val.1).prod
          (collarHopfJetMixed_analyticAt C x₀ z hz ij.val.2))

/-- The actual literal square pairing varies analytically with the FULL original CK jet.
Source: main.tex549. Reuse native finite synthesis and the real linear adjoint. -/
theorem collarHopfJetPairing_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target) :
    AnalyticAt ℝ
      (fun w : J ↦ (freeColumnOperator (collarHopfJetColumns C x₀ w)).adjoint) z := by
  let B := EuclideanSpace ℝ (Unit ⊕ BalancedPairingIndex a)
  have hA : AnalyticAt ℝ (fun w : J ↦ freeColumnOperator (collarHopfJetColumns C x₀ w)) z := by
    unfold freeColumnOperator
    apply Finset.analyticAt_fun_sum
    intro k _
    have hc := ((ContinuousLinearMap.proj k :
      (Unit ⊕ BalancedPairingIndex a → L) →L[ℝ] L).analyticAt _).comp
        (collarHopfJetColumns_analyticAt C x₀ z hz)
    have hterm := (((ContinuousLinearMap.smulRightL ℝ B L)
      (EuclideanSpace.proj k)).analyticAt _).comp hc
    convert hterm using 1
    funext w
    ext u
    simp only [Function.comp_apply, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply]
  let adj : (B →L[ℝ] L) →L[ℝ] (L →L[ℝ] B) :=
    (ContinuousLinearMap.adjoint :
      (B →L[ℝ] L) ≃ₗᵢ[ℝ] (L →L[ℝ] B)).toContinuousLinearMap
  exact (adj.analyticAt _).comp hA

/-- The actual square inverse RHS is analytic wherever its SAME actual square pairing is
invertible. Source: main.tex549. This intermediate noncharacteristicity input is supplied
at the original Cauchy jet by W4's actual fullsquareLI and the proved actual jet dictionary,
not added to the final local collar theorem. Reuse native inverse analyticity at omega. -/
theorem collarHopfLocalRHS_analyticAt (z : J)
    (hz : z.1 ∈ (collarHopfFullChart C x₀).target)
    (hT : (freeColumnOperator (collarHopfJetColumns C x₀ z)).adjoint.IsInvertible) :
    AnalyticAt ℝ (collarHopfLocalRHS C x₀) z := by
  have hInv : AnalyticAt ℝ
      (fun w : J ↦ (freeColumnOperator (collarHopfJetColumns C x₀ w)).adjoint.inverse) z :=
    (hT.contDiffAt_map_inverse (n := ω)).analyticAt.comp
      (f := fun w : J ↦ (freeColumnOperator (collarHopfJetColumns C x₀ w)).adjoint)
      (collarHopfJetPairing_analyticAt C x₀ z hz)
  have hval := ((ContinuousLinearMap.apply ℝ L).analyticAt_bilinear _).comp₂
    (collarHopfJetForcing_analyticAt C x₀ z hz) hInv
  let e : L ≃L[ℝ] V := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)
  exact (e.toContinuousLinearMap.analyticAt _).comp hval

/-- Native full finite-coordinate expansion of a spatial derivative. Source: main.tex5.3.
This is just the native orthonormal-basis reconstruction mapped by the actual derivative. -/
theorem collarHopf_fderiv_coordinates {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : CKX n → F) (q v : CKX n) :
    fderiv ℝ g q v = ∑ k, v k • fderiv ℝ g q (EuclideanSpace.single k 1) := by
  have h := congrArg (fderiv ℝ g q) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using h.symm

/-- Actual second spatial derivative in full native coordinate directions. Source: main.tex5.3.
Evaluate the native derivative-of-linear-map rule and reconstruct both direction vectors. -/
theorem collarHopf_second_fderiv_coordinates {n m : ℕ}
    (g : CKX n → CKVal m) (q v w : CKX n) (hg : AnalyticAt ℝ g q) :
    fderiv ℝ (fderiv ℝ g) q v w =
      ∑ k, ∑ l, (v k * w l) • ckDataSpatialHessian g q k l := by
  have he (l : Fin n) :
      fderiv ℝ (fun y ↦ fderiv ℝ g y (EuclideanSpace.single l 1)) q =
        (fderiv ℝ (fderiv ℝ g) q).flip (EuclideanSpace.single l 1) := by
    rw [fderiv_clm_apply hg.fderiv.differentiableAt (differentiableAt_const _)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  have hv := collarHopf_fderiv_coordinates (fderiv ℝ g) q v
  rw [hv]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hw := congrArg ((fderiv ℝ (fderiv ℝ g) q) (EuclideanSpace.single k 1))
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w)
  rw [← hw]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [ckDataSpatialHessian, he]
  rfl

omit [∀ i, Fact (0 < C i)] in
/-- A native linear output equivalence commutes with the actual Hopf derivative, including
its total derivative convention. Source: main.tex5.3; native equiv.comp_fderiv. -/
theorem collarHopfDeriv_equiv {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃L[ℝ] G) (f : FreeHopfProduct C → F) (i : Fin a)
    (x : FreeHopfProduct C) :
    freeHopfDeriv C i (e ∘ f) x = e (freeHopfDeriv C i f x) := by
  unfold freeHopfDeriv orbitDeriv
  change deriv (e ∘ (fun t ↦ f (freeHopfProductFlow C i t x))) 0 = _
  simp only [deriv, e.comp_fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- At the genuine original Cauchy jet the first array is the actual Hopf derivative of H.
Source: main.tex5.3. Apply the accepted full-chart dictionary to the native output coordinates. -/
theorem collarHopfJetFirst_initial (H ν : FreeHopfProduct C → L) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    (hH : AnalyticAt ℝ (H ∘ (collarHopfFullChart C x₀).symm) q) (i : Fin a) :
    collarHopfJetFirst C x₀
      (ckForcingInitialPoint (fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y)))
        (fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))) q) i =
      freeHopfDeriv C i H ((collarHopfFullChart C x₀).symm q) := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  let h : FreeHopfProduct C → V := fun y ↦ WithLp.ofLp (H y)
  have hh : AnalyticAt ℝ (h ∘ (collarHopfFullChart C x₀).symm) q :=
    (e.symm.toContinuousLinearMap.analyticAt _).comp hH
  have he : e ∘ h = H := by funext y; exact e.apply_symm_apply (H y)
  rw [← he, collarHopfDeriv_equiv C e h,
    collarHopfDeriv_fullChart C x₀ i q hq h hh.differentiableAt,
    collarHopf_fderiv_coordinates]
  simp only [map_sum, map_smul]
  rfl

/-- At the same genuine Cauchy jet the second array is the actual iterated Hopf derivative.
Source: main.tex5.3. Retain the full Hessian and genuine derivative-of-velocity term. -/
theorem collarHopfJetSecond_initial (H ν : FreeHopfProduct C → L) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    (hH : AnalyticAt ℝ (H ∘ (collarHopfFullChart C x₀).symm) q) (i j : Fin a) :
    collarHopfJetSecond C x₀
      (ckForcingInitialPoint (fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y)))
        (fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))) q) i j =
      freeHopfDeriv C i (freeHopfDeriv C j H) ((collarHopfFullChart C x₀).symm q) := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  let h : FreeHopfProduct C → V := fun y ↦ WithLp.ofLp (H y)
  have hh : AnalyticAt ℝ (h ∘ (collarHopfFullChart C x₀).symm) q :=
    (e.symm.toContinuousLinearMap.analyticAt _).comp hH
  have he : e ∘ h = H := by funext y; exact e.apply_symm_apply (H y)
  have hej : freeHopfDeriv C j H = e ∘ freeHopfDeriv C j h := by
    funext y
    rw [← he, collarHopfDeriv_equiv C e h]
    rfl
  rw [hej, collarHopfDeriv_equiv C e (freeHopfDeriv C j h),
    collarHopfSecondDeriv_fullChart C x₀ i j q hq h hh,
    collarHopf_second_fderiv_coordinates _ _ _ _ hh,
    collarHopf_fderiv_coordinates]
  simp only [map_add, map_sum, map_smul]
  rfl

/-- The complete actual initial square family is exactly the original normal followed by
all old first/sorted-second Hopf columns. Source: main.tex539–549; no compatibility input. -/
theorem collarHopfJetColumns_initial (H ν : FreeHopfProduct C → L) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    (hH : AnalyticAt ℝ (H ∘ (collarHopfFullChart C x₀).symm) q) :
    collarHopfJetColumns C x₀
      (ckForcingInitialPoint (fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y)))
        (fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))) q) =
      Sum.elim (fun _ : Unit ↦ ν ((collarHopfFullChart C x₀).symm q))
        (freeFlowColumns (freeHopfProductFlow C) H ((collarHopfFullChart C x₀).symm q)) := by
  funext k
  rcases k with k | (i | ij)
  · rfl
  · exact collarHopfJetFirst_initial C x₀ H ν q hq hH i
  · exact collarHopfJetSecond_initial C x₀ H ν q hq hH ij.val.1 ij.val.2

/-- Genuine noncharacteristicity at the original Cauchy jet, from the SAME original square
column independence. Source: main.tex539–549. The initial jet dictionary is proved above;
W4 supplies the actual original H/nu family, so no desired matrix premise is introduced. -/
theorem collarHopfLocalRHS_initial_analyticAt (H ν : FreeHopfProduct C → L) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    (hH : AnalyticAt ℝ (H ∘ (collarHopfFullChart C x₀).symm) q)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν ((collarHopfFullChart C x₀).symm q))
        (freeFlowColumns (freeHopfProductFlow C) H ((collarHopfFullChart C x₀).symm q)))) :
    AnalyticAt ℝ (collarHopfLocalRHS C x₀)
      (ckForcingInitialPoint (fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y)))
        (fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))) q) := by
  let h₀ := fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y))
  let h₁ := fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))
  let z : J := ckForcingInitialPoint h₀ h₁ q
  have ht : (freeColumnOperator (collarHopfJetColumns C x₀ z)).adjoint.IsInvertible := by
    rw [show collarHopfJetColumns C x₀ z = _ from
      collarHopfJetColumns_initial C x₀ H ν q hq hH]
    exact collarHopfSquarePairing_invertible _ hLI
  exact collarHopfLocalRHS_analyticAt C x₀ z hq ht

/-- The genuine full-coordinate local CK solution for the actual geometric collar RHS,
with uniqueness against EVERY actual CK competitor. Source: main.tex549. The original
Cauchy data are transported through the same native chart; actual initial invertibility
and actual analytic RHS have already been proved, not supplied as desired hypotheses. -/
theorem collarHopfLocalCK_coordinates (H ν : FreeHopfProduct C → L) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target)
    (hH : AnalyticAt ℝ (H ∘ (collarHopfFullChart C x₀).symm) q)
    (hν : AnalyticAt ℝ (ν ∘ (collarHopfFullChart C x₀).symm) q)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun _ : Unit ↦ ν ((collarHopfFullChart C x₀).symm q))
        (freeFlowColumns (freeHopfProductFlow C) H ((collarHopfFullChart C x₀).symm q)))) :
    let h₀ := fun y ↦ WithLp.ofLp (H ((collarHopfFullChart C x₀).symm y))
    let h₁ := fun y ↦ WithLp.ofLp (ν ((collarHopfFullChart C x₀).symm y))
    ∃ ε > 0, ∃ u : CKJoint d → V,
      CKOriginalSolution (collarHopfLocalRHS C x₀) h₀ h₁ q ε u ∧
      (∀ v η, 0 < η → CKOriginalSolution (collarHopfLocalRHS C x₀) h₀ h₁ q η v →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧
          ∀ r x, (r, x) ∈ Metric.ball ((0 : ℝ), q) δ → u (r, x) = v (r, x)) := by
  let e : L ≃L[ℝ] V := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)
  exact collarCauchyKovalevskayaSecondOrder _ _ _ q
    (collarHopfLocalRHS_initial_analyticAt C x₀ H ν q hq hH hLI)
    ((e.toContinuousLinearMap.analyticAt _).comp hH)
    ((e.toContinuousLinearMap.analyticAt _).comp hν)

/-- The actual native reconstruction from the full coordinate map.
Source: main.tex549. This uses the same source chart and native Euclidean output coordinates. -/
def collarHopfReconstruct (u : CKJoint d → V) : ℝ × FreeHopfProduct C → L :=
  fun p ↦ WithLp.toLp 2 (u (p.1, collarHopfFullChart C x₀ p.2))

/-- The derivative of a genuine time slice uses exactly the original full spatial direction.
Source: main.tex5.3. This is native differentiation of the actual product embedding. -/
theorem collarHopf_fderiv_slice {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : CKJoint n → F) (r : ℝ) (q v : CKX n)
    (hu : DifferentiableAt ℝ u (r, q)) :
    fderiv ℝ (fun y ↦ u (r, y)) q v = fderiv ℝ u (r, q) (0, v) := by
  have h := hu.hasFDerivAt.comp q (hasFDerivAt_prodMk_right r q)
  change HasFDerivAt (fun y ↦ u (r, y)) _ q at h
  rw [h.fderiv]
  rfl

/-- Actual full coordinate spatial first jets are the actual spatial jets of each time slice.
Source: main.tex5.3. Apply the native product-embedding derivative, with no jet hypothesis. -/
theorem collarHopf_spatial_slice {n m : ℕ} (u : CKJoint n → CKVal m)
    (r : ℝ) (q : CKX n) (hu : DifferentiableAt ℝ u (r, q)) :
    ckDataSpatialDerivative (fun y ↦ u (r, y)) q = ckSpatialDerivative u (r, q) := by
  funext k
  exact collarHopf_fderiv_slice u r q (EuclideanSpace.single k 1) hu

/-- The full Hessian array of a time slice is the original actual CK Hessian array.
Source: main.tex5.3. Differentiate the actual first-jet germ and reuse the product embedding. -/
theorem collarHopf_hessian_slice {n m : ℕ} (u : CKJoint n → CKVal m)
    (r : ℝ) (q : CKX n) (hu : AnalyticAt ℝ u (r, q)) :
    ckDataSpatialHessian (fun y ↦ u (r, y)) q = ckSecondSpatialDerivative u (r, q) := by
  have hc : ContinuousAt (fun y : CKX n ↦ (r, y)) q :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have heq := hc.eventually hu.eventually_analyticAt
  funext k l
  have hh : (fun y ↦ fderiv ℝ (fun t ↦ u (r, t)) y (EuclideanSpace.single l 1))
      =ᶠ[𝓝 q] (fun y ↦ ckSpatialDerivative u (r, y) l) := by
    filter_upwards [heq] with y hy
    exact congrFun (collarHopf_spatial_slice u r y hy.differentiableAt) l
  unfold ckDataSpatialHessian
  rw [hh.fderiv_eq]
  have hd : AnalyticAt ℝ (fun z ↦ ckSpatialDerivative u z l) (r, q) :=
    ((ContinuousLinearMap.apply ℝ (CKVal m) (ckSpaceDirection l)).analyticAt _).comp hu.fderiv
  exact collarHopf_fderiv_slice _ r q (EuclideanSpace.single k 1) hd.differentiableAt

/-- The reconstructed map has exactly the actual CK normal derivative in the same native
output coordinates. Source: main.tex5.3. Differentiate the actual normal line, not values. -/
theorem collarHopfReconstruct_rDeriv (u : CKJoint d → V) (r : ℝ) (x : FreeHopfProduct C)
    (hu : DifferentiableAt ℝ u (r, collarHopfFullChart C x₀ x)) :
    hopfCollarRDeriv (collarHopfReconstruct C x₀ u) r x =
      WithLp.toLp 2 (ckTimeDerivative u (r, collarHopfFullChart C x₀ x)) := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  have h := hu.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r (collarHopfFullChart C x₀ x)))
  have he := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r h
  exact he.deriv

/-- The existing Cauchy Hessian depends only on the actual function germ.
Source: main.tex5.3. Differentiate native germ equality twice in the fixed spatial directions. -/
theorem collarHopf_dataHessian_germ {n m : ℕ} {f g : CKX n → CKVal m} {q : CKX n}
    (hfg : f =ᶠ[𝓝 q] g) : ckDataSpatialHessian f q = ckDataSpatialHessian g q := by
  funext k l
  have hd : (fun y ↦ fderiv ℝ f y (EuclideanSpace.single l 1)) =ᶠ[𝓝 q]
      (fun y ↦ fderiv ℝ g y (EuclideanSpace.single l 1)) := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with y hy
    rw [hy]
  exact congrArg (fun T : CKX n →L[ℝ] CKVal m ↦ T (EuclideanSpace.single k 1))
    hd.fderiv_eq

/-- Actual finite first Hopf columns for an arbitrary genuine chart representative germ.
Source: main.tex5.3. Reuse the proved initial-jet dictionary and native derivative locality. -/
theorem collarHopf_first_of_chart_germ (f : FreeHopfProduct C → L) (g : CKX d → V)
    (q : CKX d) (hq : q ∈ (collarHopfFullChart C x₀).target) (hg : AnalyticAt ℝ g q)
    (hfg : (fun y ↦ WithLp.ofLp (f ((collarHopfFullChart C x₀).symm y))) =ᶠ[𝓝 q] g)
    (i : Fin a) :
    freeHopfDeriv C i f ((collarHopfFullChart C x₀).symm q) =
      ∑ k, collarHopfChartA C x₀ i q k • WithLp.toLp 2 (ckDataSpatialDerivative g q k) := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  have he : (e ∘ g) =ᶠ[𝓝 q] (f ∘ (collarHopfFullChart C x₀).symm) := by
    filter_upwards [hfg] with y hy
    change e (g y) = f ((collarHopfFullChart C x₀).symm y)
    rw [← hy]
    exact e.apply_symm_apply _
  have hf := ((e.toContinuousLinearMap.analyticAt _).comp hg).congr he
  rw [← collarHopfJetFirst_initial C x₀ f (fun _ ↦ 0) q hq hf i]
  unfold collarHopfJetFirst ckForcingInitialPoint ckDataSpatialDerivative
  rw [hfg.fderiv_eq]

/-- Actual finite second Hopf columns for an arbitrary genuine full-chart representative germ.
Source: main.tex5.3. The already proved Hessian and lower-order B term remain present. -/
theorem collarHopf_second_of_chart_germ (f : FreeHopfProduct C → L) (g : CKX d → V)
    (q : CKX d) (hq : q ∈ (collarHopfFullChart C x₀).target) (hg : AnalyticAt ℝ g q)
    (hfg : (fun y ↦ WithLp.ofLp (f ((collarHopfFullChart C x₀).symm y))) =ᶠ[𝓝 q] g)
    (i j : Fin a) :
    freeHopfDeriv C i (freeHopfDeriv C j f) ((collarHopfFullChart C x₀).symm q) =
      (∑ k, ∑ l, (collarHopfChartA C x₀ i q k * collarHopfChartA C x₀ j q l) •
        WithLp.toLp 2 (ckDataSpatialHessian g q k l)) +
      ∑ l, collarHopfChartB C x₀ i j q l • WithLp.toLp 2 (ckDataSpatialDerivative g q l) := by
  let e : V ≃L[ℝ] L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm
  have he : (e ∘ g) =ᶠ[𝓝 q] (f ∘ (collarHopfFullChart C x₀).symm) := by
    filter_upwards [hfg] with y hy
    change e (g y) = f ((collarHopfFullChart C x₀).symm y)
    rw [← hy]
    exact e.apply_symm_apply _
  have hf := ((e.toContinuousLinearMap.analyticAt _).comp hg).congr he
  rw [← collarHopfJetSecond_initial C x₀ f (fun _ ↦ 0) q hq hf i j]
  unfold collarHopfJetSecond ckForcingInitialPoint
  rw [collarHopf_dataHessian_germ hfg]
  unfold ckDataSpatialDerivative
  rw [hfg.fderiv_eq]

/-- The literal full second-order jet already used in the original CK equation.
Source: main.tex5.3. This only abbreviates the existing forcing argument; no new jet carrier. -/
def collarHopfSolutionJet (u : CKJoint d → V) (z : CKJoint d) : J :=
  (z.2, (z.1, (u z, (ckSpatialDerivative u z, (ckSecondSpatialDerivative u z,
    (ckTimeDerivative u z, ckMixedDerivative u z))))))

/-- The reconstructed function really has the original coordinate map as its chart germ.
Source: main.tex549. Only genuine target-neighborhood chart inversion is used. -/
theorem collarHopfReconstruct_chart_germ (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) :
    (fun y ↦ WithLp.ofLp
      (collarHopfReconstruct C x₀ u (r, (collarHopfFullChart C x₀).symm y))) =ᶠ[𝓝 q]
        (fun y ↦ u (r, y)) := by
  filter_upwards [(collarHopfFullChart C x₀).open_target.mem_nhds hq] with y hy
  simp only [collarHopfReconstruct, (collarHopfFullChart C x₀).right_inv hy,
    WithLp.ofLp_toLp]

/-- The true normal derivative has exactly the original time-derivative chart germ.
Source: main.tex5.3. Analyticity supplies a genuine neighborhood for differentiating
normal lines. -/
theorem collarHopfReconstruct_rDeriv_chart_germ (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) :
    (fun y ↦ WithLp.ofLp (hopfCollarRDeriv (collarHopfReconstruct C x₀ u) r
      ((collarHopfFullChart C x₀).symm y))) =ᶠ[𝓝 q]
        (fun y ↦ ckTimeDerivative u (r, y)) := by
  have hc : ContinuousAt (fun y : CKX d ↦ (r, y)) q :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  filter_upwards [(collarHopfFullChart C x₀).open_target.mem_nhds hq,
    hc.eventually hu.eventually_analyticAt] with y hy huy
  have hd : DifferentiableAt ℝ u
      (r, collarHopfFullChart C x₀ ((collarHopfFullChart C x₀).symm y)) := by
    rw [(collarHopfFullChart C x₀).right_inv hy]
    exact huy.differentiableAt
  rw [collarHopfReconstruct_rDeriv C x₀ u r _ hd]
  simp only [(collarHopfFullChart C x₀).right_inv hy]

/-- ALL actual square columns of the reconstructed map are the literal original CK jet
columns. Source: main.tex5.3. Normal, first and all sorted-second columns are identified
using actual chart germs and actual time-slice derivatives, never supplied compatibility. -/
theorem collarHopfReconstruct_columns (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) :
    hopfCollarSquareColumns C (collarHopfReconstruct C x₀ u) r
      ((collarHopfFullChart C x₀).symm q) =
        collarHopfJetColumns C x₀ (collarHopfSolutionJet C u (r, q)) := by
  have hs : AnalyticAt ℝ (fun y ↦ u (r, y)) q :=
    hu.comp (analyticAt_const.prod analyticAt_id)
  have hg := collarHopfReconstruct_chart_germ C x₀ u r q hq
  funext k
  rcases k with k | (i | ij)
  · change hopfCollarRDeriv _ r _ = _
    have hd : DifferentiableAt ℝ u
        (r, collarHopfFullChart C x₀ ((collarHopfFullChart C x₀).symm q)) := by
      rw [(collarHopfFullChart C x₀).right_inv hq]
      exact hu.differentiableAt
    rw [collarHopfReconstruct_rDeriv C x₀ u r _ hd,
      (collarHopfFullChart C x₀).right_inv hq]
    rfl
  · change freeHopfDeriv C i (fun x ↦ collarHopfReconstruct C x₀ u (r, x))
      ((collarHopfFullChart C x₀).symm q) = _
    rw [collarHopf_first_of_chart_germ C x₀ _ _ q hq hs hg i,
      collarHopf_spatial_slice u r q hu.differentiableAt]
    rfl
  · change freeHopfDeriv C ij.val.1
      (freeHopfDeriv C ij.val.2 (fun x ↦ collarHopfReconstruct C x₀ u (r, x)))
        ((collarHopfFullChart C x₀).symm q) = _
    rw [collarHopf_second_of_chart_germ C x₀ _ _ q hq hs hg ij.val.1 ij.val.2,
      collarHopf_hessian_slice u r q hu,
      collarHopf_spatial_slice u r q hu.differentiableAt]
    rfl

/-- Actual mixed Hopf/normal derivatives of the reconstructed map are the original CK mixed
jet. Source: main.tex5.3. The normal derivative is first identified on a genuine chart germ. -/
theorem collarHopfReconstruct_mixed (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) (i : Fin a) :
    freeHopfDeriv C i (hopfCollarRDeriv (collarHopfReconstruct C x₀ u) r)
      ((collarHopfFullChart C x₀).symm q) =
        collarHopfJetMixed C x₀ (collarHopfSolutionJet C u (r, q)) i := by
  have ht : AnalyticAt ℝ (ckTimeDerivative u) (r, q) :=
    ((ContinuousLinearMap.apply ℝ V ckTimeDirection).analyticAt _).comp hu.fderiv
  have hs : AnalyticAt ℝ (fun y ↦ ckTimeDerivative u (r, y)) q :=
    ht.comp (analyticAt_const.prod analyticAt_id)
  rw [collarHopf_first_of_chart_germ C x₀ _ _ q hq hs
    (collarHopfReconstruct_rDeriv_chart_germ C x₀ u r q hq hu) i,
    collarHopf_spatial_slice (ckTimeDerivative u) r q ht.differentiableAt]
  rfl

/-- The same actual square pairing is the adjoint synthesized from the literal CK jet.
Source: main.tex5.3. This is a consequence of the full actual column identification. -/
theorem collarHopfReconstruct_pairing (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) :
    hopfCollarSquarePairing C (collarHopfReconstruct C x₀ u) r
      ((collarHopfFullChart C x₀).symm q) =
        (freeColumnOperator
          (collarHopfJetColumns C x₀ (collarHopfSolutionJet C u (r, q)))).adjoint := by
  unfold hopfCollarSquarePairing
  rw [collarHopfReconstruct_columns C x₀ u r q hq hu]

/-- The same original geometric forcing is the literal original CK mixed-jet forcing.
Source: main.tex5.3. Every sorted pair and diagonal is retained. -/
theorem collarHopfReconstruct_forcing (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) :
    hopfCollarSquareForcing C (collarHopfReconstruct C x₀ u) r
      ((collarHopfFullChart C x₀).symm q) =
        collarHopfJetForcing C x₀ (collarHopfSolutionJet C u (r, q)) := by
  unfold hopfCollarSquareForcing collarHopfJetForcing
  congr 1
  funext k
  rcases k with k | (i | ij)
  · rfl
  · rfl
  · change inner ℝ _ _ = inner ℝ _ _
    rw [collarHopfReconstruct_mixed C x₀ u r q hq hu ij.val.1,
      collarHopfReconstruct_mixed C x₀ u r q hq hu ij.val.2]

/-- The actual normal acceleration of the reconstructed map is the CK second time derivative.
Source: main.tex5.3. Differentiate an equality on a genuine normal-time neighborhood. -/
theorem collarHopfReconstruct_acceleration (u : CKJoint d → V) (r : ℝ)
    (x : FreeHopfProduct C) (hu : AnalyticAt ℝ u (r, collarHopfFullChart C x₀ x)) :
    deriv (fun t ↦ hopfCollarRDeriv (collarHopfReconstruct C x₀ u) t x) r =
      WithLp.toLp 2 (ckSecondTimeDerivative u (r, collarHopfFullChart C x₀ x)) := by
  have hc : ContinuousAt (fun t : ℝ ↦ (t, collarHopfFullChart C x₀ x)) r :=
    continuous_id.continuousAt.prodMk continuous_const.continuousAt
  have heq : (fun t ↦ hopfCollarRDeriv (collarHopfReconstruct C x₀ u) t x) =ᶠ[𝓝 r]
      (fun t ↦ WithLp.toLp 2 (ckTimeDerivative u (t, collarHopfFullChart C x₀ x))) := by
    filter_upwards [hc.eventually hu.eventually_analyticAt] with t ht
    exact collarHopfReconstruct_rDeriv C x₀ u t x ht.differentiableAt
  rw [heq.deriv_eq]
  have ht : AnalyticAt ℝ (ckTimeDerivative u) (r, collarHopfFullChart C x₀ x) :=
    ((ContinuousLinearMap.apply ℝ V ckTimeDirection).analyticAt _).comp hu.fderiv
  exact collarHopfReconstruct_rDeriv C x₀ (ckTimeDerivative u) r x ht.differentiableAt

/-- The actual native inverse PDE is exactly the original full-coordinate CK equation.
Source: main.tex5.3. All original derivatives and both sides are identified for the SAME map;
this works in both directions, so every native competitor yields a genuine CK competitor. -/
theorem collarHopfReconstruct_inversePDE_iff (u : CKJoint d → V) (r : ℝ) (q : CKX d)
    (hq : q ∈ (collarHopfFullChart C x₀).target) (hu : AnalyticAt ℝ u (r, q)) :
    let G := collarHopfReconstruct C x₀ u
    let x := (collarHopfFullChart C x₀).symm q
    deriv (fun t ↦ hopfCollarRDeriv G t x) r =
      (hopfCollarSquarePairing C G r x).inverse (hopfCollarSquareForcing C G r x) ↔
        ckSecondTimeDerivative u (r, q) =
          collarHopfLocalRHS C x₀ (collarHopfSolutionJet C u (r, q)) := by
  dsimp only
  have hu' : AnalyticAt ℝ u
      (r, collarHopfFullChart C x₀ ((collarHopfFullChart C x₀).symm q)) := by
    rw [(collarHopfFullChart C x₀).right_inv hq]
    exact hu
  rw [collarHopfReconstruct_acceleration C x₀ u r _ hu',
    (collarHopfFullChart C x₀).right_inv hq,
    collarHopfReconstruct_pairing C x₀ u r q hq hu,
    collarHopfReconstruct_forcing C x₀ u r q hq hu]
  constructor
  · intro h
    exact congrArg WithLp.ofLp h
  · intro h
    exact congrArg (WithLp.toLp 2) h

end ChartJet

#print axioms collarHopfReconstruct_pairing
#print axioms collarHopfReconstruct_forcing
#print axioms collarHopfReconstruct_acceleration
#print axioms collarHopfReconstruct_inversePDE_iff
#print axioms collarHopfSolutionJet
#print axioms collarHopfReconstruct_chart_germ
#print axioms collarHopfReconstruct_rDeriv_chart_germ
#print axioms collarHopfReconstruct_columns
#print axioms collarHopfReconstruct_mixed
#print axioms collarHopf_dataHessian_germ
#print axioms collarHopf_first_of_chart_germ
#print axioms collarHopf_second_of_chart_germ
#print axioms collarHopfReconstruct
#print axioms collarHopf_fderiv_slice
#print axioms collarHopf_spatial_slice
#print axioms collarHopf_hessian_slice
#print axioms collarHopfReconstruct_rDeriv
#print axioms collarHopfJetColumns_initial
#print axioms collarHopfLocalRHS_initial_analyticAt
#print axioms collarHopfLocalCK_coordinates
#print axioms collarHopfJetFirst_initial
#print axioms collarHopfJetSecond_initial
#print axioms collarHopf_fderiv_coordinates
#print axioms collarHopf_second_fderiv_coordinates
#print axioms collarHopfDeriv_equiv
#print axioms collarHopfJetPairing_analyticAt
#print axioms collarHopfLocalRHS_analyticAt
#print axioms collarHopfJetMixed_analyticAt
#print axioms collarHopfJetSecond_analyticAt
#print axioms collarHopfJetColumns_analyticAt
#print axioms collarHopfJetForcing_analyticAt
#print axioms collarHopfJetFirst
#print axioms collarHopfJetSecond
#print axioms collarHopfJetMixed
#print axioms collarHopfJetColumns
#print axioms collarHopfJetForcing
#print axioms collarHopfLocalRHS
#print axioms collarHopfJetFirst_analyticAt
end GlobalEmbedding.Paper
