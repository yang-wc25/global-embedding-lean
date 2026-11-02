import Probes.ActualIncrementPrimaryCoefficientPrimitives
import Probes.ActualSecondaryRawTensorForcing
import Smoothing.ParameterRound2MeanPrimitives

/-! The SAME signed negative quadratic forcing is a native covariant tensor.
Its four original conjugation branches, negative one-eighth coefficient and
the delta already contained in the physical coefficient are unchanged. The
actual inverse-chart differentials, not a supplied tensor transformation law,
give its two-Jacobian change between arbitrary observation charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators ComplexConjugate
namespace GlobalEmbedding.Continuation

section Algebra
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {N : ℕ}

private local instance quadraticInnerNormed : NormedAddCommGroup (Y →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance quadraticInnerSpace : NormedSpace ℝ (Y →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
private local instance quadraticOuterNormed : NormedAddCommGroup (Y →L[ℝ] Y →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance quadraticOuterSpace : NormedSpace ℝ (Y →L[ℝ] Y →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

private def signedQuadraticTensor
    (A B : Y →L[ℝ] (Fin N → ℂ)) (q : Fin 4) : Y →L[ℝ] Y →L[ℝ] ℂ :=
  let cj := (ContinuousLinearEquiv.piCongrRight fun _ : Fin N => Complex.conjCLE).toContinuousLinearMap
  let f := ![A,A,cj.comp A,cj.comp A] q
  let g := ![B,cj.comp B,B,cj.comp B] q
  let b : Y →L[ℝ] Y →L[ℝ] ℂ := ∑ c : Fin N,
    (ContinuousLinearMap.mul ℝ ℂ).bilinearComp
      ((ContinuousLinearMap.proj c).comp f) ((ContinuousLinearMap.proj c).comp g)
  show Y →L[ℝ] Y →L[ℝ] ℂ from -(1/8 : ℝ) • (b+b.flip)

private theorem signedQuadraticTensor_apply
    (A B : Y →L[ℝ] (Fin N → ℂ)) (q : Fin 4) (v w : Y) :
    signedQuadraticTensor A B q v w =
      -(1/8 : ℂ) *
        (![A v ⬝ᵥ B w, A v ⬝ᵥ (fun c => conj (B w c)),
          (fun c => conj (A v c)) ⬝ᵥ B w,
          (fun c => conj (A v c)) ⬝ᵥ (fun c => conj (B w c))] q +
         ![A w ⬝ᵥ B v, A w ⬝ᵥ (fun c => conj (B v c)),
          (fun c => conj (A w c)) ⬝ᵥ B v,
          (fun c => conj (A w c)) ⬝ᵥ (fun c => conj (B v c))] q) := by
  fin_cases q <;> simp [signedQuadraticTensor, dotProduct, Complex.real_smul, mul_add]

private def tensorRealPart (H : Y →L[ℝ] Y →L[ℝ] ℂ) : Y →L[ℝ] Y →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Y ℂ ℝ) Complex.reCLM).comp H

private def tensorImagPart (H : Y →L[ℝ] Y →L[ℝ] ℂ) : Y →L[ℝ] Y →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Y ℂ ℝ) Complex.imCLM).comp H

private theorem signedQuadraticTensor_comp
    (A B : Y →L[ℝ] (Fin N → ℂ)) (q : Fin 4)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (J : Z →L[ℝ] Y) :
    signedQuadraticTensor (A.comp J) (B.comp J) q =
      (signedQuadraticTensor A B q).bilinearComp J J := by
  ext v w
  simp only [signedQuadraticTensor_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.bilinearComp_apply]

private theorem tensorRealPart_comp
    (H : Y →L[ℝ] Y →L[ℝ] ℂ)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (J : Z →L[ℝ] Y) :
    tensorRealPart (H.bilinearComp J J) = (tensorRealPart H).bilinearComp J J := by
  rfl

private theorem tensorImagPart_comp
    (H : Y →L[ℝ] Y →L[ℝ] ℂ)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (J : Z →L[ℝ] Y) :
    tensorImagPart (H.bilinearComp J J) = (tensorImagPart H).bilinearComp J J := by
  rfl

end Algebra

section Actual
variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

/-- No source, coefficient or tensor-covariance assertion is supplied. Original
primitive data supplies the actual extension derivatives; the native coefficient
bridge and the actual chart inverse identity give both real tensor channels. -/
theorem actual_original_quadratic_forcing_chart_transfer
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau delta : ℝ)
    (e1 e2 : OpenPartialHomeomorph M D)
    (he1 : ContMDiffOn I 𝓘(ℝ,D) ∞ e1 e1.source)
    (he1Inv : ContMDiffOn 𝓘(ℝ,D) I ∞ e1.symm e1.target)
    (he2 : ContMDiffOn I 𝓘(ℝ,D) ∞ e2 e2.source)
    (he2Inv : ContMDiffOn 𝓘(ℝ,D) I ∞ e2.symm e2.target)
    (z : X) (hz : z.2 ∈ e2.target) (h12 : e2.symm z.2 ∈ e1.source)
    (hzW : (z.1,e2.symm z.2) ∈ W) (nu mu : Λ) (q : Fin 4) :
    let Hobs := fun (e : OpenPartialHomeomorph M D) (y : X) =>
      incrementsSecondaryQuadraticForcing
        (fun a t x => g.phase a (t,e.symm x)) tau (fun _ _ _ _ => 1)
        (fun a t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true a b (t,e.symm x))
        (fun a t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false a b (t,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) nu mu q y
    let Phi := fun y : X => (y.1,e1 (e2.symm y.2))
    let J := fderiv ℝ (e1 ∘ e2.symm) z.2
    actualRealTensorAssembly (Hobs e2 z) =
        (actualRealTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J ∧
      actualImaginaryTensorAssembly (Hobs e2 z) =
        (actualImaginaryTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J := by
  intro Hobs Phi J
  let p := e2.symm z.2
  have he1m : e1.MDifferentiable I 𝓘(ℝ,D) :=
    ⟨he1.mdifferentiableOn (by simp),he1Inv.mdifferentiableOn (by simp)⟩
  have he2m : e2.MDifferentiable I 𝓘(ℝ,D) :=
    ⟨he2.mdifferentiableOn (by simp),he2Inv.mdifferentiableOn (by simp)⟩
  let V1 : D →L[ℝ] TangentSpace I p := mfderiv 𝓘(ℝ,D) I e1.symm (e1 p)
  let V2 : D →L[ℝ] TangentSpace I p := mfderiv 𝓘(ℝ,D) I e2.symm z.2
  have hJ : J = (mfderiv I 𝓘(ℝ,D) e1 p).comp V2 := by
    have hh := mfderiv_comp z.2 (he1m.mdifferentiableAt h12) (he2m.mdifferentiableAt_symm hz)
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hV : V1.comp J = V2 := by
    rw [hJ]
    change ((mfderiv 𝓘(ℝ,D) I e1.symm (e1 p)).comp
      (mfderiv I 𝓘(ℝ,D) e1 p)).comp V2 = V2
    rw [he1m.symm_comp_deriv h12]
    rfl
  let C : Λ → TangentSpace I p →L[ℝ] (Fin N → ℂ) := fun a => delta •
    ContinuousLinearMap.pi (fun co =>
      (incrementsFreeComplexCoordinate co).comp
        (incrementsGlobalPrimaryCoefficient F hF g input length tau true a (z.1,p)) +
      Complex.I • (incrementsFreeComplexCoordinate co).comp
        (incrementsGlobalPrimaryCoefficient F hF g input length tau false a (z.1,p)))
  let C1 := fun a => (C a).comp V1
  let C2 := fun a => (C a).comp V2
  have hC (a : Λ) : C2 a = (C1 a).comp J := by
    change (C a).comp V2 = ((C a).comp V1).comp J
    rw [← hV]
    rfl
  have hnative (e : OpenPartialHomeomorph M D)
      (he : ContMDiffOn I 𝓘(ℝ,D) ∞ e e.source)
      (heInv : ContMDiffOn 𝓘(ℝ,D) I ∞ e.symm e.target)
      (x : D) (hx : x ∈ e.target) (hp : e.symm x = p) :
      ∀ a r,
      incrementsSecondaryPhysicalCoefficient
        (fun a t x => g.phase a (t,e.symm x)) tau (fun _ _ _ _ => 1)
        (fun a t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau true a b (t,e.symm x))
        (fun a t b x => delta • incrementsGlobalPrimaryExtension F hF g input length tau false a b (t,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) (z.1,x) a r =
        C a (mfderiv 𝓘(ℝ,D) I e.symm x (EuclideanSpace.single r 1)) := by
    have hxW : (z.1,e.symm x) ∈ W := by rw [hp]; exact hzW
    have hb := actual_original_observed_coefficient_native_from_primitives F hF g input length tau
      W h.hW primary h.hPrimary h.hPrimarySupport h.hSourceW h.hChart h.hChartInv h.hInverse
      h.hCombinedSupport h.hCut h.hNormal h.hArgument h.hEta h.hPositive h.hG h.hJ h.hT0 h.hA h.hB
      h.hSecond e he heInv z.1 x hx hxW
    intro a r
    funext co
    have ha := congrFun (congrFun
      (actual_original_primary_physical_coefficient_binding F hF g input length tau delta e (z.1,x) a) r) co
    rw [ha]
    simp only [Pi.smul_apply,hb,C,smul_apply,ContinuousLinearMap.pi_apply,
      add_apply,ContinuousLinearMap.comp_apply,Complex.real_smul,
      incrementsFreeComplexCoordinate,incrementsGlobalObservationVector,smul_eq_mul]
    rw [hp]
    rfl
  have hc1 := hnative e1 he1 he1Inv (e1 p) (e1.map_source h12) (e1.left_inv h12)
  have hc2 := hnative e2 he2 he2Inv z.2 hz rfl
  have hforce1 : ∀ i j, Hobs e1 (Phi z) i j =
      signedQuadraticTensor (C1 nu) (C1 mu) q (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro i j
    change Hobs e1 (z.1,e1 p) i j = _
    rw [signedQuadraticTensor_apply]
    simp only [Hobs,incrementsSecondaryQuadraticForcing,hc1,C1,ContinuousLinearMap.comp_apply,V1]
    rfl
  have hforce2 : ∀ i j, Hobs e2 z i j =
      signedQuadraticTensor (C2 nu) (C2 mu) q (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro i j
    change Hobs e2 (z.1,z.2) i j = _
    rw [signedQuadraticTensor_apply]
    simp only [Hobs,incrementsSecondaryQuadraticForcing,hc2,C2,ContinuousLinearMap.comp_apply,V2]
    rfl
  have hreal (e : OpenPartialHomeomorph M D) (y : X) (A B : D →L[ℝ] (Fin N → ℂ))
      (hb : ∀ i j, Hobs e y i j = signedQuadraticTensor A B q
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :
      actualRealTensorAssembly (Hobs e y) = tensorRealPart (signedQuadraticTensor A B q) := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    rw [actualRealTensorAssembly_basis,hb]
    rfl
  have himag (e : OpenPartialHomeomorph M D) (y : X) (A B : D →L[ℝ] (Fin N → ℂ))
      (hb : ∀ i j, Hobs e y i j = signedQuadraticTensor A B q
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :
      actualImaginaryTensorAssembly (Hobs e y) = tensorImagPart (signedQuadraticTensor A B q) := by
    apply actual_bilinear_tensor_eq_of_basis
    intro i j
    rw [actualImaginaryTensorAssembly_basis,hb]
    rfl
  constructor
  · rw [hreal e2 z (C2 nu) (C2 mu) hforce2,hreal e1 (Phi z) (C1 nu) (C1 mu) hforce1,
      hC nu,hC mu,signedQuadraticTensor_comp,tensorRealPart_comp]
  · rw [himag e2 z (C2 nu) (C2 mu) hforce2,himag e1 (Phi z) (C1 nu) (C1 mu) hforce1,
      hC nu,hC mu,signedQuadraticTensor_comp,tensorImagPart_comp]

end Actual
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_quadratic_forcing_chart_transfer
