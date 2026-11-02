import NormalPolar.ActualRepairModelFirstDefectTotalCoordinates
import Probes.ActualSecondaryRawTensorForcing

/-! The true signed negative quadratic tensor of an arbitrary common Unit
array is covariant under the actual original source charts. Total derivatives
commute with the genuine local chart equivalence, so no global phase or amplitude
smoothness is imposed. Both inverse-chart Jacobian slots remain explicit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter IsManifold
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
variable {M Label : Type*} {m d N : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

theorem actualRepairModelFirstDefect_quadratic_forcing_chart_transfer
    (phase : Label → Ep × M → ℝ) (R Q : Label → Ep × M → V) (tau : ℝ)
    (e1 e2 : OpenPartialHomeomorph M D)
    (he1 : e1 ∈ maximalAtlas IM ∞ M) (he2 : e2 ∈ maximalAtlas IM ∞ M)
    (z : X) (hz : z.2 ∈ e2.target) (h12 : e2.symm z.2 ∈ e1.source)
    (nu mu : Label) (q : Fin 4) :
    let Hobs := fun (e : OpenPartialHomeomorph M D) (y : X) =>
      incrementsSecondaryQuadraticForcing (fun l b x => phase l (b,e.symm x)) tau
        (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (b,e.symm x))
        (fun l b (_ : Unit) x => Q l (b,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) nu mu q y
    let Phi := fun y : X => (y.1,e1 (e2.symm y.2))
    let J := fderiv ℝ (e1 ∘ e2.symm) z.2
    actualRealTensorAssembly (Hobs e2 z) =
      (actualRealTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J ∧
    actualImaginaryTensorAssembly (Hobs e2 z) =
      (actualImaginaryTensorAssembly (Hobs e1 (Phi z))).bilinearComp J J := by
  intro Hobs Phi J
  let p := e2.symm z.2
  have he1m : e1.MDifferentiable IM 𝓘(ℝ,D) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he1).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he1).mdifferentiableOn (by simp)⟩
  have he2m : e2.MDifferentiable IM 𝓘(ℝ,D) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he2).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he2).mdifferentiableOn (by simp)⟩
  let V1 : D →L[ℝ] TangentSpace IM p := mfderiv 𝓘(ℝ,D) IM e1.symm (e1 p)
  let V2 : D →L[ℝ] TangentSpace IM p := mfderiv 𝓘(ℝ,D) IM e2.symm z.2
  have hJ : J = (mfderiv IM 𝓘(ℝ,D) e1 p).comp V2 := by
    have hh := mfderiv_comp z.2 (he1m.mdifferentiableAt h12) (he2m.mdifferentiableAt_symm hz)
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hV : V1.comp J = V2 := by
    rw [hJ]
    change ((mfderiv 𝓘(ℝ,D) IM e1.symm (e1 p)).comp
      (mfderiv IM 𝓘(ℝ,D) e1 p)).comp V2 = V2
    rw [he1m.symm_comp_deriv h12]
    rfl
  let C : Label → TangentSpace IM p →L[ℝ] (Fin N → ℂ) := fun l =>
    ContinuousLinearMap.pi (fun co =>
      (incrementsFreeComplexCoordinate co).comp
        (round4PrescribedNativeCoefficient (I := IM) false (phase l) tau (R l) (Q l) (z.1,p)) +
      Complex.I • (incrementsFreeComplexCoordinate co).comp
        (round4PrescribedNativeCoefficient (I := IM) true (phase l) tau (R l) (Q l) (z.1,p)))
  let C1 := fun l => (C l).comp V1
  let C2 := fun l => (C l).comp V2
  have hC (l : Label) : C2 l = (C1 l).comp J := by
    change (C l).comp V2 = ((C l).comp V1).comp J
    rw [← hV]
    rfl
  have hnative (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
      (x : D) (hx : x ∈ e.target) (hp : e.symm x = p) : ∀ l i,
      incrementsSecondaryPhysicalCoefficient (fun l b x => phase l (b,e.symm x)) tau
        (fun (_ : Label) (_ : Ep) (_ : Unit) _ => 1)
        (fun l b (_ : Unit) x => R l (b,e.symm x))
        (fun l b (_ : Unit) x => Q l (b,e.symm x))
        (fun i _ => EuclideanSpace.single i 1) (z.1,x) l i =
        C l (mfderiv 𝓘(ℝ,D) IM e.symm x (EuclideanSpace.single i 1)) := by
    intro l i
    funext co
    have hh := actualRepairModelFirstDefect_observed_coefficient_total e he (phase l) (R l) (Q l)
      tau z.1 x (EuclideanSpace.single i 1) hx co
    dsimp only [incrementsSecondaryPhysicalCoefficient]
    rw [hh]
    change
      (round4PrescribedNativeCoefficient (I := IM) false (phase l) tau (R l) (Q l) (z.1,e.symm x)
        (mfderiv 𝓘(ℝ,D) IM e.symm x (EuclideanSpace.single i 1)) co : ℂ) +
      Complex.I * (round4PrescribedNativeCoefficient (I := IM) true (phase l) tau (R l) (Q l) (z.1,e.symm x)
        (mfderiv 𝓘(ℝ,D) IM e.symm x (EuclideanSpace.single i 1)) co : ℂ) = _
    rw [hp]
    rfl
  have hc1 := hnative e1 he1 (e1 p) (e1.map_source h12) (e1.left_inv h12)
  have hc2 := hnative e2 he2 z.2 hz rfl
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
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_quadratic_forcing_chart_transfer
