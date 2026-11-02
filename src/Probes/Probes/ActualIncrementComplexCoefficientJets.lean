import Probes.ActualIncrementRealCoefficientJets

/-!
# Original complex first-order coefficients from primitive geometry

Real and imaginary channels are the original native conversion maps. Their
operator norms are retained explicitly; no isometric identification of Pi
complex coordinates with the Euclidean real coordinate norm is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

private local instance complexDDNormed (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexDDSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexDCNormed (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexDCSpace (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexCCNormed (m : ℕ) : NormedAddCommGroup ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexCCSpace (m : ℕ) : NormedSpace ℝ ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexRealANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexRealASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) := inferInstance
private local instance complexMidANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexMidASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexComplexANormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexComplexASpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) := inferInstance
private local instance complexRealJetNormed (m : ℕ) : NormedAddCommGroup ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))) := inferInstance
private local instance complexRealJetSpace (m : ℕ) : NormedSpace ℝ ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))) := inferInstance

def actualIncrementComplexBMap (m : ℕ) :
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      ((Fin (m+1) → ℂ) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ((ContinuousLinearMap.compL ℝ (Fin (m+1) → ℂ)
    (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)).flip incrementsModeRealPart).comp
      ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (m+1)))
        (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)) incrementsModeComplexInclude) +
  Complex.I •
    ((ContinuousLinearMap.compL ℝ (Fin (m+1) → ℂ)
      (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)).flip incrementsModeImagPart).comp
      ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (m+1)))
        (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)) incrementsModeComplexInclude)

def actualIncrementComplexAMap (m : ℕ) :
    ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (m+1))) →L[ℝ]
      ((EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ)) →L[ℝ] (Fin (m+1) → ℂ)) :=
  ((ContinuousLinearMap.compL ℝ
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ))
    (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (Fin (m+1) → ℂ)).flip
      ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (m+1)))
        (Fin (m+1) → ℂ) (EuclideanSpace ℝ (Fin (m+1)))) incrementsModeRealPart)).comp
    ((ContinuousLinearMap.compL ℝ
      (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
      (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)) incrementsModeComplexInclude) +
  Complex.I •
    ((ContinuousLinearMap.compL ℝ
      (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (Fin (m+1) → ℂ))
      (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
      (Fin (m+1) → ℂ)).flip
        ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (m+1)))
          (Fin (m+1) → ℂ) (EuclideanSpace ℝ (Fin (m+1)))) incrementsModeImagPart)).comp
      ((ContinuousLinearMap.compL ℝ
        (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))
        (EuclideanSpace ℝ (Fin (m+1))) (Fin (m+1) → ℂ)) incrementsModeComplexInclude)

def actualIncrementComplexAConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  ‖actualIncrementComplexAMap m‖ * actualIncrementRealAConstant m N j c cT MA MH

def actualIncrementComplexBConstant (m N j : ℕ) (c cT MA MH : ℝ) : ℝ :=
  ‖actualIncrementComplexBMap m‖ * actualIncrementRealBConstant m N j c cT MA MH

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ, D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m+1))) M]

/-- The fixed channel conversion is exactly the original complex A. -/
theorem actual_increment_complex_A_eq (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (e : OpenPartialHomeomorph M D) (x : D) :
    incrementsModeComplexFirstOrderA (I := 𝓙) F hF e.symm x =
      actualIncrementComplexAMap m (incrementsModeFirstOrderA (I := 𝓙) F hF e.symm x) := rfl

/-- The fixed channel conversion is exactly the original complex B. -/
theorem actual_increment_complex_B_eq (F : M → V)
    (hF : ContMDiff 𝓙 𝓘(ℝ, V) ∞ F) (e : OpenPartialHomeomorph M D) (x : D) :
    incrementsModeComplexFirstOrderB (I := 𝓙) F hF e.symm x =
      actualIncrementComplexBMap m (incrementsModeFirstOrderB (I := 𝓙) F hF e.symm x) := rfl

/-- The actual complex solver coefficients have all specified joint slow
jets from the same primitive first/Hessian fields and fixed frame reserves. -/
theorem actual_increment_complex_coefficients_slow_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hA : ContDiffOn ℝ ∞ (fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2) O)
    (hH : ContDiffOn ℝ ∞ (fun z : X =>
      fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2) O)
    (j : ℕ) (ell c cT MA MH : ℝ) (hell : 0 < ell) (hc : 0 < c) (hcT : 0 < cT)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hreserve : ∀ z ∈ O, ∀ v : D,
      c * ‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2)
    (hTreserve : ∀ z ∈ O, ∀ v : Tdata,
      cT * ‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (I := 𝓙)
        (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2)
    (hAj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) :
    (ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun y : X =>
        incrementsModeComplexFirstOrderA (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          actualIncrementComplexAConstant m N j c cT MA MH) ∧
    (ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2) O ∧
      ∀ k ≤ j, ∀ z ∈ O, ell^k * ‖iteratedFDeriv ℝ k (fun y : X =>
        incrementsModeComplexFirstOrderB (I := 𝓙) (F y.1) (hF y.1) (e y.1).symm y.2) z‖ ≤
          actualIncrementComplexBConstant m N j c cT MA MH) := by
  obtain ⟨hRA,hRB⟩ := actual_increment_real_coefficients_slow_jets F hF e he O hO hcoord
    hA hH j ell c cT MA MH hell hc hcT hMA hMH hreserve hTreserve hAj hHj
  let A := fun z : X => incrementsModeFirstOrderA (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
  let B := fun z : X => incrementsModeFirstOrderB (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2
  let LA := actualIncrementComplexAMap m
  let LB := actualIncrementComplexBMap m
  have hAe : (fun z : X => incrementsModeComplexFirstOrderA (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = LA ∘ A :=
    funext fun z => actual_increment_complex_A_eq (F z.1) (hF z.1) (e z.1) z.2
  have hBe : (fun z : X => incrementsModeComplexFirstOrderB (I := 𝓙)
      (F z.1) (hF z.1) (e z.1).symm z.2) = LB ∘ B :=
    funext fun z => actual_increment_complex_B_eq (F z.1) (hF z.1) (e z.1) z.2
  rw [hAe,hBe]
  constructor
  · refine ⟨LA.contDiff.comp_contDiffOn hRA.1, ?_⟩
    intro k hk z hz
    exact slow_linear_jet_bound LA O hO A hRA.1 k ell
      (actualIncrementRealAConstant m N j c cT MA MH) hell.le z hz (hRA.2 k hk z hz)
  · refine ⟨LB.contDiff.comp_contDiffOn hRB.1, ?_⟩
    intro k hk z hz
    exact slow_linear_jet_bound LB O hO B hRB.1 k ell
      (actualIncrementRealBConstant m N j c cT MA MH) hell.le z hz (hRB.2 k hk z hz)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_increment_complex_coefficients_slow_jets
