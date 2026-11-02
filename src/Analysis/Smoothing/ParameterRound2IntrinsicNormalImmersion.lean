import Probes.ActualOriginalNormalPointPreparation
import Probes.ActualOriginalNormalAndImmersionPreparation
import Smoothing.ParameterRound2IntrinsicNormalField

/-! A genuine new unit free normal for the perturbed actual map. The reference
normal is the OLD map's unit phase-free field. Original two-jet closeness
internally supplies new-map immersion, every new first/transverse reserve and the normalization
margin 1/2. The same literal new field is smooth on the full prepared open set,
free on the ORIGINAL phase kernel, and has all requested joint slow jets.
The perturbation threshold precedes the derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance prepFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance prepFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance prepHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance prepHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance prepFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance prepFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem parameterRound2_intrinsic_normal_and_immersion_preparation
    (cF cT MH0 : ℝ) (hcF : 0 < cF) (hcT : 0 < cT) (hMH0 : 0 ≤ MH0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (j : ℕ) (MA MH Mv : ℝ),
      0 ≤ MA → 0 ≤ MH → 0 ≤ Mv → ∃ C : ℝ, 0 ≤ C ∧ ∀
      (F0 F : Ep → M → V)
      (hF0 : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F0 p))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (psi : Ep → M → ℝ) (e : Ep → OpenPartialHomeomorph M D)
      (_he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
      (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
      (_hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
      (_hpsi : ∀ z ∈ O, MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
      (_hadapt : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = z.2 0)
      (_hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
      (vref : Ep × M → V) (_hv0 : ContDiffOn ℝ ∞ (fun z : X => vref (z.1,(e z.1).symm z.2)) O)
      (_hOldLegal : ∀ z ∈ O, ∃ normal : normalSpace (I := 𝓙) (F0 z.1) ((e z.1).symm z.2),
        (normal : V) = (fun z : X => vref (z.1,(e z.1).symm z.2)) z ∧ ‖normal‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F0 z.1) (hF0 z.1) ((e z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) u.val w.val)) : V)
          (normal : V) = 0)
      (_hFirst : ∀ z ∈ O, ∀ w : D, cF*‖w‖^2 ≤ ‖fderiv ℝ (F0 z.1 ∘ (e z.1).symm) z.2 w‖^2)
      (_hFrame : ∀ z ∈ O, ∀ w : Tdata, cT*‖w‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F0 z.1) (hF0 z.1) (e z.1).symm z.2 w‖^2)
      (_hHessian0 : ∀ z ∈ O, ‖fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e z.1).symm)) z.2‖ ≤ MH0)
      (_hD : ∀ z ∈ O, ‖fderiv ℝ (F0 z.1 ∘ (e z.1).symm) z.2-
        fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2‖ ≤ epsilon)
      (_hH : ∀ z ∈ O, ‖fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2-
        fderiv ℝ (fderiv ℝ (F0 z.1 ∘ (e z.1).symm)) z.2‖ ≤ epsilon)
      (ell : ℝ) (_hell : 0 < ell),
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA) →
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH) →
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k (fun z : X => vref (z.1,(e z.1).symm z.2)) z‖ ≤ Mv) →
      (∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2))) ∧
      ContDiffOn ℝ ∞ ((fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref (z.1,(e z.1).symm z.2))) O ∧
      (∀ z ∈ O, ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (normal : V) = (fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref (z.1,(e z.1).symm z.2)) z ∧ ‖normal‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F z.1) (hF z.1) ((e z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) u.val w.val)) : V)
          (normal : V) = 0) ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        ((fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref (z.1,(e z.1).symm z.2))) z‖ ≤ C := by
  obtain ⟨epsilon,hepsilon,hPreparation⟩ := actual_original_reference_normal_and_immersion_preparation
    (m := m) (N := N) (Ep := Ep) (M := M) cF cT MH0 hcF hcT hMH0
  refine ⟨epsilon,hepsilon,?_⟩
  intro j MA MH Mv hMA hMH hMv
  obtain ⟨C,hC,hPrepared⟩ := hPreparation j MA MH Mv hMA hMH hMv
  refine ⟨C,hC,?_⟩
  intro F0 F hF0 hF psi e he O S hO hSO hcoord hpsi hadapt hJoint
    vref hv0 hOldLegal hFirst hFrame hHessian0 hD hH ell hell hAj hHj hvj
  let v0 := fun z : X => vref (z.1,(e z.1).symm z.2)
  let normal := fun z : X => parameterRound2_intrinsicUnitFreeNormalField F hF psi vref
    (z.1,(e z.1).symm z.2)
  obtain ⟨hImm,hSmooth,hLegal,hBound⟩ := hPrepared F0 F hF0 hF psi e he O S hO hSO hcoord hpsi
    hadapt hJoint v0 hv0 hOldLegal hFirst hFrame hHessian0 hD hH ell hell hAj hHj hvj
  have hEq : EqOn (actualOriginalUnitFreeNormalField F hF e v0) normal O :=
    (parameterRound2_actual_normal_field_eq_intrinsic_on F hF psi e he O hO hcoord hpsi hadapt vref).2
  refine ⟨hImm,hSmooth.congr (fun z hz => (hEq hz).symm),?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,hunit,hfree⟩ := hLegal z hz
    exact ⟨v,hv.trans (hEq hz),hunit,hfree⟩
  · intro k hk z hz
    have hg : actualOriginalUnitFreeNormalField F hF e v0 =ᶠ[𝓝 z] normal :=
      eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => hEq hw)
    rw [← (hg.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hBound k hk z hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.parameterRound2_intrinsic_normal_and_immersion_preparation
