import Probes.ActualSecondaryLocalizedForcingSupport
import GlobalEmbedding.Paper.IncrementsSecondaryQuadraticForcing

/-! The original negative signed quadratic forcing produces a native real
and imaginary tensor. The fixed assembly retains all ordered entries and
uses only the original grouped primary coefficients. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ
local notation "CMatrix" => Fin (m+1) → Fin (m+1) → ℂ

private local instance rawTensorSemi : SeminormedAddCommGroup Tensor := ContinuousLinearMap.toSeminormedAddCommGroup
private local instance rawTensorNormed : NormedAddCommGroup Tensor := ContinuousLinearMap.toNormedAddCommGroup
private local instance rawTensorSpace : NormedSpace ℝ Tensor := ContinuousLinearMap.toNormedSpace

def actualRealArrayTensorAssembly : Source →L[ℝ] Tensor :=
  actualRealTensorAssembly.comp (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j : (Fin (m+1) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Source →L[ℝ] (Fin (m+1) → ℝ))))

 theorem actualRealArrayTensorAssembly_basis (H : Source) (i j : Fin (m+1)) :
    actualRealArrayTensorAssembly H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = H i j := by
  change actualRealTensorAssembly (fun i j => (H i j : ℂ)) _ _ = _
  rw [actualRealTensorAssembly_basis, Complex.ofReal_re]

 theorem actualRealTensorAssembly_eq_realArray (H : CMatrix) :
    actualRealTensorAssembly H = actualRealArrayTensorAssembly (fun i j => (H i j).re) := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  rw [actualRealTensorAssembly_basis, actualRealArrayTensorAssembly_basis]

 theorem actualImaginaryTensorAssembly_eq_realArray (H : CMatrix) :
    actualImaginaryTensorAssembly H = actualRealArrayTensorAssembly (fun i j => (H i j).im) := by
  apply actual_bilinear_tensor_eq_of_basis
  intro i j
  rw [actualImaginaryTensorAssembly_basis, actualRealArrayTensorAssembly_basis]

 theorem actual_secondary_quadratic_native_forcing_profiles
    (n N : ℕ) (MD : ℝ) (hMD : 0 ≤ MD) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ep Label Sub : Type*} [Fintype Sub] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
        (phi : Label → Ep → D → ℝ) (tau : ℝ) (chi : Label → Ep → Sub → D → ℝ)
        (P Q : Label → Ep → Sub → D → EuclideanSpace ℝ (Fin N)) (nu mu : Label) (q : Fin 4)
        (O S : Set (Ep × D)) (hO : IsOpen O) (hSO : S ⊆ O) (ell delta : ℝ) (hell : 0 < ell)
        (hnu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z nu) O)
        (hmu : ContDiffOn ℝ ∞ (fun z => incrementsSecondaryPhysicalCoefficient
          phi tau chi P Q (fun i _ => EuclideanSpace.single i 1) z mu) O)
        (hnub : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y nu) z‖ ≤ MD*|delta|)
        (hmub : ∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r
          (fun y => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
            (fun i _ => EuclideanSpace.single i 1) y mu) z‖ ≤ MD*|delta|),
      let H := incrementsSecondaryQuadraticForcing phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) nu mu q
      let HR := fun z => actualRealTensorAssembly (H z)
      let HI := fun z => actualImaginaryTensorAssembly (H z)
      ContDiffOn ℝ ∞ HR O ∧ ContDiffOn ℝ ∞ HI O ∧
      (∀ z, ∀ v w : D, HR z v w = HR z w v) ∧
      (∀ z, ∀ v w : D, HI z v w = HI z w v) ∧
      (tsupport HR ⊆ tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) z nu) ∩
        tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) z mu)) ∧
      (tsupport HI ⊆ tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) z nu) ∩
        tsupport (fun z => incrementsSecondaryPhysicalCoefficient phi tau chi P Q
        (fun i _ => EuclideanSpace.single i 1) z mu)) ∧
      (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r HR z‖ ≤ C*delta^2) ∧
      (∀ r ≤ n, ∀ z ∈ S, ell^r*‖iteratedFDeriv ℝ r HI z‖ ≤ C*delta^2) := by
  obtain ⟨CH,hCH,hdata⟩ := increments_secondary_quadratic_forcing_data n N MD hMD
  refine ⟨‖actualRealArrayTensorAssembly (m := m)‖*CH, by positivity, ?_⟩
  intro Ep Label Sub _ _ _ phi tau chi P Q nu mu q O S hO hSO ell delta hell hnu hmu hnub hmub H HR HI
  obtain ⟨hR,hI,hsymm,hsR,hsI,hRb,hIb⟩ := hdata phi tau chi P Q
    (fun i _ => EuclideanSpace.single i 1) nu mu q O S hO hSO ell delta hell hnu hmu hnub hmub
  have hReq : HR = actualRealArrayTensorAssembly ∘ (fun z i j => (H z i j).re) := by
    funext z
    exact actualRealTensorAssembly_eq_realArray (H z)
  have hIeq : HI = actualRealArrayTensorAssembly ∘ (fun z i j => (H z i j).im) := by
    funext z
    exact actualImaginaryTensorAssembly_eq_realArray (H z)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hReq]
    exact actualRealArrayTensorAssembly.contDiff.comp_contDiffOn hR
  · rw [hIeq]
    exact actualRealArrayTensorAssembly.contDiff.comp_contDiffOn hI
  · intro z v w
    exact actual_real_tensor_assembly_symmetric (H z) (hsymm z) v w
  · intro z v w
    exact actual_imag_tensor_assembly_symmetric (H z) (hsymm z) v w
  · rw [hReq]
    exact (tsupport_comp_subset (map_zero actualRealArrayTensorAssembly) _).trans hsR
  · rw [hIeq]
    exact (tsupport_comp_subset (map_zero actualRealArrayTensorAssembly) _).trans hsI
  · intro r hr z hz
    rw [hReq]
    exact (slow_linear_jet_bound actualRealArrayTensorAssembly O hO _ hR r ell (CH*delta^2)
      hell.le z (hSO hz) (hRb r hr z hz)).trans_eq (by ring)
  · intro r hr z hz
    rw [hIeq]
    exact (slow_linear_jet_bound actualRealArrayTensorAssembly O hO _ hI r ell (CH*delta^2)
      hell.le z (hSO hz) (hIb r hr z hz)).trans_eq (by ring)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_secondary_quadratic_native_forcing_profiles
