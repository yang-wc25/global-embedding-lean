import Probes.ActualOriginalNormalPointPreparation

/-! A genuine new unit free normal for the perturbed actual map. The reference
normal is the OLD map's unit phase-free field. Original two-jet closeness
internally supplies every new first/transverse reserve and the normalization
margin 1/2. The same literal new field is smooth on the full prepared open set,
free on the ORIGINAL phase kernel, and has all requested joint slow jets.
The perturbation threshold precedes the derivative order. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
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

theorem actual_original_reference_unit_free_normal_preparation
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
      (_hImm : ∀ z ∈ O, Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2)))
      (v0 : X → V) (_hv0 : ContDiffOn ℝ ∞ v0 O)
      (_hOldLegal : ∀ z ∈ O, ∃ normal : normalSpace (I := 𝓙) (F0 z.1) ((e z.1).symm z.2),
        (normal : V) = v0 z ∧ ‖normal‖ = 1 ∧
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
      (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k v0 z‖ ≤ Mv) →
      ContDiffOn ℝ ∞ (actualOriginalUnitFreeNormalField F hF e v0) O ∧
      (∀ z ∈ O, ∃ normal : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (normal : V) = actualOriginalUnitFreeNormalField F hF e v0 z ∧ ‖normal‖ = 1 ∧
        let xi := (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))
        ∀ u w : xi.ker, inner ℝ
          ((trueSecondForm (F z.1) (hF z.1) ((e z.1).symm z.2)
            (symmetricSquareProduct (TangentSpace 𝓙 ((e z.1).symm z.2)) u.val w.val)) : V)
          (normal : V) = 0) ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
        (actualOriginalUnitFreeNormalField F hF e v0) z‖ ≤ C := by
  obtain ⟨epsilon,hepsilon,hReserve⟩ := actual_original_two_jet_free_normal_reserve
    (m := m) (N := N) (M := M) cF cT MH0 hcF hcT hMH0
  refine ⟨epsilon,hepsilon,?_⟩
  intro j MA MH Mv hMA hMH hMv
  obtain ⟨C,hC,hJets⟩ := actual_original_unit_free_normal_field_slow_jets
    (m := m) (N := N) (Ep := Ep) (M := M) j (cF/4) (cT/4) MA MH (1/2) Mv
    (by positivity) (by positivity) hMA hMH (by norm_num) hMv
  refine ⟨C,hC,?_⟩
  intro F0 F hF0 hF psi e he O S hO hSO hcoord hpsi hadapt hJoint hImm
    v0 hv0 hOldLegal hFirst hFrame hHessian0 hD hH ell hell hAj hHj hvj
  let slice := fun p => {y : D | (p,y) ∈ O}
  have hSlice (p : Ep) : IsOpen (slice p) := hO.preimage (continuous_const.prodMk continuous_id)
  have hNew (z : X) (hz : z ∈ O) :
      (∀ w : D, (cF/4)*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2) ∧
      (∀ w : Tdata, (cT/4)*‖w‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 w‖^2) ∧
      (1/2 : ℝ) ≤ ‖actualOriginalFreeNormalFieldRaw F hF e v0 z‖ := by
    obtain ⟨normal,hn,hunit,hfree⟩ := hOldLegal z hz
    have hb := actual_increment_transverse_kernel_of_phase_free (F0 z.1) (hF0 z.1) (psi z.1)
      (e z.1) (he z.1) (slice z.1) (hSlice z.1) (fun y hy => hcoord (z.1,y) hy)
      z.2 hz (hpsi z hz) (fun y hy => hadapt (z.1,y) hy) normal hfree
    have hh := hReserve (F0 z.1) (F z.1) (hF0 z.1) (hF z.1) (e z.1) (he z.1) z.2
      (hcoord z hz) (hFirst z hz) (hFrame z hz) (hHessian0 z hz) (hD z hz) (hH z hz)
      normal hunit hb
    simpa only [actualOriginalFreeNormalFieldRaw,hn] using hh
  obtain ⟨hSmooth,hLegal,hBound⟩ := hJets F hF e he O S hO hSO hcoord hJoint hImm ell hell
    (fun z hz => (hNew z (hSO hz)).1) (fun z hz => (hNew z hz).2.1) hAj hHj v0 hv0 hvj
    (fun z hz => (hNew z (hSO hz)).2.2)
  have hnonzero (z : X) (hz : z ∈ O) : actualOriginalFreeNormalFieldRaw F hF e v0 z ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hNew z hz).2.2)
  refine ⟨hSmooth.mono (fun z hz => ⟨hz,hnonzero z hz⟩),?_,hBound⟩
  intro z hz
  obtain ⟨normal,hn,hunit,hb⟩ := actual_original_unit_free_normal_field_beta_at
    F hF e he v0 z (hcoord z hz) (hnonzero z hz)
  refine ⟨normal,hn,hunit,?_⟩
  exact actual_increment_phase_free_of_transverse_kernel (F z.1) (hF z.1) (psi z.1)
    (e z.1) (he z.1) (slice z.1) (hSlice z.1) (fun y hy => hcoord (z.1,y) hy)
    z.2 hz (hpsi z hz) (fun y hy => hadapt (z.1,y) hy) normal hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_reference_unit_free_normal_preparation
