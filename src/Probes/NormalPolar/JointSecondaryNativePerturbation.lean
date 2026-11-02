import NormalPolar.JointSecondaryNativeGoodSmooth
import NormalPolar.JointSecondaryCompactGoodRadius

/-! Original smooth phases on a genuine chart and a compact carrier supply
a uniform original Good perturbation radius. Native continuity, covector
bounds and the radius are all constructed from those original data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped TensorProduct Topology ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance nativePerturbationRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance nativePerturbationSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def jointSecondaryPhaseCovector (psi : M → ℝ) (x : M) : TangentSpace IM x →L[ℝ] ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi x)).toContinuousLinearMap.comp
    (mfderiv IM 𝓘(ℝ,ℝ) psi x)

theorem jointSecondaryPhaseCovector_eq (psi : M → ℝ) (x : M) :
    jointSecondaryPhaseCovector psi x = mfderiv IM 𝓘(ℝ,ℝ) psi x := by
  ext v
  rfl

theorem jointSecondary_native_compact_phase_perturbation
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (psi phi : M → ℝ) (O : Set M) (hO : IsOpen O)
    (hpsi : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ psi O)
    (hphi : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phi O)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (heO : e.source ⊆ O) (C : Set M) (hC : IsCompact C) (hCe : C ⊆ e.source)
    (hgood : ∀ x ∈ C, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) psi x)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t : ℝ, |t| < epsilon → ∀ x ∈ C,
      GoodCovector F hF x
        (jointSecondaryPhaseCovector psi x + t • jointSecondaryPhaseCovector phi x) := by
  let S : Set D := e '' C
  have hS : IsCompact S := hC.image_of_continuousOn (e.continuousOn.mono hCe)
  have hSt : S ⊆ e.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hCe hx)
  have hpsiAt (y : D) (hy : y ∈ e.target) :
      MDifferentiableAt IM 𝓘(ℝ,ℝ) psi (e.symm y) :=
    (hpsi.contMDiffAt (hO.mem_nhds (heO (e.map_target hy)))).mdifferentiableAt (by simp)
  have hphiAt (y : D) (hy : y ∈ e.target) :
      MDifferentiableAt IM 𝓘(ℝ,ℝ) phi (e.symm y) :=
    (hphi.contMDiffAt (hO.mem_nhds (heO (e.map_target hy)))).mdifferentiableAt (by simp)
  have hps : ContDiffOn ℝ ∞ (psi ∘ e.symm) e.target :=
    (hpsi.comp (contMDiffOn_symm_of_mem_maximalAtlas he)
      (fun y hy => heO (e.map_target hy))).contDiffOn
  have hph : ContDiffOn ℝ ∞ (phi ∘ e.symm) e.target :=
    (hphi.comp (contMDiffOn_symm_of_mem_maximalAtlas he)
      (fun y hy => heO (e.map_target hy))).contDiffOn
  have hpsD := hps.fderiv_of_isOpen e.open_target (m := ∞) (by simp)
  have hphD := hph.fderiv_of_isOpen e.open_target (m := ∞) (by simp)
  have hnGood (y : D) (hy : y ∈ S) :
      LinearSecondFormGoodCovector (jointSecondaryNativePhaseOperator F e y).toLinearMap
        (fderiv ℝ (psi ∘ e.symm) y).toLinearMap := by
    apply (jointSecondary_native_phase_good_iff F hF e he psi y (hSt hy) (hpsiAt y (hSt hy))).mpr
    rcases hy with ⟨x,hx,rfl⟩
    exact (congrArg (fun z => GoodCovector F hF z (mfderiv IM 𝓘(ℝ,ℝ) psi z))
      (e.left_inv (hCe hx))).mpr (hgood x hx)
  obtain ⟨radius,hradius,hball⟩ := jointSecondary_compact_actual_good_radius
    (jointSecondaryNativePhaseOperator F e) (fderiv ℝ (psi ∘ e.symm)) S hS
    ((jointSecondary_native_phase_operator_smooth F hF hImm e he).continuousOn.mono hSt)
    (hpsD.continuousOn.mono hSt) hnGood
  obtain ⟨bound,hbound⟩ := hS.exists_bound_of_continuousOn (hphD.continuousOn.mono hSt)
  let B : ℝ := 1 + |bound|
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
  have hb (y : D) (hy : y ∈ S) : ‖fderiv ℝ (phi ∘ e.symm) y‖ ≤ B :=
    (hbound y hy).trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨radius / B,div_pos hradius hB,?_⟩
  intro t ht x hx
  have hy : e x ∈ S := ⟨x,hx,rfl⟩
  have hyT := hSt hy
  have hs : |t| * B < radius := (lt_div_iff₀ hB).mp ht
  have hnear : ‖(fderiv ℝ (psi ∘ e.symm) (e x) +
      t • fderiv ℝ (phi ∘ e.symm) (e x)) - fderiv ℝ (psi ∘ e.symm) (e x)‖ < radius := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb (e x) hy) (abs_nonneg t)).trans_lt hs
  have hn := hball (e x) hy _ hnear
  have hgradientPsi := jointSecondary_native_phase_gradient e he psi (e x) hyT (hpsiAt (e x) hyT)
  have hgradientPhi := jointSecondary_native_phase_gradient e he phi (e x) hyT (hphiAt (e x) hyT)
  rw [← jointSecondaryPhaseCovector_eq] at hgradientPsi hgradientPhi
  have hsum : (jointSecondaryPhaseCovector psi (e.symm (e x)) +
      t • jointSecondaryPhaseCovector phi (e.symm (e x))).comp
        (jointSecondaryNativeTangentMap e (e x)) =
      fderiv ℝ (psi ∘ e.symm) (e x) + t • fderiv ℝ (phi ∘ e.symm) (e x) := by
    ext v
    exact congrArg₂ (fun a b : ℝ => a + t*b)
      (congrArg (fun L : D →L[ℝ] ℝ => L v) hgradientPsi).symm
      (congrArg (fun L : D →L[ℝ] ℝ => L v) hgradientPhi).symm
  have hactual := (jointSecondary_native_good_iff F hF e he (e x) hyT
      (jointSecondaryPhaseCovector psi (e.symm (e x)) +
        t • jointSecondaryPhaseCovector phi (e.symm (e x)))).mp (by
    rw [hsum]
    exact hn)
  exact (congrArg (fun z => GoodCovector F hF z
    (jointSecondaryPhaseCovector psi z + t • jointSecondaryPhaseCovector phi z))
    (e.left_inv (hCe hx))).mp hactual

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_native_compact_phase_perturbation
