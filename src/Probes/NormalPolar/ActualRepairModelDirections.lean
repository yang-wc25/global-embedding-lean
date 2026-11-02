import NormalPolar.ActualRepairModelChart
import NormalPolar.FullResponseTail
import GlobalEmbedding.Offline.RepairDisplacementBudget

/-!
# All original parameter directions from the actual native columns

The native derivative is linear in its direction. Finite summation in the
original coordinate Cj norm gives the honest fixed factor p for Pi^p. No
parameter ball or coordinate norm is changed, and dimension zero is included.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade
variable {n N p : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,E)

/-- Uniform bounds for the actual standard columns yield the original bound
for every parameter direction, with the explicit finite-dimensional factor. -/
theorem actualRepairModel_parameter_direction_of_columns
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    {U : Set (Fin p → ℝ)} (hU : IsOpen U)
    (F : (Fin p → ℝ) → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ,Fin p → ℝ)).prod IM) 𝓘(ℝ,V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (u : Fin p → ℝ) (hu : u ∈ U) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hcolumns : ∀ a : Fin p, probeAtlasCj A j
      (fun x => fderiv ℝ (fun v => F v x) u (Pi.single a 1)) ≤ ENNReal.ofReal C)
    (direction : Fin p → ℝ) :
    probeAtlasCj A j (fun x => fderiv ℝ (fun v => F v x) u direction) ≤
      ENNReal.ofReal ((p : ℝ)*C*‖direction‖) := by
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  let ey := EuclideanSpace.equiv (Fin N) ℝ
  have hdir : (∑ a : Fin p, direction a • Pi.single a (1 : ℝ)) = direction := by
    ext a
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  apply iSup_le
  intro i
  let O := ex '' (A.chart i).target
  let S := ex '' ((A.chart i) '' A.support i)
  let R := fun a x => ey (fderiv ℝ
    (fun v => F v ((A.chart i).symm (ex.symm x))) u (Pi.single a 1))
  have hO : IsOpen O := ex.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨A.chart i y,(A.chart i).map_source (hA.support_subset i hy),rfl⟩
  have hR (a : Fin p) : ContDiffOn ℝ ∞ (R a) O := by
    apply ey.contDiff.comp_contDiffOn
    apply (atlas_actual_parameter_response_contDiffOn A hA i hU F hF u (Pi.single a 1) hu).comp
      ex.symm.contDiff.contDiffOn
    rintro _ ⟨x,hx,rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  have hlocal (a : Fin p) : paperCoordinateCj j (R a) O S ≤ ENNReal.ofReal C := by
    exact (le_iSup (fun k => paperCoordinateCj j
      (fun x => ey (fderiv ℝ (fun v => F v ((A.chart k).symm (ex.symm x))) u (Pi.single a 1)))
      (ex '' (A.chart k).target) (ex '' ((A.chart k) '' A.support k))) i).trans (hcolumns a)
  have hsum := paperCoordinateCj_sum_le j hO hSO (Finset.univ : Finset (Fin p))
    (fun a x => direction a • R a x)
    (fun a _ => (contDiffOn_const (c := direction a)).smul (hR a))
    (fun a => |direction a| * C) (fun a _ => mul_nonneg (abs_nonneg _) hC)
    (fun a _ => paperCoordinateCj_smul_le j hO hSO (R a) (hR a) (direction a) hC (hlocal a))
  have heq : (fun x => ∑ a : Fin p, direction a • R a x) =
      (fun x => ey (fderiv ℝ (fun v => F v ((A.chart i).symm (ex.symm x))) u direction)) := by
    funext x
    calc
      _ = ey (fderiv ℝ (fun v => F v ((A.chart i).symm (ex.symm x))) u
          (∑ a : Fin p, direction a • Pi.single a 1)) := by
        simp only [map_sum,map_smul,R]
      _ = _ := by rw [hdir]
  rw [heq] at hsum
  apply hsum.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    ∑ a : Fin p, |direction a| * C ≤ ∑ _a : Fin p, ‖direction‖*C := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm direction a) hC
    _ = (p : ℝ)*C*‖direction‖ := by simp; ring

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModel_parameter_direction_of_columns
