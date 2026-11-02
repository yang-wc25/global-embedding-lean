import Probes.Round3PreparedTransverseGood
import Probes.ActualOriginalHostRefinement

/-! Actual positive transverse reserve on an adapted host chart gives the
original Good differential at every physical source point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ}
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance hostGoodFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] Ey) := inferInstance
private local instance hostGoodFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] Ey) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round3_prepared_host_good_at_native
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b psi e)
    (F : Ep → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : ∀ z ∈ b.target, ∀ v : Tdata,
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2)
    (z : X) (hz : z ∈ b.target)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) ((e z.1).symm z.2)) :
    GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi (z.1,(e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (z.1,x)) ((e z.1).symm z.2))) := by
  rcases hdata with ⟨hat,ha,hai,hforward,he,hes,het,hef,hei,hpair,hadapt,hback,hforw,hbj,hfj⟩
  have hx : z.2 ∈ (e z.1).target := by rw [het]; exact hz
  have hAdapt : ∀ x ∈ (e z.1).target, psi (z.1,(e z.1).symm x) = x 0 := by
    intro x hx
    exact hadapt (z.1,x) (by rw [het] at hx; exact hx)
  exact round3_prepared_good_of_transverse_reserve (F z.1) (hF z.1)
    (fun x => psi (z.1,x)) (e z.1) (he z.1) (e z.1).target (e z.1).open_target
    (Subset.rfl) z.2 hx hpsi hAdapt cT hcT (hFrame z hz)

theorem round3_prepared_host_good_of_reserve
    (c : OpenPartialHomeomorph M D) (b : OpenPartialHomeomorph X X)
    (psi : Ep × M → ℝ) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData c b psi e)
    (F : Ep → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : ∀ z ∈ b.target, ∀ v : Tdata,
      cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2)
    (y : Ep × M) (hy : y ∈ (actualHostAdaptedChart c b).source)
    (hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) y.2) :
    GoodCovector (F y.1) (hF y.1) y.2
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi y)).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) y.2)) := by
  have hSource := hdata.2.2.2.2.2.1 y.1
  have hys : y.2 ∈ (e y.1).source := by rw [hSource]; exact hy
  have hTarget := hdata.2.2.2.2.2.2.1 y.1
  have hz : (y.1,e y.1 y.2) ∈ b.target := by
    have hh := (e y.1).map_source hys
    rwa [hTarget] at hh
  have hleft : (e y.1).symm (e y.1 y.2) = y.2 := (e y.1).left_inv hys
  have hp : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun x => psi (y.1,x)) ((e y.1).symm (e y.1 y.2)) := by
    rwa [hleft]
  have hGood := round3_prepared_host_good_at_native c b psi e hdata F hF cT hcT hFrame
    (y.1,e y.1 y.2) hz hp
  dsimp only at hGood
  rw [hleft] at hGood
  exact hGood


end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_host_good_of_reserve
