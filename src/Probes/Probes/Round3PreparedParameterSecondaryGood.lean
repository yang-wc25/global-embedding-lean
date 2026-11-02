import Probes.Round3PreparedParameterSecondaryC2
import Probes.Round3PreparedHostGood

/-! The actual perturbed transverse reserve on a fixed signed carrier gives
the ORIGINAL physical signed covector, for an arbitrary parameter manifold.
There is no new-map phase-legality premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

 def round3PreparedPhysicalSignedPhase
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (z : P × M) : ℝ :=
    ![Ref.phase r.val.1.1 z+Ref.phase r.val.1.2 z,
      Ref.phase r.val.1.1 z-Ref.phase r.val.1.2 z,
      -Ref.phase r.val.1.1 z+Ref.phase r.val.1.2 z,
      -Ref.phase r.val.1.1 z-Ref.phase r.val.1.2 z] r.val.2

 theorem round3_prepared_physical_signed_differentiable
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (z : P × M)
    (hnu : z ∈ Ref.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Ref)
    (hmu : z ∈ Ref.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Ref) :
    MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2 := by
  rcases r with ⟨⟨⟨nu,mu⟩,q⟩,hr⟩
  have hn := actual_original_phase_mdifferentiableAt Ref hd hs nu z.1 z.2 hnu
  have hm := actual_original_phase_mdifferentiableAt Ref hd hs mu z.1 z.2 hmu
  have hplus : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (fun x => Ref.phase nu (z.1,x)+Ref.phase mu (z.1,x)) z.2 := by exact hn.add hm
  have hminus : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (fun x => Ref.phase nu (z.1,x)-Ref.phase mu (z.1,x)) z.2 := by exact hn.sub hm
  have hreverse : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (fun x => -Ref.phase nu (z.1,x)+Ref.phase mu (z.1,x)) z.2 := by exact hn.neg.add hm
  have hneg : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (fun x => -Ref.phase nu (z.1,x)-Ref.phase mu (z.1,x)) z.2 := by exact hn.neg.sub hm
  fin_cases q
  · simpa [round3PreparedPhysicalSignedPhase] using hplus
  · simpa [round3PreparedPhysicalSignedPhase] using hminus
  · simpa [round3PreparedPhysicalSignedPhase] using hreverse
  · simpa [round3PreparedPhysicalSignedPhase] using hneg

 theorem round3_prepared_parameter_secondary_good_on_carrier
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (i : Fin Ref.atlas.count × Fin Ref.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Ref hd hs i r W)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (y : Ep × M) (hy : y ∈ piece.carrier)
    (cT : ℝ) (hcT : 0 < cT)
    (hFrame : let z := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native y
      ∀ v : Tdata, cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (F ((Ref.parameterChart i.2).symm z.1)) (hF ((Ref.parameterChart i.2).symm z.1))
        (piece.slices z.1).symm z.2 v‖^2) :
    let p := (Ref.parameterChart i.2).symm y.1
    GoodCovector (F p) (hF p) y.2
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r (p,y.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (p,x)) y.2)) := by
  intro p
  let a := actualHostAdaptedChart (Ref.atlas.chart i.1) piece.native
  let z := a y
  have hys := piece.carrier_source hy
  have hz : z ∈ piece.native.target := by rw [← piece.data.1]; exact a.map_source hys
  rcases piece.data with ⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩
  have hzp : z.1 = y.1 := (hforw y hys).1
  have hpx : (piece.slices z.1).symm z.2 = y.2 := by
    have hh := a.left_inv hys
    rw [hpair z hz] at hh
    exact congrArg Prod.snd hh
  have hactive := piece.active y hys
  have hdiff := round3_prepared_physical_signed_differentiable Ref hd hs r (p,y.2) hactive.1 hactive.2
  have hpsi : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ)
      (fun x => actualOriginalParameterSignedPhase Ref i r.val (z.1,x)) ((piece.slices z.1).symm z.2) := by
    rw [hpx]
    simpa only [actualOriginalParameterSignedPhase,round3PreparedPhysicalSignedPhase,hzp,p] using hdiff
  have hx : z.2 ∈ (piece.slices z.1).target := by rw [het]; exact hz
  have hAdapt : ∀ x ∈ (piece.slices z.1).target,
      actualOriginalParameterSignedPhase Ref i r.val (z.1,(piece.slices z.1).symm x) = x 0 := by
    intro x hx
    exact hphase (z.1,x) (by rw [het] at hx; exact hx)
  have hGood := round3_prepared_good_of_transverse_reserve
    (F ((Ref.parameterChart i.2).symm z.1)) (hF ((Ref.parameterChart i.2).symm z.1))
    (fun x => actualOriginalParameterSignedPhase Ref i r.val (z.1,x))
    (piece.slices z.1) (he z.1) (piece.slices z.1).target (piece.slices z.1).open_target
    subset_rfl z.2 hx hpsi hAdapt cT hcT hFrame
  rw [hpx] at hGood
  dsimp only [actualOriginalParameterSignedPhase] at hGood
  rw [hzp] at hGood
  exact hGood

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_good_on_carrier
