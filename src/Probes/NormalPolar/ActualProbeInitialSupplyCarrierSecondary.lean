import NormalPolar.ActualProbeInitialSupplySecondaryObserver
import NormalPolar.JointSecondaryCarrierFamily

/-! A vanishing parameter-response modulus for the actual grouped carrier
source. The complete joint forcing is formed first. Its physical finite
pieces and observer are manufactured from the raw fields, then the original
affine parameter coordinates are inserted. No completed response is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {M Ep Tr Λ Β Sub U E : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)
private local instance : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

theorem actualProbeInitialSupply_carrier_secondary_responses_uniform
    (nInput nSolve q probeLength j length Rbackground L Rsecondary : ℕ)
    (hq : 1 ≤ q) (hj : 2 ≤ j) (hbudget : j+2+length ≤ nSolve)
    (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput)
    (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tinv Tobs : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (coordinate : (U × E) ≃L[ℝ] X) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ t, 0 ≤ GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus C t) ∧
      Filter.Tendsto (GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus C) (𝓝[>] 0) (𝓝 0) ∧
    ∀ (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Pieces l → Ep → D → M)
      (chi : (l : Fin r) → Pieces l → X → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
      (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X)
      (phase : Fin r → Ep × M → ℝ)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (u : Ep → Fin p → ℝ) (t Delta : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
      (W : Set (Ep × M)) (hW : IsOpen W) (primaryDomain : Λ → Set (Ep × M))
      (K : (Λ ⊕ Fin r) → Set (Ep × M))
      (pieceK : (l : Fin r) → Pieces l → Set (Ep × M))
      (profiles : JointGroupedSecondaryCarrierProfiles (Sub := Sub) (Tr := Tr) F hF g c chi nu a phase
        input inputbar u W primaryDomain K pieceK nInput nSolve q probeLength (j+1) Rbackground L
        reserve Bnd Mg Kcut Bchi Bnu Ku Mphase (t^((6:ℝ)/5)) (t^((11:ℝ)/10))
        (t^(10:ℕ)) Delta Tbackground Tprobe Tinv)
      (e : OpenPartialHomeomorph M D) (OmegaOld S : Set X)
      (observer : JointMixedNativeObserverGeometry F hF nSolve j (t^((11:ℝ)/10)) Mg W
        profiles.geometry e OmegaOld S K L Rsecondary Tobs)
      (Omega : Set X) (hO : IsOpen Omega) (hSO : S ⊆ Omega)
      (hTarget : ∀ z ∈ Omega, z.2 ∈ e.target)
      (hWmap : MapsTo (fun z : X => (z.1,e.symm z.2)) Omega W) (center : X),
    let tau := t^((6:ℝ)/5)
    let ell := t^((11:ℝ)/10)
    let delta := t^(10:ℕ)
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u false
    let Q := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u true
    let source := fun rec s => jointSecondarySourceOfRawGeometry F hF nSolve (j+1) ell Mg W
      (profiles.geometry rec s) (profiles.host rec s) (profiles.cutoff rec s) phases R Q tau rec.val
    let phi := fun z : U × E => center+coordinate z
    let wave := fun z : U × E => actualParameterSecondarySourceSum F hF source tau length
      ((phi z).1,e.symm (phi z).2)
    ContDiffOn ℝ ∞ wave (phi ⁻¹' Omega) ∧
    ∀ z, phi z ∈ S → ∀ direction : U,
      ‖fderiv ℝ (fun v => wave (v,z.2)) z.1 direction‖ ≤
        t^((56:ℝ)/5)*GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fun x => wave (v,x)) z.2) z.1 direction‖ ≤
        t^(10:ℕ)*GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus C t*‖direction‖ ∧
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (fun x => wave (v,x))) z.2) z.1 direction‖ ≤
        t^((44:ℝ)/5)*GlobalEmbedding.NormalPolar.actualProbeSecondaryModulus C t*‖direction‖ := by
  obtain ⟨CH,hCH,hfamily⟩ := jointCarrier_mixed_family_from_raw_uniform
    (M := M) (Ep := Ep) (Tr := Tr) (m := m) (N := N) (p := p)
    (Λ := Λ) (Β := Β) (Pieces := Pieces) (Sub := Sub)
    nInput nSolve q probeLength Rbackground L hq hbackgroundOrder hprobeOrder
    reserve Bnd Mg Kcut Bchi Bnu Ku Mphase hreserve hBnd hMg hKcut hBchi hBnu hKu hMphase
    weight Tbackground Tprobe Tinv hTbackground hTprobe hTinv
  let Tnew := fun k => linearModelFactor coordinate k*Tobs k
  have hTnew k : 0 ≤ Tnew k := mul_nonneg (linearModelFactor_nonneg coordinate k) (hTobs k)
  have hscaled := actual_secondary_native_paper_responses_uniform
    (m := m) (N := N) (n := nSolve) (j := j+1) (Ep := Ep) (M := M)
    (Label := Λ ⊕ Fin r) (Sub := Sub) (U := U) (E := E)
    length L Rsecondary Tnew Mg CH hTnew hMg hCH (by omega) hbudget
  refine ⟨actualConstructedSecondaryWaveBudget m N nSolve (j+1) length L Rsecondary Mg CH Tnew,
    hscaled.1,hscaled.2.1,hscaled.2.2.1,?_⟩
  intro F hF g label c chi nu a phase input inputbar u t Delta ht ht1 W hW primaryDomain K pieceK profiles
    e OmegaOld S observer Omega hO hSO hTarget hWmap center tau ell delta vf phases R Q source phi wave
  obtain ⟨data,spec⟩ := hfamily F hF g label c chi nu a phase input inputbar u tau ell delta Delta
    (pow_nonneg ht.le _) W primaryDomain K pieceK (j+1) profiles
  let native := actualProbeInitialSupply_secondary_observation F hF ell Mg CH delta W
    profiles.geometry e OmegaOld S K L Rsecondary Tobs hTobs observer data
    (fun rec s => (spec rec s).2.1) (fun rec s => (spec rec s).2.2.2.1)
    (fun rec s => (spec rec s).2.2.2.2.1) Omega hO hSO hTarget hWmap
  let obs := native.affinePullback coordinate center (Real.rpow_nonneg ht.le _)
  have he : obs.wave tau length = wave := by
    funext z
    change actualConstructedSecondarySum F hF (fun rec s => (data rec s).base) tau length
      ((phi z).1,e.symm (phi z).2) = _
    rw [jointSecondary_sum_eq_physical_source F hF nSolve (j+1) ell Mg CH delta W
      profiles.geometry profiles.host profiles.cutoff phases R Q tau data spec tau length]
  have hs := obs.wave_smooth tau length hW
  rw [he] at hs
  refine ⟨hs,?_⟩
  intro z hz direction
  have hb := hscaled.2.2.2 F hF t ht ht1 W hW data obs rfl rfl rfl z hz direction
  rw [he] at hb
  exact hb

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_carrier_secondary_responses_uniform
