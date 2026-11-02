import Smoothing.Round3OuterStablePrimaryReserves
import Smoothing.Round3OuterParameterCrossReserves

/-! The actual global stable primary family produces every observer's
native slices and all three quantitative reserves. Every observer is a
canonical pullback of the SAME family; no native data or reserve supplier
is an input to this theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
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
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem round3_stable_primary_all_observer_data
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hn : IncrementsOriginalFreeNormalConditions Ref hd hs)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :
    let A := Round3ParameterWholePrimaryIndex Ref theta packet
    let ps := round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable
    let piece := round3ParameterWholePrimaryPiece Ref hd theta ps
    let g := round3ParameterWholePrimaryFamily Ref hd hs hn theta ps
    let host := fun nu (_ : Fin Ref.parameterCount) (a : A) => (piece nu a).host
    let b := fun nu ip (a : A) => round3ParameterCrossNativeChart
      (Ref.parameterChart a.1.2) (Ref.parameterChart ip) (piece nu a).native
    ∃ e : Fin Ref.primaryCount → Fin Ref.parameterCount → A → Ep → OpenPartialHomeomorph M D,
    (∀ nu ip a, ActualOriginalHostSliceData (Ref.atlas.chart (host nu ip a)) (b nu ip a)
      (fun w : Ep × M => Ref.phase nu ((Ref.parameterChart ip).symm w.1,w.2)) (e nu ip a)) ∧
    (∀ nu ip a, (b nu ip a).source ⊆ actualOriginalNativeOpen Ref (host nu ip a,ip)) ∧
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a)).source →
      ((Ref.parameterChart ip).symm w.1,w.2) ∈ Ref.primaryDomain nu ∩ incrementsOriginalParameterRegion Ref) ∧
    (∀ nu ip a w, w ∈ (actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a)).source →
      w.2 ∈ Ref.atlas.inner (host nu ip a)) ∧
    (∀ nu ip a, actualHostAdaptedChart (Ref.atlas.chart (host nu ip a)) (b nu ip a) =
      (round3ParameterNativePrimary (fun p x => Ref.F (p,x)) g (Ref.parameterChart ip)).chart nu a) ∧
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ v : D,
      (profiles.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart ip).symm z.1) ∘ (e nu ip a z.1).symm) z.2 v‖^2) ∧
    (∀ nu ip a z, z ∈ (b nu ip a).target → ∀ v : Tdata,
      (profiles.cT/16)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (F ((Ref.parameterChart ip).symm z.1)) (hF ((Ref.parameterChart ip).symm z.1)) (e nu ip a z.1).symm z.2 v‖^2) ∧
    (∀ nu ip a z, z ∈ (b nu ip a).target → (1/4 : ℝ) ≤
      ‖actualOriginalFreeNormalFieldRaw (fun p x => F ((Ref.parameterChart ip).symm p) x)
        (fun p => hF ((Ref.parameterChart ip).symm p)) (e nu ip a)
        (fun z : X => Ref.freeNormal nu ((Ref.parameterChart ip).symm z.1,(e nu ip a z.1).symm z.2)) z‖) ∧
    (∀ nu ip a p x, (e nu ip a p).symm x = g.inverse nu a ((Ref.parameterChart ip).symm p) x) := by
  intro A ps piece g host b
  have hRes := round3_stable_primary_sigma_reserves Ref hd hs theta packet profiles F hF stable
  have hEach (nu : Fin Ref.primaryCount) (ip : Fin Ref.parameterCount) (a : A) :=
    round3_parameter_actual_cross_reserves Ref hd a.1.2 ip nu _ (piece nu a) F hF
      (profiles.cF/16) (profiles.cT/16) (1/4)
      (hRes.1 nu a) (hRes.2.1 nu a) (hRes.2.2.1 nu a) (hRes.2.2.2 nu a)
  choose e hData hNative hActive hInner hFirst hFrame hNormal hSlices using hEach
  refine ⟨e,hData,hNative,hActive,hInner,?_,hFirst,hFrame,hNormal,?_⟩
  · intro nu ip a
    exact round3Parameter_cross_host_conjugation (Ref.parameterChart a.1.2)
      (Ref.parameterChart ip) (Ref.atlas.chart (piece nu a).host) (piece nu a).native
      (round3Parameter_primary_native_preserves_phase Ref hd a.1.2 nu _ (piece nu a)).1
  · intro nu ip a p x
    exact hSlices nu ip a p x

#print axioms round3_stable_primary_all_observer_data
end GlobalEmbedding.Continuation
