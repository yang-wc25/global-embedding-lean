import NormalPolar.ActualProbeInitialSupplyPrimaryOriginal
import NormalPolar.ActualProbeInitialSupplyCarrierNativeRemainder
import NormalPolar.ActualProbeInitialSupplyCarrierNativeMap

/-!
# Independent primitive domains and amplitude carriers in one raw atlas for the actual primary and secondary first increment

Every native family is the canonical pullback of the same original parameter
family. The record contains only the actual primitive geometry, original
profiles and support observations. Both the map and metric estimates use the
same geometry, host, cutoff and signed source at native order j+2. There is no
computed map norm, computed error bound or repair-state field.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M P Tr Λ Β Sub : Type*} {m d N p r count : ℕ}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)

structure ActualProbeInitialCarrierPrimaryRawAtlas
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (c : (l : Fin r) → Pieces l → P → D → M) (chi : (l : Fin r) → Pieces l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (W : Set (P × M)) (primaryDomain : Λ → Set (P × M))
    (K : (Λ ⊕ Fin r) → Set (P × M))
    (pieceK : (l : Fin r) → Pieces l → Set (P × M))
    (n backgroundLength j Rbackground L Rprobe : ℕ)
    (reserve Bnd Mg Bchi Bnu Ku Mphase tau ell Delta : ℝ)
    (Tbackground Tprobe : ℕ → ℝ) where
  domain : Fin A.count × Fin count → Set X
  target : ∀ i z, z ∈ domain i → z.2 ∈ (A.chart i.1).target
  background : ∀ i : Fin A.count × Fin count,
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n backgroundLength (j+1) Rbackground L
      reserve Bnd Mg Tbackground
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (primaryDomain l))
      (A.chart i.1) (domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      tau ell Delta
  prescribed : ∀ i : Fin A.count × Fin count,
    JointGroupedPrescribedObservationProfiles
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (fun l s t => c l s ((B i.2).symm t))
      (fun l s z => chi l s ((B i.2).symm z.1,z.2))
      (fun l s t => nu l s ((B i.2).symm t))
      (fun l s => round3ParameterChartPullback (B i.2) (a l s))
      (round3ParameterNativeDomain (B i.2) W)
      (fun l s => round3ParameterNativeDomain (B i.2) (pieceK l s))
      n (j+2) ell Mg Bchi Bnu (fun z : X => (z.1,(A.chart i.1).symm z.2))
      (domain i) ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i) Tprobe
      (fun l z => phase l ((B i.2).symm z.1,z.2)) Mphase
  parameter_smooth : ∀ i,
    ContDiffOn ℝ ∞ (fun z : X => u ((B i.2).symm z.1)) (domain i)
  parameter_jets : ∀ i k, k ≤ j+2 →
    ∀ z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i,
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => u ((B i.2).symm y.1)) z‖ ≤ Ku
  piece_overlap : ∀ i l z, z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i →
    (Finset.univ.filter (fun s => (z.1,(A.chart i.1).symm z.2) ∈
      round3ParameterNativeDomain (B i.2) (pieceK l s))).card ≤ Rprobe
  overlap : ∀ i z, z ∈ (parameterTensorModelEquiv (m+1) d) ⁻¹' S i →
    (Finset.univ.filter (fun l => (z.1,(A.chart i.1).symm z.2) ∈
      round3ParameterNativeDomain (B i.2) (K l))).card ≤ L


structure ActualProbeInitialCarrierRawAtlas
    (A : BufferedAtlas M D) (B : Fin count → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin count → Set (Fin (m+1+d) → ℝ))
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (c : (l : Fin r) → Pieces l → P → D → M) (chi : (l : Fin r) → Pieces l → P × D → ℝ)
    (nu : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input inputbar : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ) (W : Set (P × M)) (primaryDomain : Λ → Set (P × M))
    (K : (Λ ⊕ Fin r) → Set (P × M))
    (pieceK : (l : Fin r) → Pieces l → Set (P × M))
    (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
    (nInput nSolve q probeLength j Rbackground L Rprobe Rsecondary : ℕ)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta : ℝ)
    (Tbackground Tprobe Tinv Tobs : ℕ → ℝ) where
  primary : ActualProbeInitialCarrierPrimaryRawAtlas (Tr := Tr) A B S F hF g c chi nu phase a
    input inputbar u W primaryDomain K pieceK nInput (q+2) j Rbackground L Rprobe
    reserve Bnd Mg Bchi Bnu Ku Mphase tau ell Delta Tbackground Tprobe
  profiles : ∀ i : Fin A.count × Fin count,
    JointGroupedSecondaryCarrierProfiles (Sub := Sub) (Tr := Tr)
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun l s t => c l s ((B i.2).symm t))
      (fun l s z => chi l s ((B i.2).symm z.1,z.2))
      (fun l s t => nu l s ((B i.2).symm t))
      (fun l s => round3ParameterChartPullback (B i.2) (a l s))
      (fun l z => phase l ((B i.2).symm z.1,z.2))
      (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
      (fun t => u ((B i.2).symm t))
      (round3ParameterNativeDomain (B i.2) W)
      (fun l => round3ParameterNativeDomain (B i.2) (primaryDomain l))
      (fun l => round3ParameterNativeDomain (B i.2) (K l))
      (fun l s => round3ParameterNativeDomain (B i.2) (pieceK l s))
      nInput nSolve q probeLength (j+2) Rbackground L
      reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta Tbackground Tprobe Tinv
  choice_eq : ∀ i rec b,
    ({host := (profiles i).host rec b,chart := ((profiles i).geometry rec b).chart,
      c := ((profiles i).geometry rec b).c,cutoff := (profiles i).cutoff rec b} :
      Round3ParameterSecondaryChoice Ep M m) = (choice rec b).pullback (B i.2)
  observer : ∀ i : Fin A.count × Fin count,
    JointMixedNativeObserverGeometry
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      nSolve (j+1) ell Mg (round3ParameterNativeDomain (B i.2) W)
      (profiles i).geometry (A.chart i.1) (primary.domain i)
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)
      (fun l => round3ParameterNativeDomain (B i.2) (K l)) L Rsecondary Tobs
  background_geometry : ∀ i : Fin A.count × Fin count,
    ActualOriginalPrimaryPhysicalGeometry
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
  prescribed_geometry : ∀ (i : Fin A.count × Fin count) l s,
    ActualPrescribedPhysicalGeometry
      (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (fun t => c l s ((B i.2).symm t)) (fun t => nu l s ((B i.2).symm t))
      (round3ParameterChartPullback (B i.2) (a l s))
      (fun z => phase l ((B i.2).symm z.1,z.2))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ActualProbeInitialCarrierRawAtlas
