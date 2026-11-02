import Smoothing.ParameterRound2MeanRawGermReserveSupply

/-! Original reserve supplies yield the exact pair records consumed by the
full-background native response theorem. Input representatives, original
observer sample images, scale, derivative order and all primitive constants
are kept literally; no raw-output estimate is manufactured. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
variable {m d N count : ℕ} {M P Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep×D
local notation "IM" => 𝓘(ℝ,D)

theorem globalWave_background_raw_pairs_of_reserve
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep×M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace atlas param S W))
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=IM) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (primary : Λ → Set (Ep×M)) (ell : ℝ)
    (hraw : ParameterRound2MeanRawGermReserveSupply (Tr:=Tr) atlas param S W p H rho q
      Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (epsilon : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (j : ℕ) (R : ℝ) (hDinput : 0 ≤ Dinput j)
    (Su : Set P) (u : P) (hu : u ∈ Su)
    (Germ : P → parameterRound2_originalTensorGermSpace atlas param S W)
    (input : P → (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (hvalue : ∀ v ∈ Su, (Germ v).val = input v)
    (hreserve : ∀ v ∈ Su, p 0 (Germ v-H) < rho)
    (hsize : ∀ v ∈ Su, p (j+(q+4)) (Germ v) ≤ R)
    (K : ℝ)
    (hpair : ∀ v ∈ Su, p (j+(q+4)) (Germ v-Germ u) ≤ K*(‖v‖+‖u‖)*‖v-u‖)
    (idx : Fin atlas.count × Fin count) :
    let Samples := parameterRound2_meanParameterMap (m:=m) (param idx.2) ''
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' S idx)
    ∀ v ∈ Su, ∃ (G : Set (Ep×M)) (hG : IsOpen G) (Oraw : Set X) (Delta : ℝ),
      G ⊆ W ∧ Oraw ⊆ (param idx.2).source ×ˢ (atlas.chart idx.1).target ∧
      Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr:=Tr) (j+(q+4)) (q+2) j Rsub Lprimary
        reserve (Bnd j R) (Mg j) T F hF (parameterRound2_restrictPrimaryFamily F g G hG)
        (input v) (input u) G primary (atlas.chart idx.1) Oraw Samples (epsilon*ell) ell Delta) ∧
      Delta ≤ (Dinput j*K)*(‖v‖+‖u‖)*‖v-u‖ := by
  intro Samples v hv
  obtain ⟨G,hG,hGW,_,Obs,hObs,⟨raw⟩⟩ := hraw epsilon he he1 j R
    ⟨Germ v,hreserve v hv⟩ ⟨Germ u,hreserve u hu⟩ (hsize v hv) (hsize u hu)
  refine ⟨G,hG,Obs idx,Dinput j*p (j+(q+4)) (Germ v-Germ u),hGW,hObs idx,?_,?_⟩
  · have hh := raw idx
    rw [hvalue v hv,hvalue u hu] at hh
    exact ⟨hh⟩
  · calc
      _ ≤ Dinput j*(K*(‖v‖+‖u‖)*‖v-u‖) := mul_le_mul_of_nonneg_left (hpair v hv) hDinput
      _ = _ := by ring

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_background_raw_pairs_of_reserve
