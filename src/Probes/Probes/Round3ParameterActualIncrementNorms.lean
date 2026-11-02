import Probes.Round3ParameterRawAtlasData
import Probes.Round3ParameterOriginalMapNorm
import Probes.ActualOriginalIncrementRawJetsAllIndex

/-! # Original displacement estimates for one global general-parameter U

The constants precede the physical parameter type, all parameter/source
atlases, and every primary/secondary index type.  Raw analytic profiles are
consumed in the actual original parameter charts.  The result concerns one
literal global U, with the original full total-derivative atlas norms and
unchanged sample sets.  No local output map, output budget, or output gluing
is supplied by the caller. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M Tr : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_actual_increment_original_norms_uniform
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : j+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P Label SubPrimary SubSecondary : Type*)
      [TopologicalSpace P] [Fintype Label] [DecidableEq Label]
      [Fintype SubPrimary] [Fintype SubSecondary], ∀ (c : ℕ)
      (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
      (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
      (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (P × M)) (primary : Label → Set (P × M))
      (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
      (ell delta tau Delta : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
      (hdelta : 0 ≤ delta) (hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
      (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
      (data : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
        nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
        W primary S ell delta tau Delta choice),
    let U := round3ParameterIncrementMap F hF g input (q+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 0 (j+1) tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta*tau) ∧
    (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 1 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ C*delta) := by
  obtain ⟨K,hK,hraw⟩ := actual_original_increment_raw_jets_uniform_all_index
    (m := m) (N := N) («Ep» := Ep) (M := M) (Tr := Tr)
    nInput nSolve j q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv Tobs hT hTinv hTobs
  refine ⟨round3ParameterMapNormCost m d N j K,round3ParameterMapNormCost_nonneg m d N j K hK,?_⟩
  intro P Label SubPrimary SubSecondary _ _ _ _ _ c A B F hF g hg input inputbar W primary S
    ell delta tau Delta htau htaul hell1 hdelta hdeltatau choice hc data U coordinates
  let O := data.observationDomain
  let S0 := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹' S i
  let U0 := fun (i : Fin A.count × Fin c) (z : X) =>
    actualOriginalIncrementMap (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
      (round3ParameterNativePrimary F g (B i.2))
      (fun t => input ((B i.2).symm t)) (q+2) tau delta
      (round3ParameterNativeChoices choice (B i.2)) (z.1,(A.chart i.1).symm z.2)
  have hh (i : Fin A.count × Fin c) := hraw Label SubPrimary SubSecondary
    (fun t => F ((B i.2).symm t)) (fun t => hF ((B i.2).symm t))
    (round3ParameterNativePrimary F g (B i.2))
    (fun t => input ((B i.2).symm t)) (fun t => inputbar ((B i.2).symm t))
    (round3ParameterNativeDomain (B i.2) W) (fun ν => round3ParameterNativeDomain (B i.2) (primary ν))
    ell delta tau Delta hdelta hdeltatau (round3ParameterNativeChoices choice (B i.2)) (data.raw i.2)
    (A.chart i.1) (O i) (S0 i) (data.observation i)
  have hO (i) : IsOpen (O i) := (data.observation i).profiles.hO
  have hSO (i) : S0 i ⊆ O i := (data.observation i).profiles.hSO
  have hOsub (i) : O i ⊆ (B i.2).target ×ˢ (A.chart i.1).target := by
    intro z hz
    exact ⟨((data.observation i).profiles.hmapWO hz).1,(data.observation i).target z hz⟩
  have heq (i) : EqOn (round3ParameterObservedMap A B U i) (U0 i) (O i) := by
    intro z hz
    exact (round3Parameter_native_increment_eq F hF g (B i.2) hg input (q+2) tau delta choice hc
      z.1 (hOsub i hz).1 ((A.chart i.1).symm z.2)).symm
  have hsm (i) : ContDiffOn ℝ ∞ (round3ParameterObservedMap A B U i) (O i) :=
    (hh i).1.congr (heq i)
  have hj : ∀ i, ∀ k ≤ j+1, ∀ z : X, parameterTensorModelEquiv (m+1) d z ∈ S i →
      tau^k*‖iteratedFDeriv ℝ k (round3ParameterObservedMap A B U i) z‖ ≤ K*delta*tau := by
    intro i k hk z hz
    rw [(((heq i).eventuallyEq_of_mem ((hO i).mem_nhds (hSO i hz))).iteratedFDeriv ℝ k).eq_of_nhds]
    exact (hh i).2 k hk z hz
  exact round3Parameter_original_map_norms_from_native A B S O hO hOsub hSO U j tau delta K
    htau (htaul.trans hell1) hdelta hK hsm hj

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_increment_original_norms_uniform
