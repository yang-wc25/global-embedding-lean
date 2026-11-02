import Probes.ActualOriginalIncrementRawNorms
import Probes.ActualRepairWeightedRecurrence

/-! The SAME actual displacement supplies the base-two norm needed by the
full repair pair recurrence. The additional observed order is supplied by
the actual smoother gain; no new target entrance norm is imposed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold IsManifold
open scoped ContDiff Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N pcount : ℕ} {M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ
 theorem actual_original_increment_raw_base_two_norm_uniform
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hSolve : (j+1)+2+(q+2) ≤ nSolve) (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hc : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs TP : ℕ → ℝ)
    (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k) (hTobs : ∀ k, 0 ≤ Tobs k) (hTP : ∀ k, 0 ≤ TP k) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
      (A : BufferedAtlas M D) (B : Fin pcount → OpenPartialHomeomorph Ep Ep)
      (_hA : IsSmoothBufferedAtlas A) (_hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
      (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
      (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
      (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
      (S : Fin A.count × Fin pcount → Set (Fin (m+1+d) → ℝ))
      (_hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
      (ell delta tau Delta : ℝ) (_htau : 0 < tau) (_htaul : tau ≤ ell) (_hell1 : ell ≤ 1)
      (_hdelta : 0 ≤ delta) (_hdeltatau : delta ≤ tau)
      (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
      (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar nInput nSolve (j+1) q Rsub Lprimary
        reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice)
      (Omega : Fin A.count × Fin pcount → Set X)
      (_obs : ∀ i : Fin A.count × Fin pcount, ActualOriginalSecondaryObservationData raw Tobs Rsecondary
        (A.chart i.1) (Omega i)
        (parameterRound2_meanParameterMap (m := m) (B i.2) '' ((parameterTensorModelEquiv (m+1) d) ⁻¹' S i)))
      (_hParam : ∀ i : Fin A.count × Fin pcount, ∀ z : X,
        parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k → k ≤ j+2 →
        ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m := m) (B i.2)) z‖ ≤ TP k),
    let U := actualOriginalIncrementMap F hF g input (q+2) tau delta choice
    let coordinates := incrementsOriginalMapCoordinates A B U
    (∀ i, ∃ G : Set (Fin (m+1+d) → ℝ), IsOpen G ∧ S i ⊆ G ∧
      G ⊆ incrementsOriginalDifferentiation A B i ∧ ContDiffOn ℝ ∞ (coordinates i) G) ∧
    paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S ≠ ⊤ ∧
      (paperAtlasWeighted 2 j tau coordinates (incrementsOriginalDifferentiation A B) S).toReal ≤ CR*delta/tau := by
  obtain ⟨C0,hC0,hraw⟩ := actual_original_increment_raw_paper_norms_uniform
    (m := m) (d := d) (N := N) (pcount := pcount) (M := M) (Tr := Tr)
    (Label := Label) (SubPrimary := SubPrimary) (SubSecondary := SubSecondary)
    nInput nSolve (j+1) q Rsub Lprimary Rsecondary hq hSolve hInput
    reserve Bnd Mg Kcut hc hBnd hMg hKcut T Tinv Tobs TP hT hTinv hTobs hTP
  refine ⟨(j+1)*C0,mul_nonneg (by positivity) hC0,?_⟩
  intro A B hA hB F hF g input inputbar W primary S hSO ell delta tau Delta htau htaul hell1
    hdelta hdeltatau choice raw Omega obs hParam U coordinates
  have h := hraw A B hA hB F hF g input inputbar W primary S hSO ell delta tau Delta htau htaul hell1
    hdelta hdeltatau choice raw Omega obs (fun i z hz k hk hkj => hParam i z hz k hk (by omega))
  have hshift := actual_paper_weighted_base_shift 2 j htau coordinates
    (incrementsOriginalDifferentiation A B) S (by simpa only [Nat.add_assoc] using h.2.1.1)
  refine ⟨h.1,hshift.1,hshift.2.trans ?_⟩
  calc
    _ ≤ (j+1)*(C0*delta*tau)/tau^2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [Nat.add_assoc] using h.2.1.2) (by positivity)) (sq_nonneg _)
    _ = _ := by field_simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_original_increment_raw_base_two_norm_uniform
