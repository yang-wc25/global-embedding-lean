import Probes.ActualIncrementJointNormalizedMean
import Probes.ActualIncrementJointNormalizedSource

/-! Primitive-data producer for the SAME actual normalized mean. The sources,
finite-polynomial reconstruction, leading coefficients and complete mean are
computed by the original definitions. No source, correction, error or mean
profile is assumed. All jets include nonzero-dimensional parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

theorem actual_joint_primitive_normalized_mean_bounds_uniform
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] {J : Type*} [Fintype J]
    (j p : ℕ) (v : J → D) (i i' : J) (c Bnd : ℝ) (Bsub : ℕ)
    (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Type*} [Fintype A] (_hCard : Fintype.card A ≤ Bsub)
        (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b)) (chart : Ep → D → M),
      ∀ (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
        (L : X → T →L[ℝ] ℝ) (input inputbar : X → T)
        (cutoff phi : X → ℝ)
        (normal : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
        (cs : A → X → ℝ)
        (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
        (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
        (_hPhi : ContDiffOn ℝ ∞ phi O)
        (_hNormal : ContDiffOn ℝ ∞ (fun z : X => (normal z.1 z.2 : V)) O)
        (_hcs : ∀ a, ContDiffOn ℝ ∞ (cs a) O)
        (_hBrow : ContDiffOn ℝ ∞ (fun z : X => fun a : Fin (m+1) =>
          (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 a : V)) O)
        (_hA : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1) z.2) O)
        (_hB : ContDiffOn ℝ ∞ (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1) z.2) O)
        (_hG : ContDiffOn ℝ ∞ (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ chart z.1) z.2)) O)
        (_hJ : ContDiffOn ℝ ∞ (fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
          (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)) O)
        (_hT0 : ContDiffOn ℝ ∞ (fun z : X => incrementsModeTransverseValue (F z.1) (chart z.1) z.2) O)
        (ell tau Delta : ℝ) (_hell : 0 < ell) (_hell1 : ell ≤ 1)
        (_htau : 0 < tau) (_htauell : tau ≤ ell) (_hDelta : 0 ≤ Delta)
        (_hReserve : ∀ x ∈ S, c ≤ L x (input x) ∧ c ≤ L x (inputbar x))
        (_hLb : ∀ i ≤ j + p + 2, ∀ x ∈ S, ell ^ i * ‖iteratedFDeriv ℝ i L x‖ ≤ Bnd)
        (_hInputb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i input x‖ ≤ Bnd)
        (_hInputbarb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i inputbar x‖ ≤ Bnd)
        (_hCutb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i cutoff x‖ ≤ Bnd)
        (_hNormalb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => (normal z.1 z.2 : V)) x‖ ≤ Bnd)
        (_hcsb : ∀ a, ∀ i ≤ j+p+2, ∀ x ∈ S,
          ell^i * ‖iteratedFDeriv ℝ i (cs a) x‖ ≤ Bnd)
        (_hBrowb : ∀ i ≤ j+p+2, ∀ x ∈ S, ell^i * ‖iteratedFDeriv ℝ i
          (fun z : X => fun a : Fin (m+1) =>
            (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 a : V)) x‖ ≤ Bnd)
        (_hInputd : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ input y - inputbar y) x‖ ≤ Delta)
        (_hAb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hBb : ∀ i ≤ j + p + 2, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hGb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun z : X => freeGramRightInverse (fderiv ℝ (F z.1 ∘ chart z.1) z.2)) x‖ ≤ Bnd)
        (_hJb : ∀ i ≤ j + 1, ∀ x ∈ S, ell ^ i *
          ‖iteratedFDeriv ℝ i (fun z : X => (normalSpace (I := I) (F z.1) (chart z.1 z.2)).subtypeL.comp
            (incrementsModeCoordinateJ (F z.1) (hF z.1) (chart z.1) z.2)) x‖ ≤ Bnd)
        (_hT0b : ∀ i ≤ j + 1, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => incrementsModeTransverseValue (F z.1) (chart z.1) z.2) x‖ ≤ Bnd)
        (_hPhib : ∀ d, ∀ i ≤ j, ∀ x ∈ S,
          ell ^ i * ‖iteratedFDeriv ℝ i (fun z : X => fderiv ℝ (fun x => phi (z.1,x)) z.2 (v d)) x‖ ≤ Bnd),
      let vf := fun (B : X → T) (a : A) (b : Ep) (x : D) =>
        cs a (b,x) • ((Real.sqrt 2*1*tau*(cutoff (b,x)*Real.sqrt (L (b,x) (B (b,x))))) • normal b x)
      let k := fun (B : X → T) (a : A) (z : X) => incrementsModeComplexInclude
        (incrementsModeSource (F z.1) (hF z.1) (chart z.1) (fun _ _ _ => 0) (vf B a z.1) z.2)
      let meanA := fun z : X => incrementsActualNormalizedMean (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => input (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => (normal z.1 x : V))
        (fun a x => k input a (z.1,x)) tau p v i i' z.2
      let meanB := fun z : X => incrementsActualNormalizedMean (F z.1) (hF z.1)
        (chart z.1) (fun x => L (z.1,x)) (fun x => inputbar (z.1,x))
        (fun x => cutoff (z.1,x)) (fun x => phi (z.1,x)) (fun x => (normal z.1 x : V))
        (fun a x => k inputbar a (z.1,x)) tau p v i i' z.2
      let positive := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
      (ContDiffOn ℝ ∞ meanA positive ∧ ContDiffOn ℝ ∞ meanB positive) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r meanA x‖ ≤ C*(tau/ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r meanB x‖ ≤ C*(tau/ell)) ∧
      (∀ r ≤ j, ∀ x ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y => meanA y-meanB y) x‖ ≤ C*(tau/ell)*Delta) ∧
      (let realA := fun y ↦ incrementsMeanRealCoordinate (meanA y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realA x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realA S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realB := fun y ↦ incrementsMeanRealCoordinate (meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realB x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realB S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell))) ∧
      (let realDiff := fun y ↦ incrementsMeanRealCoordinate (meanA y - meanB y)
       (∀ r ≤ j, BddAbove (Set.range fun x : S ↦ ‖iteratedFDeriv ℝ r realDiff x‖)) ∧
        (∑ r ∈ Finset.range (j + 1), ell ^ r * finiteCjNorm r realDiff S) ≤
          (∑ r ∈ Finset.range (j + 1), ((r + 1 : ℕ) : ℝ)) * (C * (tau / ell) * Delta)) := by
  obtain ⟨K,hK,hSource⟩ := actual_joint_normalized_source_family_profiles
    (I := I) (M := M) (Ep := Ep) (T := T) (m := m) (N := N) (j+p+2) c Bnd hc hBnd
  obtain ⟨C,hC,hMean⟩ := actual_joint_normalized_mean_bounds_uniform
    (I := I) (M := M) (Ep := Ep) j p v i i' c Bnd K Bsub hc hBnd hK
  refine ⟨C,hC,?_⟩
  intro A _ hCard F hF chart O S hO hSO L input inputbar cutoff phi normal cs
    hL hInput hInputbar hCut hPhi hNormal hcs hBrow hA hB hG hJ hT0
    ell tau Delta hell hell1 htau htauell hDelta hReserve hLb hInputb hInputbarb
    hCutb hNormalb hcsb hBrowb hInputd hAb hBb hGb hJb hT0b hPhib
    vf k meanA meanB positive
  obtain ⟨hPos,hSpos,hk,hkbar,hkb,hkbarb,hkd,hs1,hs2⟩ := hSource F hF chart normal O S hO hSO
    L input inputbar cutoff cs hL hInput hInputbar hCut hcs hNormal hBrow
    ell tau Delta hell htau hDelta hReserve hLb hInputb hInputbarb hCutb hcsb hNormalb hBrowb hInputd
  have hPosO : positive ⊆ O := fun z hz => hz.1.1
  have hres := hMean hCard F hF chart positive S hPos hSpos L input inputbar cutoff phi
    (fun z : X => (normal z.1 z.2 : V)) (hL.mono hPosO) (hInput.mono hPosO)
    (hInputbar.mono hPosO) (hCut.mono hPosO) (hPhi.mono hPosO) (hNormal.mono hPosO)
    (hA.mono hPosO) (hB.mono hPosO) (hG.mono hPosO) (hJ.mono hPosO) (hT0.mono hPosO)
    (k input) (k inputbar) hk hkbar ell tau Delta hell hell1 htau htauell hDelta
    hReserve hLb hInputb hInputbarb hCutb hNormalb hInputd hAb hBb hGb hJb hT0b
    hkb hkbarb hkd hPhib
  have hsame : positive ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)} = positive := by
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  simpa only [hsame] using hres

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_primitive_normalized_mean_bounds_uniform
