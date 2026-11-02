import GlobalEmbedding.Paper.IncrementsNormalizedPrimarySource
import GlobalEmbedding.Paper.IncrementsNormalizedPrimarySourceRegularity

/-! Actual normalized primary sources for a subordinate family. These are the
original h=0 sources with the subordinate cutoff inside the normal amplitude.
All parameter/source derivatives, same-input differences and true supports are
produced from primitive amplitude and actual first-row second-form data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup T] [NormedSpace ℝ T] {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actual_joint_normalized_source_family_profiles
    (j : ℕ) (c Bnd : ℝ) (hc : 0 < c) (hBnd : 0 ≤ Bnd) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Type*}
      (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ, V) ∞ (F b)) (chart : Ep → D → M)
      (normal : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (chart b x))
      (O S : Set X) (_hO : IsOpen O) (_hSO : S ⊆ O)
      (L : X → T →L[ℝ] ℝ) (input inputbar : X → T) (cutoff : X → ℝ) (cs : A → X → ℝ)
      (_hL : ContDiffOn ℝ ∞ L O) (_hInput : ContDiffOn ℝ ∞ input O)
      (_hInputbar : ContDiffOn ℝ ∞ inputbar O) (_hCut : ContDiffOn ℝ ∞ cutoff O)
      (_hcs : ∀ a, ContDiffOn ℝ ∞ (cs a) O)
      (_hNormal : ContDiffOn ℝ ∞ (fun z : X => (normal z.1 z.2 : V)) O)
      (_hBrow : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F z.1) (hF z.1) (chart z.1) z.2 0 i : V)) O)
      (ell tau Delta : ℝ) (_hell : 0 < ell) (_htau : 0 < tau) (_hDelta : 0 ≤ Delta)
      (_hReserve : ∀ z ∈ S, c ≤ L z (input z) ∧ c ≤ L z (inputbar z))
      (_hLb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r L z‖ ≤ Bnd)
      (_hInputb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r input z‖ ≤ Bnd)
      (_hInputbarb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r inputbar z‖ ≤ Bnd)
      (_hCutb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r cutoff z‖ ≤ Bnd)
      (_hcsb : ∀ a, ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (cs a) z‖ ≤ Bnd)
      (_hNormalb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y : X => (normal y.1 y.2 : V)) z‖ ≤ Bnd)
      (_hBrowb : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y : X => fun i : Fin (m+1) =>
          (incrementsModeSecondForm (F y.1) (hF y.1) (chart y.1) y.2 0 i : V)) z‖ ≤ Bnd)
      (_hInputd : ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
        (fun y => input y-inputbar y) z‖ ≤ Delta),
    let positive := O ∩ {z | 0 < L z (input z)} ∩ {z | 0 < L z (inputbar z)}
    let vf := fun (B : X → T) (a : A) (b : Ep) (x : D) =>
      cs a (b,x) • ((Real.sqrt 2*1*tau*(cutoff (b,x)*Real.sqrt (L (b,x) (B (b,x))))) • normal b x)
    let k := fun (B : X → T) (a : A) (z : X) => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (chart z.1) (fun _ _ _ => 0) (vf B a z.1) z.2)
    IsOpen positive ∧ S ⊆ positive ∧
    (∀ a, ContDiffOn ℝ ∞ (k input a) positive) ∧
    (∀ a, ContDiffOn ℝ ∞ (k inputbar a) positive) ∧
    (∀ a, ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (k input a) z‖ ≤ K*tau) ∧
    (∀ a, ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r (k inputbar a) z‖ ≤ K*tau) ∧
    (∀ a, ∀ r ≤ j, ∀ z ∈ S, ell^r * ‖iteratedFDeriv ℝ r
      (fun y => k input a y-k inputbar a y) z‖ ≤ K*tau*Delta) ∧
    (∀ a, tsupport (k input a) ⊆ tsupport (fun z => cs a z*cutoff z)) ∧
    (∀ a, tsupport (k inputbar a) ⊆ tsupport (fun z => cs a z*cutoff z)) := by
  obtain ⟨K,hK,hbound⟩ := increments_normalized_primary_source_bounds
    (I := I) (M := M) (Ep := Ep) (T := T) (m := m) (N := N) j c Bnd Bnd hc hBnd hBnd
  refine ⟨K,hK,?_⟩
  intro A F hF chart normal O S hO hSO L input inputbar cutoff cs hL hInput hInputbar hCut
    hcs hNormal hBrow ell tau Delta hell htau hDelta hReserve hLb hInputb hInputbarb
    hCutb hcsb hNormalb hBrowb hInputd positive vf k
  have hPos : IsOpen positive := by
    have ha : IsOpen (O ∩ {z | 0 < L z (input z)}) :=
      (hL.clm_apply hInput).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    have hb : IsOpen (O ∩ {z | 0 < L z (inputbar z)}) :=
      (hL.clm_apply hInputbar).continuousOn.isOpen_inter_preimage hO isOpen_Ioi
    convert ha.inter hb using 1
    ext z
    simp only [positive,Set.mem_inter_iff,Set.mem_ofPred_eq]
    tauto
  have hSpos : S ⊆ positive := fun z hz =>
    ⟨⟨hSO hz,hc.trans_le (hReserve z hz).1⟩,hc.trans_le (hReserve z hz).2⟩
  have hsize (a : A) := hbound F hF chart normal O S hO L input inputbar cutoff (cs a)
    (fun z hz => hSO hz.1) hL hInput hInputbar hCut (hcs a) hNormal hBrow
    ell Delta tau hell hDelta (fun z hz => hReserve z hz.1)
    (fun r hr z hz => hLb r hr z hz.1) (fun r hr z hz => hInputb r hr z hz.1)
    (fun r hr z hz => hInputbarb r hr z hz.1) (fun r hr z hz => hCutb r hr z hz.1)
    (fun r hr z hz => hcsb a r hr z hz.1) (fun r hr z hz => hNormalb r hr z hz.1)
    (fun r hr z hz => hBrowb r hr z hz.1) (fun r hr z hz => hInputd r hr z hz.1)
  have hsizeBar (a : A) := hbound F hF chart normal O S hO L inputbar inputbar cutoff (cs a)
    (fun z hz => hSO hz.1) hL hInputbar hInputbar hCut (hcs a) hNormal hBrow
    ell 0 tau hell le_rfl (fun z hz => ⟨(hReserve z hz.1).2,(hReserve z hz.1).2⟩)
    (fun r hr z hz => hLb r hr z hz.1) (fun r hr z hz => hInputbarb r hr z hz.1)
    (fun r hr z hz => hInputbarb r hr z hz.1) (fun r hr z hz => hCutb r hr z hz.1)
    (fun r hr z hz => hcsb a r hr z hz.1) (fun r hr z hz => hNormalb r hr z hz.1)
    (fun r hr z hz => hBrowb r hr z hz.1) (fun r hr z hz => by simp)
  refine ⟨hPos,hSpos,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact (increments_normalized_primary_source_contDiffOn F hF chart normal positive O hPos hO
      L input cutoff (cs a) (fun z hz => hz.1.1.1) hL hInput hCut (hcs a) hNormal hBrow
      (fun z hz => hz.1.1.2) tau).2
  · intro a
    exact (increments_normalized_primary_source_contDiffOn F hF chart normal positive O hPos hO
      L inputbar cutoff (cs a) (fun z hz => hz.1.1.1) hL hInputbar hCut (hcs a) hNormal hBrow
      (fun z hz => hz.1.2) tau).2
  · intro a
    simpa only [abs_of_pos htau] using (hsize a).1
  · intro a
    simpa only [abs_of_pos htau] using (hsizeBar a).1
  · intro a
    simpa only [abs_of_pos htau] using (hsize a).2.1
  · intro a
    exact (hsize a).2.2.1
  · intro a
    exact (hsize a).2.2.2

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_normalized_source_family_profiles
