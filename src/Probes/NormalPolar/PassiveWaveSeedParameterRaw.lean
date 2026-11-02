import NormalPolar.PassiveWaveSeedObservation
import NormalPolar.JointSecondaryGroupedParameterRaw

/-! The full grouped parameter-chart raw record is built from the actual
seed observation data. The given original sample set is retained exactly;
only its genuine source and parameter projections are used for membership. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {S P M : Type*} {m N d r : ℕ}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [Subsingleton S]
  [TopologicalSpace P]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "IM" => 𝓘(ℝ,D)

def passiveWaveSeed_parameter_raw
    (B : OpenPartialHomeomorph P Ep) (e : OpenPartialHomeomorph M D)
    (he : e ∈ maximalAtlas IM ∞ M)
    (F : S → M → V) (hF : ∀ s, ContMDiff IM 𝓘(ℝ,V) ∞ (F s))
    (c : (l : Fin r) → Sub l → S → D → M)
    (chi : (l : Fin r) → Sub l → S × D → ℝ)
    (nu : (l : Fin r) → (s : Sub l) → (b : S) → (x : D) →
      normalSpace (I := IM) (F b) (c l s b x))
    (a : (l : Fin r) → Sub l → OpenPartialHomeomorph (S × M) (S × D))
    (K : (l : Fin r) → Sub l → Set (S × M))
    (n j : ℕ) (ell Mg Bchi Bnu : ℝ) (hell : 0 ≤ ell)
    (R : Set D) (hR : R ⊆ e.target)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (phase : Fin r → S × M → ℝ) (Mphase : ℝ)
    (profiles : JointGroupedPrescribedObservationProfiles F hF c chi nu a univ K
      n (j+1) ell Mg Bchi Bnu (fun z : S × D => (z.1,e.symm z.2))
      ((univ : Set S) ×ˢ e.target) ((univ : Set S) ×ˢ R) T phase Mphase)
    (Sn : Set (Ep × D)) (hSnB : ∀ z ∈ Sn, z.1 ∈ B.target)
    (hSnR : ∀ z ∈ Sn, z.2 ∈ R) :
    JointGroupedPrescribedParameterChartRawData
      (fun _ : P => F 0) (fun _ => hF 0) (fun l s _ => c l s 0)
      (fun l s (z : P × D) => chi l s (0,z.2)) (fun l s _ => nu l s 0)
      (fun l (z : P × M) => phase l (0,z.2))
      (fun l s => passiveParameterChart 0 (a l s))
      B e (B.target ×ˢ e.target) Sn n j ell Mg Bchi Bnu Mphase (fun k => 1+T k) := by
  refine {
    domain := {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ (univ : Set (S × M))}
    carrier := fun l s => {z : Ep × M | z.1 ∈ B.target ∧ (0,z.2) ∈ K l s}
    domain_open := (B.open_target.preimage continuous_fst).inter isOpen_univ
    observer_smooth := ?_
    observer_domain := fun z hz => ⟨hz.1,mem_univ _⟩
    raw := ?_ }
  · have hfirst : ContMDiffOn 𝓘(ℝ,Ep × D) 𝓘(ℝ,Ep) ∞
        (fun z : Ep × D => z.1) (B.target ×ˢ e.target) := contDiffOn_fst.contMDiffOn
    have hsecond := (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      (contDiffOn_snd.contMDiffOn : ContMDiffOn 𝓘(ℝ,Ep × D) IM ∞ Prod.snd
        (B.target ×ˢ e.target)) (fun z hz => hz.2)
    exact hfirst.prodMk hsecond
  · have hh := passiveWaveSeed_observation B e F hF c chi nu a univ K n (j+1)
      ell Mg Bchi Bnu hell ((univ : Set S) ×ˢ e.target) ((univ : Set S) ×ˢ R)
      (fun z hz => ⟨hz.1,hR hz.2⟩) T hT phase Mphase profiles Sn hSnB
      (fun z hz => ⟨mem_univ _,hSnR z hz⟩)
    have hO : {z : Ep × D | z.1 ∈ B.target ∧ (0,z.2) ∈ ((univ : Set S) ×ˢ e.target)} =
        B.target ×ˢ e.target := by ext z; simp
    rw [hO] at hh
    exact hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveWaveSeed_parameter_raw
