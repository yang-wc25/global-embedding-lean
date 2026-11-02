import Probes.Round3ParameterUniformGlobalIncrement

/-! # One actual global mean-corrected increment for arbitrary parameters

Primitive mean reserve profiles produce one global Kq.  A single fixed
secondary family then produces one literal U, independent of j.  The theorem
simultaneously proves the original zero/first weighted displacement bounds,
the original (6.8) metric error, and joint smoothness throughout the common
physical domain W.  Constants and the finite mean threshold are chosen
before F, primitive witnesses, the secondary family, epsilon, delta and j.
Only primitive raw evidence is required; no output estimate is a premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff ENNReal Classical
namespace GlobalEmbedding.Continuation
universe uM uTr uP uΛ uΒ uSubSecondary
variable {m d N c : ℕ} {M : Type uM} {Tr : Type uTr} {P : Type uP}
  {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def Round3ParameterUniformFixedInput
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho ell : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ) (Theta : ℝ)
    (Rsecondary : ℕ) (Bsec Msec Ccut : ℕ → ℝ) (Tsec Tinv Tobs : ℕ → ℕ → ℝ)
    (Cmap Cmetric : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F t)) : Prop := ∀
      (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Λ) (Β := Β) F)
      (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β)) (primary : Λ → Set (P × M)),
      Round3ParameterMeanRawReserveSupply (Tr := Tr) A B S W p H rho q Rsub Lprimary reserve
        Bnd Mg Dinput T F hF g primary ell →
      ∃ hsm : ∀ epsilon, 0 < epsilon → epsilon ≤ 1 →
        ∀ K : {K : parameterRound2_originalTensorGermSpace A B S W // p 0 (K-H) < rho},
        round3ParameterPrimaryMeanError F hF g K.val.val (q+2) (epsilon*ell) ∈
          parameterRound2_originalTensorGermSpace A B S W,
      ∀ epsilon, 0 < epsilon → epsilon < Theta → ∀ delta, 0 ≤ delta → delta ≤ epsilon*ell →
      let Top := round3ParameterMeanReserveOperator A B S W p H rho ell F hF g q hsm
      let Kq := (meanReserveStep (p 0) H rho (Top epsilon))^[q] H
      ∀ (G : Set (P × M)) (hG : IsOpen G), G ⊆ W →
      (∀ i, MapsTo (incrementsOriginalJointPoint A B i) (S i) G) →
      let gG := round3Parameter_restrictPrimaryFamily F g G hG
      ∀ (choice : ActualSecondarySignedRecord Λ → SubSecondary → Round3ParameterSecondaryChoice P M m),
      (∀ r a, Round3ParameterChartPreserves (choice r a).chart) →
      (∀ j, Nonempty (Round3ParameterRawAtlasData (Tr := Tr) A B F hF gG Kq.val Kq.val
        (j+2*q+8) (j+q+4) j q Rsub Lprimary Rsecondary reserve (Bsec j) (Msec j) (Ccut j)
        (Tsec j) (Tinv j) (Tobs j) G primary S ell delta (epsilon*ell) 0 choice)) →
      p 0 (Kq-H) ≤ rho/2 ∧
      Round3ParameterJointIncrementConclusion A B S G (fun z => F z.1 z.2)
        (round3ParameterIncrementMap F hF gG Kq.val (q+2) (epsilon*ell) delta choice)
        H.val q delta (epsilon*ell) ell Cmap Cmetric

end GlobalEmbedding.Continuation
