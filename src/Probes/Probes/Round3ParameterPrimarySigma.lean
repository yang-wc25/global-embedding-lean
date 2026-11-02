import Probes.Round3ParameterWholePrimaryPieces
import Probes.Round3PreparedPrimarySigma
import Probes.Round3PreparedFiniteAssembly

/-! One common finite index contains every actual parameter chart and every
phase's real compact refinement. Exact zero padding changes no sum and no
active support count. All physical parameter changes remain nonlinear chart
conjugations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

@[simp] theorem round3ParameterLiftedPrimaryCutoff_empty
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (nu : Fin Data.primaryCount) (W : Set (Ep × M)) :
    round3ParameterLiftedPrimaryCutoff Data i.2 nu W (round3PreparedPrimaryEmpty Data hd i nu W) = 0 := by
  funext z
  simp only [round3ParameterLiftedPrimaryCutoff_eq,round3PreparedPrimaryEmpty_cutoff,Pi.zero_apply,ite_self]

abbrev Round3ParameterWholePrimaryIndex
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta) :=
  Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => Sigma (fun nu : Fin Data.primaryCount => ↥(packet.s nu i)))

def round3ParameterWholePrimaryPiece
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (nu : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) :
    Round3PreparedPrimaryPiece Data a.1.2 nu ((Data.parameterChart a.1.2).target ×ˢ (univ : Set M)) :=
  round3PreparedPrimarySigmaPiece Data hd a.1 ((Data.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (fun mu => ↥(packet.s mu a.1)) (fun mu b => packet.piece mu a.1 b) nu a.2

def round3ParameterWholePrimaryFamily
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta) :
    Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (N := N)
      (Λ := Fin Data.primaryCount) (Β := Round3ParameterWholePrimaryIndex Data theta packet)
      (fun p x => Data.F (p,x)) :=
  round3ParameterOriginalPrimaryFamily Data hd hs hn (fun _ a => a.1.2)
    (fun _ a => (Data.parameterChart a.1.2).target ×ˢ (univ : Set M))
    (round3ParameterWholePrimaryPiece Data hd theta packet)

theorem round3ParameterWholePrimaryFamily_eta
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (nu : Fin Data.primaryCount) (a : Round3ParameterWholePrimaryIndex Data theta packet) :
    (round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu a =
      round3ParameterLiftedPrimaryCutoff Data a.1.2 nu _ (round3ParameterWholePrimaryPiece Data hd theta packet nu a) := by
  funext z
  exact (round3ParameterLiftedPrimaryCutoff_eq Data a.1.2 nu _ _ z).symm

theorem round3ParameterWholePrimaryFamily_eta_sum
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (nu : Fin Data.primaryCount) (z : P × M) :
    (∑ a, (round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu a z) =
      ∑ i, ∑ a : packet.s nu i, round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a) z := by
  simp_rw [round3ParameterWholePrimaryFamily_eta]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [round3ParameterLiftedPrimaryCutoff_eq]
  by_cases hz : z.1 ∈ (Data.parameterChart i.2).source
  · simp only [hz,ite_true,round3ParameterWholePrimaryPiece]
    exact round3_prepared_primary_sigma_cutoff_sum Data hd i _ (fun mu => ↥(packet.s mu i))
      (fun mu a => packet.piece mu i a) nu ((Data.parameterChart i.2) z.1,z.2)
  · simp only [hz,ite_false,Finset.sum_const_zero]

theorem round3ParameterWholePrimaryFamily_eta_card
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M) :
    (Finset.univ.filter (fun a : Sigma (fun mu => ↥(packet.s mu i)) =>
      z ∈ tsupport ((round3ParameterWholePrimaryFamily Data hd hs hn theta packet).eta nu ⟨i,a⟩))).card =
    (Finset.univ.filter (fun a : packet.s nu i => z ∈ tsupport
      (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)))).card := by
  simp_rw [round3ParameterWholePrimaryFamily_eta]
  rw [show (Finset.univ.filter (fun a : Sigma (fun mu => ↥(packet.s mu i)) => z ∈ tsupport
      (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (round3ParameterWholePrimaryPiece Data hd theta packet nu ⟨i,a⟩)))).card =
      ∑ a : Sigma (fun mu => ↥(packet.s mu i)), if z ∈ tsupport
        (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (round3ParameterWholePrimaryPiece Data hd theta packet nu ⟨i,a⟩)) then (1 : ℕ) else 0 from
      Finset.natCast_card_filter _ _]
  rw [Fintype.sum_sigma]
  have he (mu : Fin Data.primaryCount) :
      (∑ a : packet.s mu i, if z ∈ tsupport
        (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (round3ParameterWholePrimaryPiece Data hd theta packet nu ⟨i,⟨mu,a⟩⟩)) then (1 : ℕ) else 0) =
      if mu = nu then (Finset.univ.filter (fun a : packet.s nu i => z ∈ tsupport
        (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a)))).card else 0 := by
    by_cases h : mu = nu
    · subst mu
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active,ite_true]
      exact Finset.sum_boole _ _
    · simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,h,dite_false,
        round3ParameterLiftedPrimaryCutoff_empty,tsupport_zero,mem_empty_iff_false,ite_false,Finset.sum_const_zero]
  simp_rw [he]
  simp

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterWholePrimaryFamily_eta_sum
#print axioms GlobalEmbedding.Continuation.round3ParameterWholePrimaryFamily_eta_card
