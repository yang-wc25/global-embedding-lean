import Probes.Round3RepairUniformCostFactory

/-! A genuine next state from the literal same SF, SH and global U.
Both stay and advance are covered.  The old and new states use exactly one
fixed Ω/Q domain; all higher-order recurrences survive in the result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uM uP uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M : Type uM} {P : Type uP} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairGeneratedCostsChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairGeneratedCostsIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)




/-- The chosen uniform costs preserve every supplied primitive profile. -/
def Round3RepairPrimitiveCosts.UsesProfiles (cost : Round3RepairPrimitiveCosts)
    (profile : Round3RepairPrimitiveProfiles) : Prop :=
  cost.rho=profile.rho ∧ cost.reserve=profile.reserve ∧ cost.Rsub=profile.Rsub ∧
  cost.Lprimary=profile.Lprimary ∧ cost.Rsecondary=profile.Rsecondary ∧
  cost.Bnd=profile.Bnd ∧ cost.Mg=profile.Mg ∧ cost.Dinput=profile.Dinput ∧ cost.T=profile.T ∧
  cost.Bsec=profile.Bsec ∧ cost.Msec=profile.Msec ∧ cost.Ccut=profile.Ccut ∧
  cost.Tsec=profile.Tsec ∧ cost.Tinv=profile.Tinv ∧ cost.Tobs=profile.Tobs

/-- Fixed numerical output of the actual smoother/uniform theorem. The
explicit named threshold and the raw profile bindings remain inspectable. -/
structure Round3RepairGeneratedCosts (profile : Round3RepairPrimitiveProfiles)
    (q : ℕ) (hq : 1 ≤ q) (budget : ℝ) where
  targetCost : ℕ → ℝ
  target_nonneg : ∀ j, 0 ≤ targetCost j
  cost : Round3RepairPrimitiveCosts
  profiles : cost.UsesProfiles profile
  named_threshold : cost.Theta = parameterRound2_uniformMeanThreshold
    (fun j => targetCost j*budget+(j+1)*packet.closedReferenceProfile j)
    (round3ParameterMeanSizeCost.{uM,uTr,uP,uΛ,uΒ} (m := m) (d := d) (N := N) (M := M) (Tr := Tr)
      q profile.Rsub profile.Lprimary hq profile.reserve profile.reserve_pos profile.Bnd profile.Mg
      profile.Bnd_nonneg profile.Mg_nonneg profile.T profile.T_nonneg)
    profile.rho q (q+4)
  data : ∀ state : Round3RepairCurrentSmoothingState packet q budget,
    Round3RepairClosedUniformMeanData (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost state

/-- There are no current-map, target or output-budget inputs to this factory. -/
theorem round3_repair_generate_costs [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (profile : Round3RepairPrimitiveProfiles)
    (q : ℕ) (hq : 1 ≤ q) (budget : ℝ) :
    Nonempty (Round3RepairGeneratedCosts (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet profile q hq budget) := by
  obtain ⟨Ctarget,hCtarget,hTheta,hTheta1,Cmap,Cmetric,hCmap,hCmetric,hData⟩ :=
    round3_repair_uniform_costs_from_actual_closed_target (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet hBS0 hTS0 hBP0 hTP0 hK q hq budget profile
  refine ⟨{ targetCost := Ctarget
            target_nonneg := hCtarget
            cost := profile.withUniform _ hTheta hTheta1 Cmap Cmetric hCmap hCmetric
            profiles := ?_
            named_threshold := rfl
            data := fun state => Classical.choice (hData state) }⟩
  simp [Round3RepairPrimitiveCosts.UsesProfiles,Round3RepairPrimitiveProfiles.withUniform]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_generate_costs
