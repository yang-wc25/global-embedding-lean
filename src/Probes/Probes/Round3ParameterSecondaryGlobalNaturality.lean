import Probes.Round3ParameterSecondaryForcingNaturality
import Probes.Round3ParameterSecondaryLocality

/-! The very same supported secondary wave on the physical parameter manifold.
The proof uses open-target locality of the inhomogeneous finite solver, so it
needs no off-target preservation or arbitrary smooth extension hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m+1) → Fin (m+1) → ℝ
variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Label) (Β := SubPrimary) F)
  (B : OpenPartialHomeomorph P Q)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
include hg

theorem round3ParameterSecondary_pullback_channels
    (r : (Label × Label) × Fin 4) (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart)
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t,x) ∈ c.chart.target) :
    let FQ := fun t => F (B.symm t)
    let hFQ := fun t => hF (B.symm t)
    let gQ := round3ParameterPrimaryPullback F g B
    let inputQ := fun t => input (B.symm t)
    let RQ := round3ParameterSecondaryRealForcing FQ hFQ gQ inputQ length tau delta r (c.pullback B)
    let IQ := round3ParameterSecondaryImagForcing FQ hFQ gQ inputQ length tau delta r (c.pullback B)
    let R := round3ParameterSecondaryRealForcing F hF g input length tau delta r c
    let J := round3ParameterSecondaryImagForcing F hF g input length tau delta r c
    actualSecondaryRealChannel FQ hFQ (c.pullback B).c RQ IQ tau length (t,x) =
      actualSecondaryRealChannel F hF c.c R J tau length (B.symm t,x) ∧
    actualSecondaryImagChannel FQ hFQ (c.pullback B).c RQ IQ tau length (t,x) =
      actualSecondaryImagChannel F hF c.c R J tau length (B.symm t,x) := by
  intro FQ hFQ gQ inputQ RQ IQ R J
  let O : Set D := {y | (B.symm t,y) ∈ c.chart.target}
  have hO : IsOpen O := c.chart.open_target.preimage (continuous_const.prodMk continuous_id)
  let RP : Q × D → Source := fun z => R (B.symm z.1,z.2)
  let IP : Q × D → Source := fun z => J (B.symm z.1,z.2)
  have hr : EqOn (fun y => RQ (t,y)) (fun y => RP (t,y)) O := by
    intro y hy
    exact round3ParameterSecondary_pullback_realForcing F hF g B hg input length tau delta r c hc t ht y hy
  have hi : EqOn (fun y => IQ (t,y)) (fun y => IP (t,y)) O := by
    intro y hy
    exact round3ParameterSecondary_pullback_imagForcing F hF g B hg input length tau delta r c hc t ht y hy
  exact ⟨round3ParameterSecondary_realChannel_eqOn FQ hFQ (c.pullback B).c RQ IQ RP IP t O hr hi hO tau length hx,
    round3ParameterSecondary_imagChannel_eqOn FQ hFQ (c.pullback B).c RQ IQ RP IP t O hr hi hO tau length hx⟩

theorem round3ParameterSecondary_pullback_piece
    (r : (Label × Label) × Fin 4) (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart)
    (t : Q) (ht : t ∈ B.target) (x : M) :
    round3ParameterSecondaryPiece (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta r (c.pullback B) (t,x) =
      round3ParameterSecondaryPiece F hF g input length tau delta r c (B.symm t,x) := by
  classical
  have hi := round3ParameterChartPullback_source_iff B c.chart hc (t,x) ht
  by_cases hx : (B.symm t,x) ∈ c.chart.source
  · have hb := hi.mpr hx
    have ha : (c.pullback B).chart (t,x) = (t,(c.chart (B.symm t,x)).2) := by
      change round3ParameterChartPullback B c.chart (t,x) = _
      rw [round3ParameterChartPullback_apply, hc _ hx]
      simp only [B.right_inv ht]
    have hp : c.chart (B.symm t,x) = (B.symm t,(c.chart (B.symm t,x)).2) :=
      Prod.ext (hc _ hx) rfl
    have htarget : (B.symm t,(c.chart (B.symm t,x)).2) ∈ c.chart.target := by
      rw [← hp]
      exact c.chart.map_source hx
    obtain ⟨hr,hj⟩ := round3ParameterSecondary_pullback_channels F hF g B hg input length tau delta r c hc
      t ht (c.chart (B.symm t,x)).2 htarget
    simp only [round3ParameterSecondaryPiece, round3ParameterSupportedWave]
    change Real.cos (_ / tau) • (if (t,x) ∈ (round3ParameterChartPullback B c.chart).source then _ else 0) -
      Real.sin (_ / tau) • (if (t,x) ∈ (round3ParameterChartPullback B c.chart).source then _ else 0) = _
    rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left hx, ite_eq_left hx, ha, hr, hj, hp]
    rfl
  · have hb := mt hi.mp hx
    simp only [round3ParameterSecondaryPiece, round3ParameterSupportedWave]
    change Real.cos (_ / tau) • (if (t,x) ∈ (round3ParameterChartPullback B c.chart).source then _ else 0) -
      Real.sin (_ / tau) • (if (t,x) ∈ (round3ParameterChartPullback B c.chart).source then _ else 0) = _
    rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hx, ite_eq_right hx]
    simp only [smul_zero, sub_zero]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondary_pullback_piece
