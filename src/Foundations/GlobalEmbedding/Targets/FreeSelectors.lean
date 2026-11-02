import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.FreeSelectorProperties
import GlobalEmbedding.Paper.FreeHopfSelectorBaseCase
import GlobalEmbedding.Paper.FreeInductionDataExists
import GlobalEmbedding.Paper.FreeHopfSelectorFromNormalizedInverse
import GlobalEmbedding.Paper.FreeInductionEuclideanBlocks
import GlobalEmbedding.Paper.FreeRegularizedPairingInverse

/-!
# Free selectors on the entire finite Hopf product

Source: `literature/parallelizable-stable-plus-one/main.tex`, thm:free, lines 421–428.
DAG node: `thm-free`. This is the complete original target, pending independent statement review.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- For every positive number of factors and every original C_i≥2, one native smooth map
on the entire actual Hopf product has exact partial Gram I, all first and symmetric second
columns independent everywhere, and a single global native smooth unit section of their
line complement. Native C∞ refers to the same maps at every order. All derivatives are
along the original literal period-one factor flows, with their original 2π normalization.

Proof plan: induction on the positive number of factors. For one factor, use the accepted
actual unit-speed free space curve and its native smooth unit binormal. The real singleton
product identification transports the original curve and its actual two orbit derivatives.

For the successor, write m for the number of old factors, H for the old selector and ν for
its complementary unit section. The full accepted matrix proposition on the new sphere
with d=m+1 supplies the same f,P,Q=XP,η and all four actual zero periods, XQ=0 on κ=0,
and X²η=1 there. Embed F₀=(H,f,0_m) into the required Euclidean dimension. The native
old framed distribution and accepted partial immersion give A into R^(m+1). The actual
ordered cofactor of Y_iA gives n. Set T=(ν,e₂,…,e_(m+1)) and the literal displacement
Z=T(PA+δ₀ηQn). Its actual first metric variation vanishes. The full mixed-period expansion
uses av(PᵀQ), avη, orthogonality of n and its differentiated unit identity, and
av(η²QᵀXQ); derivatives Y_iν outside the complement are retained.

The mixed columns M_i are independent uniformly for one small positive δ₀. Actual Gram
projection gives n_δ=Qn+O(δ). On κ=0, XQ=0 and the twice-differentiated orthogonality
identity make QᵀX²Q skew, so the active pairing is exactly δ before projection and loses
only O(δ²) after projection. Compactness fixes one positive buffered curvature threshold.

Define the actual e=|XZ|², k₂=avκ²>0, b=κ av(e)/(2k₂), u=I_X(-e/2+κb), and
w_i=I_X(-inner(Y_iZ,XZ)-Y_i u). Average/primitive commutation and the mixed periods
prove the literal inputs have mean zero. The old free pairing Gram inverse constructs
W_H with the displayed first/second pairings in the source. With W=(W_H,uv+bJ₂v,0_m),
the genuine metric variation in W cancels the whole Gram of Z. The same actual polynomial
F₀+εZ+ε²W therefore has exactly ε³S₃+ε⁴S₄ residual with fixed native smooth coefficients.

Near κ=0 project off J₂v and divide actual mixed/active second columns by ε; away from
zero use unprojected columns and divide only mixed columns. Their genuine smooth quotient
extensions have independent limits. Actual Gram right inverses and the reconstruction
Π R S⁻¹ give the full original pairing inverse, with ε times that inverse native smooth
through zero. A fixed buffered curvature cutoff glues the full-range inverses linearly.
The accepted balanced correction, via the actual product-geometry bridge, gives a native
smooth correction of uniform vertical C² size O(ε²). Thus normalized columns change only
by O(ε); compact rank margins persist for one small positive ε. The corrected map has
exact Gram I and all free columns independent. The actual ordered cofactor of its D−1
columns gives the required global native smooth unit complementary section.

This uses one actual corrected map and one complement on the whole product at all orders.
The actual BalancedPairingIndex cardinality is already proved in BalancedPairing; together
with the accepted symmetric-square count it gives precisely a+s_a columns in a+s_a+1
dimensions, hence their orthogonal complement is a line. No desired map, normal, pivot,
period, inverse, correction, chosen orbit origin or extra curvature hypothesis is an input.
Source: thm:free statement lines 421–428 and complete proof lines 431–495. -/
theorem free_hopf_selectors_with_line_complement (a : ℕ) (ha : 1 ≤ a)
    (C : Fin a → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    ∃ F ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount a + a + 1)),
      FreeSelectorProperties (freeHopfModel C) (freeHopfProductFlow C) F ν := by
  induction a with
  | zero => omega
  | succ m ih =>
    let _ : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    by_cases hm : m = 0
    · subst m
      exact freeHopf_selector_base_case C hC
    · have hm' : 1 ≤ m := by omega
      obtain ⟨H, ν, hIH⟩ := ih hm' (freeHopfOldDimensions C) (fun i ↦ hC i.castSucc)
      obtain ⟨f, P, η, hf, hP, hη, hSO, havQ, hperiod, hmean, hquad,
        hstationary, haccel, A, n, hA, hn, hLI, hunit, hperp,
        δ₀, d₀, lam, B, hδ, hd, hlam, hB, hpivot, W, hW, hjoint, hres, hS3, hS4⟩ :=
        freeHopf_induction_data_exists C hm' hC H ν hIH
      let F0 := freeHopfInductionBase C H f
      let Z := freeHopfInductionZ C ν P (orbitDeriv planarHopfFlow P) η δ₀ A n
      let family := fun p : ℝ × FreeHopfProduct C ↦ freePolynomialFamily F0 Z W p.1 p.2
      let S3 := freeMetricCrossTerm Z W (freeHopfGeneratorSection C)
      let S4 := balancedGeometry W hW (freeHopfGeneratorSection C)
      let Dstep := (freeSymmetricColumnCount m + m + 1) + (2 + m)
      have hbackend : ∃ εbar μ : ℝ, 0 < εbar ∧ 0 < μ ∧
          ∃ (inv : ℝ → FreeHopfProduct C →
            EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
              EuclideanSpace ℝ (Fin Dstep))
            (invtilde : ℝ × FreeHopfProduct C →
              EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
                EuclideanSpace ℝ (Fin Dstep))
            (patch : Bool → Set (FreeHopfProduct C))
            (prj : Bool → FreeHopfProduct C →
              EuclideanSpace ℝ (Fin Dstep) →L[ℝ] EuclideanSpace ℝ (Fin Dstep))
            (masked : Bool → BalancedPairingIndex (m + 1) → Bool),
          (∀ x, ∃ p, x ∈ patch p) ∧
          (∀ p x, x ∈ patch p → ‖prj p x‖ ≤ 1) ∧
          (∀ ε, ε ∈ Metric.ball (0 : ℝ) εbar → ε ≠ 0 → ∀ x,
            IsBalancedPairingRightInverse (fun y ↦ family (ε, y))
              (freeHopfGenerator C) x (inv ε x)) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
            𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
              EuclideanSpace ℝ (Fin Dstep)) ∞ invtilde
              (Metric.ball (0 : ℝ) εbar ×ˢ Set.univ) ∧
          (∀ ε, ε ∈ Metric.ball (0 : ℝ) εbar → ε ≠ 0 → ∀ x,
            invtilde (ε, x) = ε • inv ε x) ∧
          (∀ ε, 0 < ε → ε < εbar → ∀ p x, x ∈ patch p → ∀ u,
            μ * ‖u‖ ≤ ‖freeColumnOperator
              (freeNormalizedColumns (prj p x) (masked p) ε
                (freeFlowColumns (freeHopfProductFlow C) (fun y ↦ family (ε, y)) x)) u‖) := by
        -- The actual normalized inverse on these same fixed genuine data.
        have hapi :
          let Z := freeHopfInductionZ C ν P (orbitDeriv planarHopfFlow P) η δ₀ A n
          let F0 := freeHopfInductionBase C H f
          let κ := fun x ↦ planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2
          ∃ d ε₀ μ : ℝ, d = d₀ / 2 ∧ 0 < d ∧ 0 < ε₀ ∧ 0 < μ ∧
            ∃ R Rtilde : ℝ × FreeHopfProduct C →
              EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
                EuclideanSpace ℝ (Fin (Dstep)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod (freeHopfModel C))
                𝓘(ℝ, EuclideanSpace ℝ (BalancedPairingIndex (m + 1)) →L[ℝ]
                  EuclideanSpace ℝ (Fin (Dstep))) ∞ Rtilde
                    (Metric.ball (0 : ℝ) ε₀ ×ˢ Set.univ) ∧
              (∀ ε, |ε| < ε₀ → ε ≠ 0 → ∀ x,
                IsBalancedPairingRightInverse (freePolynomialFamily F0 Z W ε)
                  (freeHopfGenerator C) x (R (ε, x)) ∧ Rtilde (ε, x) = ε • R (ε, x)) ∧
              (∀ ε, 0 < ε → ε < ε₀ → ∀ x,
                (|κ x| ≤ d → ∀ u, μ * ‖u‖ ≤ ‖freeColumnOperator
                  (freeNormalizedColumns
                    (freeInductionNearProjection (freeSymmetricColumnCount m + m + 1) m
                      (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2))
                    (freeNearColumnMask m) ε
                    (freeFlowColumns (freeHopfProductFlow C) (freePolynomialFamily F0 Z W ε) x)) u‖) ∧
                (d / 3 ≤ |κ x| → ∀ u, μ * ‖u‖ ≤ ‖freeColumnOperator
                  (freeNormalizedColumns (ContinuousLinearMap.id ℝ _) (freeFarColumnMask m) ε
                    (freeFlowColumns (freeHopfProductFlow C)
                      (freePolynomialFamily F0 Z W ε) x)) u‖)) := by
          have hQ := contMDiff_orbitDeriv planarHopfFlow
            (planarHopfFlow_contMDiff (C (Fin.last m))) P hP
          exact freeHopf_induction_pairing_inverse C H ν hIH f hf P
            (orbitDeriv planarHopfFlow P) hP hQ (fun _ ↦ rfl) η hη
            δ₀ d₀ lam hδ hd hlam A n hA hn
            (fun x ↦ (hpivot (freeHopfProductSplit C x)).1)
            (fun x ↦ (hpivot (freeHopfProductSplit C x)).2.2.2) W hW
        obtain ⟨d, εbar, μ, hdeq, hdp, hbar, hμ, inv, invtilde, htilde, hinv, hb⟩ := hapi
        let κ := fun x : FreeHopfProduct C ↦
          planarOrbitCurvature planarHopfFlow f (freeHopfProductSplit C x).2
        let patch : Bool → Set (FreeHopfProduct C) := fun p ↦
          if p then {x | |κ x| ≤ d} else {x | d / 3 ≤ |κ x|}
        let prj : Bool → FreeHopfProduct C →
            EuclideanSpace ℝ (Fin Dstep) →L[ℝ] EuclideanSpace ℝ (Fin Dstep) :=
          fun p x ↦ if p then freeInductionNearProjection (freeSymmetricColumnCount m + m + 1) m
            (orbitDeriv planarHopfFlow f (freeHopfProductSplit C x).2)
          else ContinuousLinearMap.id ℝ _
        let masked : Bool → BalancedPairingIndex (m + 1) → Bool :=
          fun p ↦ if p then freeNearColumnMask m else freeFarColumnMask m
        have htime {ε : ℝ} (hε : ε ∈ Metric.ball (0 : ℝ) εbar) : |ε| < εbar := by
          simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
        refine ⟨εbar, μ, hbar, hμ, (fun ε x ↦ inv (ε, x)), invtilde, patch, prj, masked,
          ?_, ?_, ?_, htilde, ?_, ?_⟩
        · intro x
          by_cases hx : |κ x| ≤ d
          · exact ⟨true, hx⟩
          · refine ⟨false, ?_⟩
            change d / 3 ≤ |κ x|
            linarith [lt_of_not_ge hx]
        · intro p x _
          cases p
          · exact ContinuousLinearMap.norm_id_le
          · exact freeInductionNearProjection_norm_le _ _ _
        · intro ε hε hne x
          exact (hinv ε (htime hε) hne x).1
        · intro ε hε hne x
          exact (hinv ε (htime hε) hne x).2
        · intro ε hε he p x hx u
          cases p
          · exact (hb ε hε he x).2 hx u
          · exact (hb ε hε he x).1 hx u
      obtain ⟨εbar, μ, hbar, hμ, inv, invtilde, patch, prj, masked,
        hcover, hprj, hinv, htilde, hscale, hmargin⟩ := hbackend
      have hfinal := freeHopf_selector_from_normalized_inverse C
      rw [← free_induction_target_dimension m] at hfinal ⊢
      exact hfinal (Metric.ball (0 : ℝ) εbar) Metric.isOpen_ball (Metric.mem_ball_self hbar)
        family hjoint.contMDiffOn S3 S4 (fun ε _ ↦ hres ε) inv hinv invtilde htilde hscale
        hμ hbar patch hcover prj masked hprj hmargin


#print axioms free_hopf_selectors_with_line_complement

end GlobalEmbedding.Paper
