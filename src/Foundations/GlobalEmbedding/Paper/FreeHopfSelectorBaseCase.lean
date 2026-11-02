import GlobalEmbedding.Targets.PlanarSelectors
import GlobalEmbedding.Paper.FreeHopfProductNative
import GlobalEmbedding.Paper.FreeSelectorProperties

/-!
# The genuine singleton Hopf selector

The accepted planar free curve supplies the original a=1 case of thm:free on the
actual native Hopf product. No different flow, column family, or target dimension is used.
Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 421–432.
-/

open Manifold
open scoped ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- Pull back the accepted unit-speed planar free space curve and its global unit
binormal by the actual singleton factor projection. The literal product orbit derivatives
are the planar derivatives. The two actual first/symmetric-second indices inject into
the accepted independent pair, and unit speed gives the singleton identity Gram matrix.
Thus all original selector and global line-complement properties hold in exactly R³.
Source: thm:free, base case, lines 421–432. -/
theorem freeHopf_selector_base_case (C : Fin 1 → ℕ) (hC : ∀ i, 2 ≤ C i) :
    letI : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
    ∃ F ν : FreeHopfProduct C →
        EuclideanSpace ℝ (Fin (freeSymmetricColumnCount 1 + 1 + 1)),
      FreeSelectorProperties (freeHopfModel C) (freeHopfProductFlow C) F ν := by
  let _ : ∀ i, Fact (0 < C i) := fun i ↦ ⟨by have := hC i; omega⟩
  have hdim : freeSymmetricColumnCount 1 + 1 + 1 = 3 := by
    rw [free_symmetric_column_count]
  change ∃ F ν : FreeHopfProduct C →
      EuclideanSpace ℝ (Fin (freeSymmetricColumnCount 1 + 1 + 1)), _
  rw [hdim]
  obtain ⟨c, ν, hc, hν, hspeed, hli, hunit, horth₁, horth₂⟩ :=
    planar_hopf_free_curve (C 0) (hC 0)
  have hder (g : PlanarHopfSphere (C 0) → SpaceCurve) (i : Fin 1)
      (x : FreeHopfProduct C) :
      orbitDeriv (freeHopfProductFlow C i) (fun z ↦ g (z 0)) x =
        orbitDeriv planarHopfFlow g (x 0) := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    unfold orbitDeriv
    congr 1
  have hsecond (g : PlanarHopfSphere (C 0) → SpaceCurve) (i j : Fin 1)
      (x : FreeHopfProduct C) :
      orbitDeriv (freeHopfProductFlow C i)
          (orbitDeriv (freeHopfProductFlow C j) (fun z ↦ g (z 0))) x =
        orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow g) (x 0) := by
    have he : orbitDeriv (freeHopfProductFlow C j) (fun z ↦ g (z 0)) =
        fun z ↦ orbitDeriv planarHopfFlow g (z 0) := funext (hder g j)
    rw [he]
    exact hder _ i x
  let index : BalancedPairingIndex 1 → Fin 2 := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
  have hinj : Function.Injective index := by
    rintro (i | ij) (j | jk) h
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · norm_num [index] at h
    · norm_num [index] at h
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  have hcolumns (x : FreeHopfProduct C) :
      freeFlowColumns (freeHopfProductFlow C) (fun z ↦ c (z 0)) x =
        ![orbitDeriv planarHopfFlow c (x 0),
          orbitDeriv planarHopfFlow (orbitDeriv planarHopfFlow c) (x 0)] ∘ index := by
    funext j
    rcases j with i | ij
    · simpa [freeFlowColumns, index] using hder c i x
    · simpa [freeFlowColumns, index] using hsecond c ij.val.1 ij.val.2 x
  refine ⟨(fun x ↦ c (x 0)), (fun x ↦ ν (x 0)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp (freeHopfProduct_contMDiff_apply C 0)
  · exact hν.comp (freeHopfProduct_contMDiff_apply C 0)
  · intro x
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp [Matrix.gram, hder, hspeed]
  · intro x
    rw [hcolumns]
    exact (hli (x 0)).comp index hinj
  · exact fun x ↦ hunit (x 0)
  · intro x j
    rcases j with i | ij
    · simpa only [freeFlowColumns, hder] using horth₁ (x 0)
    · simpa only [freeFlowColumns, hsecond] using horth₂ (x 0)

#print axioms freeHopf_selector_base_case

end GlobalEmbedding.Paper
