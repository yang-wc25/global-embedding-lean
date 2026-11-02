import NormalPolar.PassiveOriginalCoordinateNorm

/-! Exact passive transport of the original coordinate-partial norm, even
before regularity has been supplied. This uses the literal within-line
derivative defining the paper norm: a source coordinate gives the same
one-variable function, and a parameter coordinate gives a constant function.
There is no new smoothness assumption on the phase-covector or other
primitive coordinate fields. The actual open differentiation domains and
their separate evaluation domains are retained. -/

noncomputable section
open Set Function
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper

variable {n d q : ℕ}

theorem passiveOriginal_lineDeriv_source
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (D : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalSourceProjection (d := d)) D O)
    (x : Fin (n+d) → ℝ) (hx : x ∈ D) (i : Fin n) :
    lineDerivWithin ℝ (f ∘ passiveOriginalSourceProjection (d := d)) D x
        (Pi.single (Fin.castAdd d i) 1) =
      lineDerivWithin ℝ f O (passiveOriginalSourceProjection x) (Pi.single i 1) := by
  rw [lineDerivWithin_of_isOpen hD hx,lineDerivWithin_of_isOpen hO (hDO hx)]
  unfold lineDeriv
  congr 1
  funext t
  simp only [Function.comp_apply,map_add,map_smul,
    passiveOriginalSourceProjection_single_source]

theorem passiveOriginal_lineDeriv_parameter
    (f : (Fin n → ℝ) → ℝ) (D : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (x : Fin (n+d) → ℝ) (hx : x ∈ D) (i : Fin (n+d)) (hi : n ≤ i.val) :
    lineDerivWithin ℝ (f ∘ passiveOriginalSourceProjection (d := d)) D x
      (Pi.single i 1) = 0 := by
  rw [lineDerivWithin_of_isOpen hD hx]
  simp only [lineDeriv,Function.comp_apply,map_add,map_smul,
    passiveOriginalSourceProjection_single_parameter i hi,smul_zero,add_zero]
  exact deriv_const _ _

theorem passiveOriginal_partial_source
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (D : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalSourceProjection (d := d)) D O)
    (l : List (Fin n)) :
    EqOn (paperCoordinatePartial (l.map (Fin.castAdd d))
      (f ∘ passiveOriginalSourceProjection (d := d)) D)
      ((paperCoordinatePartial l f O) ∘ passiveOriginalSourceProjection (d := d)) D := by
  induction l with
  | nil => intro x _; rfl
  | cons i l ih =>
    intro x hx
    change lineDerivWithin ℝ _ D x _ = lineDerivWithin ℝ _ O _ _
    rw [lineDerivWithin_congr' ih hx]
    exact passiveOriginal_lineDeriv_source _ O hO D hD hDO x hx i

/-- Every word is an actual source word, or its literal passive partial is
zero. This includes raw coordinate functions with no differentiability
certificate and the zero-dimensional source. -/
theorem passiveOriginal_partial_word
    (f : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) (hO : IsOpen O)
    (D : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalSourceProjection (d := d)) D O)
    (l : List (Fin (n+d))) :
    (∃ l₀ : List (Fin n), l₀.map (Fin.castAdd d) = l) ∨
      EqOn (paperCoordinatePartial l (f ∘ passiveOriginalSourceProjection (d := d)) D)
        (fun _ => 0) D := by
  induction l with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons i l ih =>
    rcases ih with ⟨l₀,hl₀⟩ | hz
    · by_cases hi : i.val < n
      · left
        refine ⟨⟨i.val,hi⟩ :: l₀,?_⟩
        simp only [List.map_cons,hl₀]
        congr 1
      · right
        intro x hx
        change lineDerivWithin ℝ _ D x _ = 0
        rw [← hl₀]
        rw [lineDerivWithin_congr'
          (passiveOriginal_partial_source f O hO D hD hDO l₀) hx]
        exact passiveOriginal_lineDeriv_parameter _ D hD x hx i (Nat.le_of_not_gt hi)
    · right
      intro x hx
      change lineDerivWithin ℝ _ D x _ = 0
      rw [lineDerivWithin_congr' hz hx,lineDerivWithin_of_isOpen hD hx]
      exact deriv_const _ _

/-- Constant one in the original norm without a smoothness premise. Only
the actual open derivative domains and their actual sample maps are used. -/
theorem passiveOriginal_raw_paperCoordinateCj_le (j : ℕ)
    (f : (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ)) (hO : IsOpen O)
    (D T : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalSourceProjection (d := d)) D O)
    (hTD : T ⊆ D)
    (hTS : MapsTo (passiveOriginalSourceProjection (d := d)) T S) :
    paperCoordinateCj j (f ∘ passiveOriginalSourceProjection (d := d)) D T ≤
      paperCoordinateCj j f O S := by
  unfold paperCoordinateCj
  refine iSup_le fun l => iSup_le fun x => iSup_le fun c => ?_
  change ENNReal.ofReal ‖paperCoordinatePartial l.val
      ((fun y => f y c) ∘ passiveOriginalSourceProjection (d := d)) D x.val‖ ≤ _
  rcases passiveOriginal_partial_word (fun y => f y c) O hO D hD hDO l.val with
      ⟨l₀,hl₀⟩ | hz
  · have hp : l₀.Pairwise (· ≤ ·) :=
      List.Pairwise.of_map (Fin.castAdd d) (fun _ _ h => h) (hl₀.symm ▸ l.property.1)
    have hlen : l₀.length ≤ j := by
      simpa only [← hl₀,List.length_map] using l.property.2
    rw [← hl₀,passiveOriginal_partial_source (fun y => f y c) O hO D hD hDO l₀ (hTD x.property)]
    exact le_iSup_of_le ⟨l₀,hp,hlen⟩
      (le_iSup_of_le ⟨passiveOriginalSourceProjection x,hTS x.property⟩ (le_iSup_of_le c le_rfl))
  · rw [hz (hTD x.property)]
    simp only [norm_zero,ENNReal.ofReal_zero]
    exact bot_le

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_raw_paperCoordinateCj_le
