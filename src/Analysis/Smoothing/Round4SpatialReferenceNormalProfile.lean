import Smoothing.Round4SpatialHostNormalProfile

/-! The fixed-reference reserve fractions used by the actual normal producer,
with a named scalar-cost function and exact finite-prefix dependence. -/
noncomputable section
namespace GlobalEmbedding.Continuation

def round4SpatialReferenceNormalProfile (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS0 TS0 BP0 TP0 Inverse Forward Given : ℕ → ℝ) (Ds Dp r : ℕ)
    (budget cF cT : ℝ) : ℕ → ℝ :=
  round4SpatialHostNormalProfile m d N radius hradius BS0 TS0 BP0 TP0 Inverse Forward Given
    Ds Dp r budget (cF/16) (cT/16) (1/4) (by norm_num)

theorem round4SpatialReferenceNormalProfile_congr_prefix
    (m d N : ℕ) (radius : ℝ) (hradius : 0 < radius) (Ds Dp r j : ℕ)
    (budget cF cT : ℝ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ I₁ I₂ F₁ F₂ G₁ G₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j+2, TP₁ a = TP₂ a)
    (hI : ∀ a ≤ j+2, I₁ a = I₂ a)
    (hF : ∀ a ≤ j+1, F₁ a = F₂ a) (hG : ∀ a ≤ j, G₁ a = G₂ a) :
    round4SpatialReferenceNormalProfile m d N radius hradius BS₁ TS₁ BP₁ TP₁ I₁ F₁ G₁
      Ds Dp r budget cF cT j =
    round4SpatialReferenceNormalProfile m d N radius hradius BS₂ TS₂ BP₂ TP₂ I₂ F₂ G₂
      Ds Dp r budget cF cT j := by
  exact round4SpatialHostNormalProfile_congr_prefix m d N radius hradius Ds Dp r j
    budget (cF/16) (cT/16) (1/4) (by norm_num) hBS hTS hBP hTP hI hF hG

#print axioms round4SpatialReferenceNormalProfile_congr_prefix
end GlobalEmbedding.Continuation
