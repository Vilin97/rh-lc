import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem CommonFactorInduction.proof (hpos : ExcessPositive.Statement.{u}) (havoid : AvoidingFormExists.Statement.{u})
    (hhor : HorizontalAvoidingForm.Statement.{u}) (hpieces : BlowUpDecomposition.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hred : BlowUpReduction.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hmul : DivCycleMul.Statement.{u}) : CommonFactorInduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH hcommon IH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hε := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  obtain ⟨e, h, hh, hhP, hle, hhH, hhG, hh0, hmulε⟩ :=
    havoid O ϖ hϖ K ι P d hP b f g hD (fun k => (b k).toNat)
  have hdiv : ∀ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (s * h)) W : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ) + ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P h) W : ℤ) := fun W => by
    rw [hmul O K ι P s h hPp hsP hhP]; rfl
  have hshP : s * h ∉ P := fun hm => (hPp.mem_or_mem hm).elim hsP hhP
  have hshH : ∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (s * h)) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g := by
    intro H hH hϖH
    rw [hdiv] at hH
    by_cases h1 : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) = 0
    · exact hhH H (by rwa [h1, zero_add] at hH) hϖH
    · exact hsH H h1 hϖH
  have hcommon' : ∃ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G ∧ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (s * h)) G : ℤ) ≠ 0 ∧ ratDiv P f g G ≠ 0 := by
    obtain ⟨G, hG, hsG, hDG⟩ := hcommon
    exact ⟨G, hG, by rwa [hdiv, hhG G hG hDG, add_zero], hDG⟩

  set e₂ : K → ℕ := fun k => (((c + e) k : ℕ) - b k : ℤ).toNat with he₂def
  have he₂ : ∀ k, (((c + e) k : ℕ) : ℤ) = b k + e₂ k := by
    intro k
    have h1 : (b k).toNat ≤ e k := hle k
    have h2 : b k ≤ ((b k).toNat : ℤ) := Int.self_le_toNat (b k)
    simp only [he₂def, Pi.add_apply, Nat.cast_add]
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  obtain ⟨m, hm, hmP, hmH⟩ := hhor O ϖ hϖ K ι P d hP (s * h) hshP e₂
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, hH₀⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD (c + e)
    (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm hmP hmH
  obtain ⟨hdrop₁, hdrop₀⟩ := hdrop O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP
    hshH e₂ he₂ m hm hmP hmH hcommon'
  rw [hmulε s hsP] at hdrop₁ hdrop₀

  have hId₁ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hD₁ _ _ hsl hslP
    (fun H hH hϖH => (hH₁ H hH hϖH).1) hdrop₁ (liftDegs L)
  have hId₀ := IH (Option K) (extIdx ι (BlowUpIdx ι)) _ d hmodel _ _ _ hE (Pi.single none 1)
    (newVar none) (isWeightedHomogeneous_X _ _ _) hY₀P hH₀ hdrop₀ (liftDegs L)

  have hIdsh := hred O ϖ hϖ K ι P d hP b f g hD (c + e) (s * h) (hs.mul hh) hshP hshH e₂ he₂ m hm
    hmP hmH L hId₁ hId₀
  have hIdh := IH K ι P d hP b f g hD e h hh hhP hhH (by rw [hh0]; exact hε) L

  rw [cutIdentity_iff] at hIdsh hIdh ⊢
  have h1 := hlhs O ϖ hϖ K ι P d hP b f g hD.1 c e L
  have h2 := hrhs O ϖ hϖ K ι P d hP b f g s h hsP hhP L
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
