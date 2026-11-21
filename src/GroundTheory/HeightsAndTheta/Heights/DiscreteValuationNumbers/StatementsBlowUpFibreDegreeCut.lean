module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

def homLocRing (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime] : Subring (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) :=
  Subring.closure {z | ∃ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
    z = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P g)}

end Objects

section Lemmas

def HomLocRingLocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.isPrime
      IsLocalRing (homLocRing P W) ∧ IsNoetherianRing (homLocRing P W) ∧
        ringKrullDim (homLocRing P W) = 1

def DivCycleHomLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (hP : IsMultiProjPrime P) (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsMultiHomog x c → x ∉ P →
    ∀ (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes), IsRelevant W →
    ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsMultiHomog g c → g ∉ W →
      haveI := hP.isPrime
      ∀ hz : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      haveI : W.IsPrime := hW.1.1
      multAt (P ⊔ Ideal.span {x}) W =
        Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {(⟨_, hz⟩ : homLocRing P W)})

def FiniteBirationalLength.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Module.Finite A B], ringKrullDim A = 1 →
    Function.Injective (algebraMap A B) → Module.finrank A B = 1 → ∀ z : A, z ≠ 0 →
      Finite {𝔫 : Ideal B // 𝔫.IsMaximal} ∧
      Module.length A (A ⧸ Ideal.span {z}) =
        ∑ᶠ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
          (haveI := 𝔫.2.isPrime
           Module.length (Localization.AtPrime 𝔫.1)
             (Localization.AtPrime 𝔫.1 ⧸
               Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1) (algebraMap A B z)})) *
            (𝔫.1.inertiaDeg A : ℕ∞)

def BlowUpFibreSemilocal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
    ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsMultiHomog g c → g ∉ W →
      haveI := hP.multiProj.isPrime
      ∀ hz : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)) (Ideal.Quotient.mk P x) /
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)) (Ideal.Quotient.mk P g) ∈
            homLocRing P W,
      ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (homLocRing P W) B),
        Module.Finite (homLocRing P W) B ∧ Function.Injective (algebraMap (homLocRing P W) B) ∧
        Module.finrank (homLocRing P W) B = 1 ∧
        ∃ e : {𝔫 : Ideal B // 𝔫.IsMaximal} ≃ {W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) //
            W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
              W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
          ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
            (haveI := 𝔫.2.isPrime
             Module.length (Localization.AtPrime 𝔫.1)
               (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1)
                 (algebraMap (homLocRing P W) B ⟨_, hz⟩)})) =
              ((((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) (e 𝔫) : ℤ).1).toNat : ℕ∞) ∧
            𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
