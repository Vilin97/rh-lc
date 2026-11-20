import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Chart

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

def chartMonomial [Fintype K] (u : ∀ k, ι k) (b : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι :=
  ∏ k, X ⟨k, u k⟩ ^ b k

def chartMap (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] (u : ∀ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι →ₐ[F] FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) :=
  aeval fun v => algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))

def chartIdeal (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] (u : ∀ k, ι k) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) :=
  RingHom.ker (chartMap P u)

instance chartIdeal.isPrime (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartIdeal P u).IsPrime :=
  RingHom.ker_isPrime _

end Chart

def MChartDehomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ P) →
    ∀ (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (b : K → ℕ), IsMultiHomog f b →
      chartMap P u f = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartHomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (u : ∀ k, ι k) (p : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), ∃ (b : K → ℕ) (h : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog h b ∧
      ∀ (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime], (∀ k, (X ⟨k, u k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ P) →
        chartMap P u p = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P h) /
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartTrdeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime], IsMultiHomogIdeal P →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ P) →
      Algebra.trdeg F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ chartIdeal P u) + Fintype.card K = Algebra.trdeg F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)

def MChartLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [P.IsPrime] [W.IsPrime], P ≤ W →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ W) →
      ringKrullDim (degZeroLoc P {W}) =
        ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).height

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
