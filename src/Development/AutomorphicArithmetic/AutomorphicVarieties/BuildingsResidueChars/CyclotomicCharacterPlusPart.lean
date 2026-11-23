module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterThird

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (algebraMap_isometry ℚ_[l] (PadicAlgCl l)).continuous
  have h3 : Continuous
      (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
        ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.Qbar l) :=
    h2.comp continuous_subtype_val
  exact (Continuous.units_map _ h3).comp h1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharacterPlusPart

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont F Ω l

private theorem mem_plus {F₀ F : Type} [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F]
    [IsTotallyReal F₀] (x : F₀) : algebraMap F₀ F x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  exact DFunLike.congr_fun
    (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F₀ F)))) x

theorem UpperTheory.cyclotomicCharacter_plusPart :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.CycConj → UpperTheory.V.Af.Sol.ToPolC := by
  intro hA hC F Ω _ _ _ _ _ _ l _ ι n r hpol
  obtain ⟨F₀, _, _, _, _, _, _, hR, μ, c, P, hμ, hs, ⟨j, hj⟩, hp⟩ := hpol
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  letI : Algebra F₀ (maximalRealSubfield F) :=
    ((algebraMap F₀ F).codRestrict (maximalRealSubfield F) mem_plus).toAlgebra
  haveI : IsScalarTower F₀ (maximalRealSubfield F) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply F₀ F Ω x
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hcyc : IsAlgChar ι (cycBar (maximalRealSubfield F) Ω l ^ ((n : ℤ) - 1)) := by
    refine (hA (maximalRealSubfield F) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, (n : ℤ) - 1, 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hres := (hA F₀ Ω l ι).2.2 (maximalRealSubfield F) μ hμ
  obtain ⟨χ, hc, art, a, h1, h2, h3⟩ := ((hA (maximalRealSubfield F) Ω l ι).2.1 _ _ hcyc hres).1
  refine ⟨_, χ, c', P, ⟨hc, art, a, h1, h2, h3⟩, fun d d' hd hd' => ?_, ⟨j, hj⟩, fun s s' hss => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply]
    rw [hC _ Ω l d hd, hC _ Ω l d' hd', hs (resG F₀ _ Ω d) (resG F₀ _ Ω d') hd hd']
  · rw [hp s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hss x)]
    congr 2
    change μ (resG F₀ F Ω s) = cycBar F Ω l s ^ (1 - (n : ℤ)) * (cycBar F Ω l s ^ ((n : ℤ) - 1) * μ (resG F₀ F Ω s))
    rw [← mul_assoc, ← zpow_add]
    simp
end
end
