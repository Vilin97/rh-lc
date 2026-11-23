module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterSecond

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G E Ω →* (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.G F Ω → (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous
      (((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l)).comp PadicInt.Coe.ringHom :
        ℤ_[l] →* UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) : ℤ_[l] → UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnDown

section

@[expose] public section




section
open UpperTheory.GalN.V UpperTheory.V.Af
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt := by
  intro hP K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r σ hσ hr hpair hirr hI hF hKp haut
  obtain ⟨P, hPr⟩ := hpair
  obtain ⟨j, hj⟩ := hσ
  have algClosure (F : Type) [Field F] [CharZero F] [Algebra F Ω] : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) F⟩
  have : IsAlgClosure K Ω := algClosure K
  have : IsAlgClosure L Ω := algClosure L
  have : IsAlgClosure (maximalRealSubfield K) Ω := algClosure (maximalRealSubfield K)
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : IsConjEl c := ⟨j, hj⟩
  have hpc : IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    have hcont : Continuous (cycBar (maximalRealSubfield K) Ω l) :=
      _root_.UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont _ Ω l
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ (hcont.zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hconj (a b : G (maximalRealSubfield K) Ω) (ha : IsConjEl a) (hb : IsConjEl b) :
      (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) a =
        (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) b := by
    have ha' : cycZ (maximalRealSubfield K) Ω l a = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := a.toRingEquiv) ha
    have hb' : cycZ (maximalRealSubfield K) Ω l b = -1 :=
      UpperTheory.V.IsConjOm.cyc (E := maximalRealSubfield K) (σ := b.toRingEquiv) hb
    simp only [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, ha', hb']
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt hP.toClassicalTheorems hn haut
  have hpol : Sol.Pol ι r := ⟨maximalRealSubfield K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, P, halg, hconj, hc, hpc⟩
  suffices h0 : AutCsd0 ι r from _root_.UpperTheory.GalN.V.mkCsd'_alt h0 fun hc' => _root_.UpperTheory.V.Z.Win.Dn.down'_alt L hP hsol hn hc' hirr hpol h0.c0 hF hI hKp
    (hN.2 (hc'.comp (continuous_restrictScalarsHom K L Ω)))
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP (maximalRealSubfield K) K Ω inferInstance l ι n hn r c P hc ?_ hpc
  refine (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP (maximalRealSubfield K) K L Ω hsol ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ (Or.inr inferInstance)
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg hconj ⟨c, P, hc, hpc⟩).2
    ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP L Ω l ι n _).2.2 haut)
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
end
end
end
