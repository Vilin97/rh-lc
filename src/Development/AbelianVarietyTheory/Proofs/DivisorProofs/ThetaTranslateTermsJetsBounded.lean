module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyTermTranslateBoundFunctionalEquationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBallStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPointStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombination

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLin

theorem sp_dual_subsingleton (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem sE_comb : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  intro V _ _ D F _ _ k β s n a σF hs r J hJ hr
  have hW : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F β)
      (fun k' => J (redE F ≫ r ≫ DegPre.famφ D F β k')) := by
    intro y _
    haveI := sp_dual_subsingleton F
    let z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
    have hy : y = (redE F).base z := Subsingleton.elim _ _
    refine Set.mem_iInter.2 fun k' => ?_
    have := hJ (redE F ≫ r ≫ DegPre.famφ D F β k') (Set.mem_univ z)
    subst hy
    simpa using this
  unfold sE
  refine (congrArg (valR r _) (hs _)).trans ((GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)))
  congr 1
  · refine (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm.trans ?_
    rw [← TrivSqZeroExt.algebraMap_eq_inl]
    exact GlobalTheory.ZH.FormCount.valR_scal (algebraMap F (DualNumber F)) r _ hr _ hW (a i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm

end GlobalTheory.DualLin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombinationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dualNumberSectionValue_linearCombination : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  first | exact @GlobalTheory.DualLin.sE_comb | exact GlobalTheory.DualLin.sE_comb | (intros; apply GlobalTheory.DualLin.sE_comb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trF_dualPoint_of_isPull : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  intro V _ _ D C _ _ gm₀ gm hp mu
  have hsq : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    simp only [epsR, TE, TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hsq
  have hb : gm.b = k ≫ gm₀.b := by
    ext1
    simpa [k] using hp.1
  set e : TE V C ⟶ TF (R := V) C := Over.homMk (spMap (algebraMap C (DualNumber C))) rfl with he
  refine ⟨?_, Over.w _, ?_⟩
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ DegPre.prB D C = k ≫ padd D.P.A gm₀.b (toUnit _ ≫ D.c mu) := by
      simp only [DegPre.trF, DegPre.prB, lift_snd, padd, comp_lift_assoc, comp_lift, hb, Category.assoc, comp_toUnit_assoc]
    have h2 := congrArg CommaMorphism.left h1
    simpa [k] using h2
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ fst _ _ = e := by
      simp [DegPre.trF]
    have h2 := congrArg CommaMorphism.left h1
    simpa [he] using h2

end GlobalTheory.MBLow

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trVal_bounded : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν k hk s gm₀ gm _ hpull α
  obtain ⟨S, hS, hint⟩ := hν
  obtain ⟨n, a, σ, σF, hsc, hsum⟩ := GlobalTheory.T.familySection_span_pullbacks_unitBall V D C hC S hS k hk (ν.eX α) (s.s (ν.eX α))
  refine ⟨∑ i, ‖a i‖, fun mu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint V D.toPre C gm₀ gm hpull (ν.eX mu)
  have e := GlobalTheory.T.dualNumberSectionValue_linearCombination V D.toPre C k (ν.eX α) (s.s (ν.eX α)) n a σF hsum _ ν.J ν.good h3
  have hb := fun i => GlobalTheory.T.pulledBackSection_integralValue_dualPoint V D C hC N ν ⟨S, hS, hint⟩ k _ (σ i) (σF i) (hsc i) _ h2 _ h1
  have hv : trVal ν s gm α mu = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i)
      ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫
        (DegPre.trF D.toPre C (ν.eX mu)).left) ν.J := e
  rw [hv]
  constructor
  · rw [TrivSqZeroExt.fst_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).1
  · rw [TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).2

end GlobalTheory.MBLow

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translate_section_values_bounded_integral_tangent : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  exact @GlobalTheory.MBLow.trVal_bounded
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBounded

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem jc_bound_k (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V))
    (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C]
    (hC : CExt V (IsLocalRing.maximalIdeal V) C) (N : NumD C) (ν : NumOf D.toPre C N) (hν : ν.IntN)
    (q : QuadraticMap ℤ N.X ℝ) (hq : N.Int q) (k : ℕ) (hk1 : 1 ≤ k) (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V))
    (gm : GtPt D.toPre (TE V C)) (htan : GtTan gm₀) (hpull : GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm) :
    ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) ∧
      ‖(jc ν s gm α).snd / ν.rg ^ k‖ ≤ b * Real.exp (-(q α / (k : ℝ))) := by
  have H1 := GlobalTheory.T.familyTerm_translate_bound_functionalEquation V D C hC N ν hν q hq k hk1 s gm₀ gm htan hpull
  have H2 := GlobalTheory.T.translate_section_values_bounded_integral_tangent V D C hC N ν hν k hk1 s gm₀ gm htan hpull
  choose bb hbb using H2
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  let bs := Module.Free.chooseBasis ℤ N.X
  let g : (Module.Free.ChooseBasisIndex ℤ N.X → Fin k) → N.X := fun c => ∑ i, ((c i : ℕ) : ℤ) • bs i
  let quo : N.X → N.X := fun χ => ∑ i, (bs.repr χ i / (k : ℤ)) • bs i
  let cOf : N.X → Module.Free.ChooseBasisIndex ℤ N.X → Fin k := fun χ i =>
    ⟨(bs.repr χ i % (k : ℤ)).toNat, by
      have h1 := Int.emod_nonneg (bs.repr χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (bs.repr χ i) hk0
      omega⟩
  have hdec : ∀ χ, χ = g (cOf χ) + k • quo χ := by
    intro χ
    have e1 : ∀ i, (((cOf χ i : ℕ) : ℤ)) = bs.repr χ i % (k : ℤ) := fun i =>
      Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')
    have e2 : k • quo χ = ∑ i, ((k : ℤ) * (bs.repr χ i / (k : ℤ))) • bs i := by
      rw [← natCast_zsmul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    rw [e2]
    simp only [g, e1, ← Finset.sum_add_distrib, ← add_smul]
    conv_lhs => rw [← bs.sum_repr χ]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have := Int.mul_ediv_add_emod (bs.repr χ i) (k : ℤ)
    linarith
  have hqk : ∀ a mu : N.X, q (a + k • mu) = q a + (k : ℝ) ^ 2 * q mu + (k : ℝ) * QuadraticMap.polar q mu a := by
    intro a mu
    have e1 : q (k • mu + a) = q (k • mu) + q a + QuadraticMap.polar q (k • mu) a := by
      simp only [QuadraticMap.polar]; ring
    have e2 : q (k • mu) = ((k : ℤ) * (k : ℤ)) • q mu := by
      rw [← natCast_zsmul]; exact QuadraticMap.map_smul q _ _
    have e3 : QuadraticMap.polar q (k • mu) a = (k : ℤ) • QuadraticMap.polar q mu a := by
      rw [← natCast_zsmul]; exact QuadraticMap.polar_smul_left q _ _ _
    rw [add_comm, e1, e2, e3, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  have hexp : ∀ a mu : N.X, Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu a)) =
      Real.exp (q a / k) * Real.exp (-(q (a + k • mu) / k)) := by
    intro a mu
    rw [← Real.exp_add, hqk]
    congr 1
    field_simp
    ring
  let B : ℝ := ∑ c, max 0 (bb (g c) * Real.exp (q (g c) / k))
  have hB : ∀ c, bb (g c) * Real.exp (q (g c) / k) ≤ B := fun c =>
    (le_max_right _ _).trans (Finset.single_le_sum (f := fun c => max 0 (bb (g c) * Real.exp (q (g c) / k)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ c))
  refine ⟨‖ν.rg ^ k‖⁻¹ * B, fun α => ?_⟩
  have hα := hdec α
  obtain ⟨h1, h2⟩ := H1 (g (cOf α)) (quo α)
  obtain ⟨h3, h4⟩ := hbb (g (cOf α)) (quo α)
  have hE := hexp (g (cOf α)) (quo α)
  rw [← hα] at h1 h2 hE
  have key : ∀ x : ℝ, x ≤ Real.exp (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α)))) * bb (g (cOf α)) →
      x ≤ B * Real.exp (-(q α / k)) := by
    intro x hx
    refine hx.trans ?_
    rw [hE]
    calc Real.exp (q (g (cOf α)) / k) * Real.exp (-(q α / k)) * bb (g (cOf α)) =
        (bb (g (cOf α)) * Real.exp (q (g (cOf α)) / k)) * Real.exp (-(q α / k)) := by ring
      _ ≤ B * Real.exp (-(q α / k)) := mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  have hE0 := Real.exp_pos (-((k : ℝ) * q (quo α) + QuadraticMap.polar q (quo α) (g (cOf α))))
  have hr0 : 0 ≤ ‖ν.rg ^ k‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  constructor
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h1.trans (mul_le_mul_of_nonneg_left h3 hE0.le))) hr0
  · rw [norm_div, div_eq_mul_inv, mul_comm, _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left (key _ (h2.trans (mul_le_mul_of_nonneg_left (max_le h3 h4) hE0.le))) hr0

theorem jc_bound : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), ν.FamV s f → IsEvFam N m p f → ∀ (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∃ b : ℝ, ∀ α, ‖(jc ν s gm α).fst / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) ∧ ‖(jc ν s gm α).snd / ν.rg ^ (m ^ 2)‖ ≤ b * Real.exp (-(q α / (m : ℝ) ^ 2)) := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν q hq m hm p s f hf hev gm₀ gm htan hpull
  have hk1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨b, hb⟩ := jc_bound_k V D C hC N ν hν q hq (m ^ 2) hk1 s gm₀ gm htan hpull
  refine ⟨b, fun α => ?_⟩
  have hcast : (((m ^ 2 : ℕ) : ℝ)) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [← hcast]
  exact hb α

end GlobalTheory.MBLow

end
end
end
