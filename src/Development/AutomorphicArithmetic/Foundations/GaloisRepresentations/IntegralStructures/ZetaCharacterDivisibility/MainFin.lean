module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.DivisionOneGeometricRepresentation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGapLac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSameOr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.InsideRefl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PTyConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.SeedFinOddOf

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCplMem

section

@[expose] public section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.Int.Div

theorem cplMem_of : CplMem := by
  intro E _ _ _ w y y' hy
  exact (GlobalTheory.Mem.Chr.conjPl_iff_mem (GlobalTheory.SplitPts.conjE E) (cpl w) w).1
    (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w) y y' hy

end UpperTheory.Gal.Int.Div
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PGenMul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDGenMul

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSatConj

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.satConj_of :
    LocIso → SatConj := by
  intro hL E _ _ _ a U hU w hw ⟨B, σ, ⟨hirr, f, hf0, hfU, hfe⟩, hB⟩
  obtain ⟨hloc, β, hβ, hK, -⟩ := hL E a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hpe : ∀ g, cLoc w ((e.symm g : locU a w) : UA E a) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hker : LinearMap.ker f = ⊥ := ((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 hirr).2 _ (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 := hfe (e.symm g) v
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
    rw [h1, hv, map_zero]) |>.resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have h0 : f x ≠ 0 := (map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hker)).2 hx.1
  obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hw
  have hs : IsSplitAt (cpl w) := ⟨w, hne.symm, hund.symm⟩
  have hfix : ∀ y ∈ locU a (cpl w), cLoc (cpl w) y ∈ GlobalTheory.LFun.KGL (cpl w) (n := a) → RU E a y (f x) = f x := by
    intro y hy hk
    have hy' : y ∈ locU a w := hloc ▸ hy
    have hk' : cLoc w y ∈ GlobalTheory.LFun.KGL w (n := a) := by
      rw [← hβ y]
      exact hK _ hk
    have h2 := GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ hk'
    have h1 := hfe ⟨y, hy'⟩ x
    change f (σ.ρ (cLoc w y) x) = RU E a y (f x) at h1
    rw [h2] at h1
    exact h1.symm
  obtain ⟨σ', S, hc, hS, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU (cpl w) hs (f x) (hfU x) h0 hfix
  exact ⟨S, σ', hc, hS⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.MainFin

section

@[expose] public section

namespace UpperTheory.Gal.Int.Div

theorem seedFinOdd_of_geoOne (h : UpperTheory.Gal.Int.Geo.GeoOne) : GlobalTheory.CongL.SeedFinOdd :=
  seedFinOdd_of divAll_holds cplMem_of (sameOr_of cplMem_of) (satConj_of locIso_of) (tyConj_of locIso_of) (lacConj_of cplMem_of)
    gapLac_of dGenMul_of h

end UpperTheory.Gal.Int.Div
end
end
