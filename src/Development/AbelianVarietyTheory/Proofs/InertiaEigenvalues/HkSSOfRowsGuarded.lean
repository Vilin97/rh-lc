module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCompSmul
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPart

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.HkGoodStable

theorem hkF_mem_V0 : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  intro D hC i hi j hj b k P hk x hx
  have hc : ∀ g z, D.nexp.actG i j b g (D.nexp.hkF i j b k P z) = D.nexp.hkF i j b k P (D.nexp.actG i j b g z) :=
    fun g z => LinearMap.congr_fun (hC i hi b j hj g k P hk) z
  have hcomm : ∀ a, Commute (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
      (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) a) (D.nexp.hkF i j b k P) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.lift_of]
      exact LinearMap.ext fun z => hc g z
    | add a a' ha ha' => rw [map_add (f := _)]; exact ha.add_left ha'
    | smul c a ha => rw [map_smul]; exact ha.smul_left c
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨D.nexp.hkF i j b k P y, ?_, ?_⟩
  · simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe] at hy ⊢
    intro u
    have h := hy u
    rw [sub_eq_zero] at h ⊢
    rw [hc, h, map_smul]
  · exact LinearMap.congr_fun (hcomm (D.nexp.eAlg i b)) y

end GlobalTheory.HkGoodStable
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hecke_preserves_good_part : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  first | exact @GlobalTheory.HkGoodStable.hkF_mem_V0 | exact GlobalTheory.HkGoodStable.hkF_mem_V0 | (intros; apply GlobalTheory.HkGoodStable.hkF_mem_V0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpan

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory

theorem charpoly_split_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  intro O V B _ _ _ _ _ _ _ _ _ _ _ e t T he hs
  refine ⟨(LinearMap.charpoly t).map (algebraMap O (FractionRing O)), ?_, hs, ?_⟩
  · exact ((LinearMap.charpoly_monic t).map _).ne_zero
  · have hpow : ∀ (n : ℕ) (b : B), (T ^ n) (e b) = e ((t ^ n) b) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih => intro b; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← he, ih]
    have key : ∀ (q : O[X]) (b : B), Polynomial.aeval T (q.map (algebraMap O (FractionRing O))) (e b) = e (Polynomial.aeval t q b) := by
      intro q b
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq]
      | monomial n a =>
          simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, LinearMap.map_smul_of_tower]
          rw [algebraMap_smul]
    have hle : Submodule.span (FractionRing O) (Set.range e) ≤ LinearMap.ker (Polynomial.aeval T ((LinearMap.charpoly t).map (algebraMap O (FractionRing O)))) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, key, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero]
    intro x hx
    exact hle hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpanStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

theorem _root_.GlobalTheory.T.split_charpoly_lattice_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  first | exact @GlobalTheory.charpoly_split_kills_span | exact GlobalTheory.charpoly_split_kills_span | (intros; apply GlobalTheory.charpoly_split_kills_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfRowsGuarded

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSpan

theorem hkSS_of_rows_guarded {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y)
    (hG : CommG D) (hC : HkComm D) (hSF : SupFull D)
    (X : NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0))
    (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i)
    (hEmb : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x,
      D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x))
    (hBr : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
      D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i))
    (hSp : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits) :
    HkSS D := by
  intro i hi j hj b
  have := D.nexp.towFm i j b

  have hspan : ∀ x ∈ V0 D.nexp i j b,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (Set.range (D.nexp.embB i j b)) := by
    intro x hx
    have hx' : x ∈ Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i j b : Set (D.nexp.Fm i j b)) := by
      rw [(hSF i hi j hj b).2]; exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (D.ntw.O i))).1 hx'
    rw [Submodule.span_eq] at hy
    have hyV : y ∈ V0 D.nexp i j b := by
      have e : y = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (z : D.ntw.O i)) •
          (IsLocalization.mk' (FractionRing (D.ntw.O i)) (1 : D.ntw.O i) z • y) := by
        rw [smul_smul, mul_comm, IsLocalization.mk'_spec, map_one, one_smul]
      rw [e]; exact Submodule.smul_mem _ _ hx
    have hyR : y ∈ LinearMap.range (D.nexp.embB i j b) := by
      rw [hBr i hi j hj b]
      exact Submodule.mem_inf.2 ⟨hy, (Submodule.restrictScalars_mem _ _ _).2 hyV⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.1 hyR))

  have hpoly : ∀ k P, HkIdx i k P → ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧ p.Splits ∧
      ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
    intro k P hkP
    obtain ⟨p1, hp10, hp1s, hp1k⟩ := GlobalTheory.T.split_charpoly_lattice_kills_span (D.ntw.O i) (D.nexp.Fm i j b) (D.ntw.B i j b)
      (D.nexp.embB i j b) (D.ntw.hk i j b k P) (D.nexp.hkF i j b k P) (hEmb i hi j hj b k P hkP)
      (hSp i hi j hj b k P hkP)
    obtain ⟨p2, hp2s, hp2k⟩ :=
      GlobalTheory.GoodSS.hkF_separable Rl F cG S Y H hG hC X hR hU hI hS0c hS02 hS0b i hi j hj b k P hkP
    classical
    refine ⟨EuclideanDomain.gcd p1 p2, hp2s.of_dvd (EuclideanDomain.gcd_dvd_right _ _),
      hp1s.of_dvd hp10 (EuclideanDomain.gcd_dvd_left _ _), ?_⟩
    intro x hx
    rw [EuclideanDomain.gcd_eq_gcd_ab, mul_comm p1, mul_comm p2, map_add (f := _), map_mul, map_mul,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hp1k x (hspan x hx), hp2k x hx,
      map_zero, map_zero, add_zero]

  have hJ := GlobalTheory.JointDiag.le_iSup_jointEigenspace_inf (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) {a : ℕ × PlE D.host // HkIdx i a.1 a.2}
    (fun a => D.nexp.hkF i j b a.1.1 a.1.2) (V0 D.nexp i j b)
    (fun a c => hC i hi j hj b _ _ _ _ a.2 c.2)
    (fun a x hx => GlobalTheory.T.hecke_preserves_good_part D hG i hi j hj b _ _ a.2 x hx)
    (fun a => hpoly _ _ a.2)
  refine hJ.trans (iSup_le fun ev => ?_)
  classical
  refine le_iSup_of_le (fun k P => if h : HkIdx i k P then ev ⟨(k, P), h⟩ else 0) (inf_le_inf_right _ ?_)
  unfold Eigsp
  refine le_iInf fun k => le_iInf fun P => le_iInf fun h => ?_
  refine (iInf_le _ ⟨(k, P), h⟩).trans ?_
  simp only [dif_pos h]
  exact le_rfl

end GlobalTheory.GoodSpan
end
end
end
