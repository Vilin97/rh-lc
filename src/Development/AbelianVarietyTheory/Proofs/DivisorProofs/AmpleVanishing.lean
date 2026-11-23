module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingLineBundleInvMixOneZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreVanishingLineBundleInvMixFixedDifferenceStatement
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points (PtsOver)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm (IsRegVar BottChern ArChow hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (om0)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.TorsionForm

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  {g D : ℕ}

section Global

variable {D' r : ℕ}



end Global

end GlobalTheory.TorsionForm

namespace GlobalTheory.Published

open GlobalTheory.TorsionForm MvPolynomial

def AmpleVanishing : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic A.hom A.hom L

end GlobalTheory.Published
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegree

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegreeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianVariety_cech_vanishing_above_degree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  first | exact @GlobalTheory.AmpleGen.not_NV_of_ge | exact GlobalTheory.AmpleGen.not_NV_of_ge | (intros; apply GlobalTheory.AmpleGen.not_NV_of_ge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCovers

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isRelAcyclic_of_not_NV : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left),
    (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  intro K _ A _ P hP U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    have hWU' : ⨆ i, W i = ⊤ := by rw [hWU]; simp
    by_contra h
    exact hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

end GlobalTheory.AmpleGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCoversStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left), (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  first | exact @GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | exact GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | (intros; apply GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.AmpleGen

namespace GlobalTheory.AmpleGen

theorem stepTwo {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h2 : (2 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (2 * a : ℕ) (2 * b : ℕ)) j₁ ∧
      NV A (mix A L (a + b : ℕ) (a + b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) = -2 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h2
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 1 1 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  simp only [t1, t0, neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem stepFive {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h5 : (5 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (4 * a + b : ℕ) (a + 4 * b : ℕ)) j₁ ∧
      NV A (mix A L (3 * a + 2 * b : ℕ) (2 * a + 3 * b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) = -5 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h5
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny K A hA 1 2 2 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  have t2 : tri 2 = 3 := by decide
  have t2' : tri (-2) = 1 := by decide
  simp only [t1, t0, t2, t2', neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem step {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (L : LB A.left) (hL : L.IsLB) (a b i : ℕ) (h : NV A (mix A L a b) i) :
    ∃ (i₁ i₂ a₁ b₁ a₂ b₂ : ℕ), i₁ + i₂ = 2 * i ∧ NV A (mix A L a₁ b₁) i₁ ∧ NV A (mix A L a₂ b₂) i₂ ∧
      a + b ≤ a₁ + b₁ ∧ 2 * (a + b) ≤ a₂ + b₂ ∧ ((a₂ : ℤ) - b₂ = (a : ℤ) - b ∨ (a₂ : ℤ) - b₂ = 0) := by
  by_cases h2 : (2 : K) = 0
  · have h5 : (5 : K) ≠ 0 := by
      have : (5 : K) = 2 * 2 + 1 := by norm_num
      rw [this, h2]; simp
    obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepFive A hA h5 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inl (by push_cast; ring)⟩
  · obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepTwo A hA h2 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inr (by push_cast; ring)⟩

theorem ampleVanishing : GlobalTheory.Published.AmpleVanishing := by
  intro K _ _ A _ hA L hL hamp
  refine GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers K A L fun j hj => ?_
  have h0 := GlobalTheory.T.cechNonvanishing_lineBundleInvMix_one_zero K A L hL _ hj
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_cech_vanishing_above_degree K A hA
  have hLB : ∀ a b : ℤ, (mix A L a b).IsLB := fun a b => LB.isLB_linComb hL _ _

  let S : ℕ → Prop := fun i => 1 ≤ i ∧ ∃ a b : ℕ, 1 ≤ a + b ∧ NV A (mix A L a b) i
  have hS : ∀ i, S i → i ≤ c := fun i ⟨_, a, b, _, h⟩ =>
    le_of_lt (not_le.1 fun hi => hc _ (hLB a b) i hi h)
  have hj1 : S (j + 1) := ⟨by omega, 1, 0, by omega, by exact_mod_cast h0⟩
  classical
  let T := Nat.findGreatest S c
  have hT : S T := Nat.findGreatest_spec (hS _ hj1) hj1
  have hmax : ∀ i, S i → i ≤ T := fun i hi => Nat.le_findGreatest (hS i hi) hi
  obtain ⟨hT1, a, b, hab, hTab⟩ := hT

  have next : ∀ a' b' : ℕ, 1 ≤ a' + b' → NV A (mix A L a' b') T → ∃ a₂ b₂ : ℕ,
      NV A (mix A L a₂ b₂) T ∧ 2 * (a' + b') ≤ a₂ + b₂ ∧
        ((a₂ : ℤ) - b₂ = (a' : ℤ) - b' ∨ (a₂ : ℤ) - b₂ = 0) := by
    intro a' b' h1 h
    obtain ⟨i₁, i₂, a₁, b₁, a₂, b₂, e, h₁, h₂, l₁, l₂, hd⟩ := step A hA L hL a' b' T h
    have u₁ : i₁ ≤ T := by
      rcases Nat.eq_zero_or_pos i₁ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₁, b₁, by omega, h₁⟩
    have u₂ : i₂ ≤ T := by
      rcases Nat.eq_zero_or_pos i₂ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₂, b₂, by omega, h₂⟩
    exact ⟨a₂, b₂, by rwa [show i₂ = T by omega] at h₂, l₂, hd⟩
  have grow : ∀ n : ℕ, ∃ a' b' : ℕ, 1 ≤ a' + b' ∧ n ≤ a' + b' ∧ NV A (mix A L a' b') T ∧
      ((a' : ℤ) - b' = (a : ℤ) - b ∨ (a' : ℤ) - b' = 0) := by
    intro n
    induction n with
    | zero => exact ⟨a, b, hab, by omega, hTab, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨a', b', h1, hn, h, hd⟩ := ih
      obtain ⟨a₂, b₂, h₂, l, hd₂⟩ := next a' b' h1 h
      refine ⟨a₂, b₂, by omega, by omega, h₂, ?_⟩
      rcases hd₂ with e | e
      · rw [e]; exact hd
      · exact Or.inr e
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp ((a : ℤ) - b)
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp 0
  obtain ⟨a', b', -, hn, h, hd⟩ := grow (N₁ + N₂)
  obtain ⟨t, ht⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  rw [ht] at h
  rcases hd with e | e
  · exact hN₁ a' b' (by omega) e t h
  · exact hN₂ a' b' (by omega) e t h

end GlobalTheory.AmpleGen
end
end
end
