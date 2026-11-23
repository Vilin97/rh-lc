module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ClauseAOfIdentityFlag
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LadjFrame
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LisoSmulMem
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LretrCancel

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LFrame

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem lframe_mem_locP {P : Ideal (𝓞 E)} [P.IsPrime] {M : Submodule (𝓞 E) S.V} {y : S.V} :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s : 𝓞 E, s ∉ P ∧ s • y ∈ M := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩

theorem lframe_local_global (M : Submodule (𝓞 E) S.V) (y : S.V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M) : y ∈ M := by
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) S.V y)
  have hI : ∀ s, s ∈ I ↔ s • y ∈ M := fun s => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  by_cases htop : I = ⊤
  · have h1 : (1 : 𝓞 E) ∈ I := by rw [htop]; trivial
    simpa using (hI 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I htop
    have hne : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
    obtain ⟨s, hs, hsy⟩ := h ⟨m, hm.isPrime, hne⟩
    exact absurd (hle ((hI s).2 hsy)) hs

theorem lframe_dual {r : ℕ} {T : E} (F : FlagG S r T) (a : Fin r) :
    ∃ φ : S.V →ₗ[E] E, ∀ b, φ (F.e b) = if b = a then 1 else 0 := by
  let B := Basis.span F.e_indep
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (B.coord a)
  refine ⟨φ, fun b => ?_⟩
  have h1 : F.e b = ((B b : Submodule.span E (Set.range F.e)) : S.V) := (congrArg Subtype.val (Basis.span_apply F.e_indep b)).symm
  have h2 : φ ((B b : Submodule.span E (Set.range F.e)) : S.V) = B.coord a (B b) := by
    rw [← hφ]
    rfl
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

end

theorem l_frame : UnitriangularFrameIntegral := by
  intro E _ _ _ S r T Λ g F F' hF hF' he U hU x hxΛ hxX
  have hXa := tie_Xa_eq F.fl F'.fl he
  have hX : F'.fl.X = F.fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  have hXL : XLam Λ F' = XLam Λ F := by
    unfold XLam
    rw [show Xsp F' = Xsp F from hX]
  apply lframe_local_global
  intro P
  have := P.isPrime
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨c, _, _, hc⟩ := hF.1 P
  obtain ⟨c', _, _, hc'⟩ := hF'.1 P
  have hA : ∀ a, c a • F'.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
    intro a
    have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
      rw [hXL, hc]
      exact lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hc'] at h1 ⊢
    obtain ⟨t, ht, h2⟩ := lframe_mem_locP.1 h1
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h2
    obtain ⟨φ, hφ⟩ := lframe_dual F'.fl a
    have hφ0 : ∀ w ∈ F'.fl.Xa a.val, φ w = 0 := by
      have hle : F'.fl.Xa a.val ≤ LinearMap.ker φ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        show φ (F'.fl.e i) = 0
        rw [hφ, if_neg]
        intro h
        subst h
        exact lt_irrefl i.val hi
      exact fun w hw => hle hw
    have hea : φ (F.fl.e a) = 1 := by
      have h3 : F.fl.e a = F'.fl.e a - (F'.fl.e a - F.fl.e a) := by abel
      rw [h3, map_sub, hφ, if_pos rfl, hφ0 _ (by rw [hXa]; exact he a), sub_zero]
    have key : algebraMap (𝓞 E) E t * c a = algebraMap (𝓞 E) E (o a) * c' a := by
      have h4 := congrArg φ ho

      simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, hφ, hea, smul_eq_mul, Algebra.smul_def, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h4
      exact h4.symm
    refine lframe_mem_locP.2 ⟨t, ht, ?_⟩
    have h5 : t • (c a • F'.fl.e a) = o a • (c' a • F'.fl.e a) := by
      rw [← algebraMap_smul E t, ← algebraMap_smul E (o a), smul_smul, smul_smul, key]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hx1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
    lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact ⟨hxΛ, hxX⟩⟩
  rw [hc] at hx1
  obtain ⟨s, hs, h3⟩ := lframe_mem_locP.1 hx1
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h3
  have hU1 : s • U x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by

    rw [← LinearMap.map_smul_of_tower, ← ho, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, map_smul, hU]
    exact Submodule.smul_mem _ _ (hA a)
  obtain ⟨t, ht, h4⟩ := lframe_mem_locP.1 hU1
  exact ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim ht hs, by rw [mul_smul]; exact h4.1⟩

end Formalism.MainNotions.BridgeLemma

end
end
end

-- Source module: Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem lift_sep {a b : S.V} (h : ∀ w, S.hT w a = S.hT w b) : a = b := by
  have hn := S.nondeg
  unfold LinearMap.Nondegenerate LinearMap.SeparatingRight at hn
  exact sub_eq_zero.mp (hn.2 (a - b) (fun w => by rw [map_sub, h w, sub_self]))

theorem lift_adj_symm {B B' : S.V →ₗ[E] S.V} (h : LAdj S B B') : LAdj S B' B := by
  intro x y
  rw [← S.herm.eq y (B' x), ← h y x]
  exact S.herm.eq (B y) x

theorem lift_exists_map {ι : Type} (e w : ι → S.V) (hli : LinearIndependent E e) :
    ∃ U : S.V →ₗ[E] S.V, ∀ a, U (e a) = w a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.linearCombination E w).comp hli.repr)
  refine ⟨g, fun a => ?_⟩
  have hmem : e a ∈ Submodule.span E (Set.range e) := Submodule.subset_span ⟨a, rfl⟩
  have h1 := LinearMap.congr_fun hg ⟨e a, hmem⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [h1, hli.repr_eq_single a ⟨e a, hmem⟩ rfl, Finsupp.linearCombination_single, one_smul]

variable {r : ℕ} {T : E}

theorem lift_gen (hA : IntegralAdjointUnimodular) (hI : IsotropicIntegralRetraction) (hF : UnitriangularFrameIntegral) (hcm : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F F' : LFlag S r T) (hlat : Submodule.IsLattice E Λ)
    (huni : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hconv : IsFixedConv Λ g F) (hconv' : IsFixedConv Λ g F')
    (he : ∀ a, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) :
    ∃ n ∈ NLam Λ F, ∀ a, n (F.fl.e a) = F'.fl.e a := by

  have hXiso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, S.hT x y = 0 := by
    have h1 : ∀ a, ∀ y ∈ Xsp F, S.hT (F.fl.e a) y = 0 := by
      intro a y hy
      replace hy : y ∈ Submodule.span E (Set.range F.fl.e) := hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨b, rfl⟩ := hz
        exact F.fl.e_iso a b
      | zero => simp
      | add z z' _ _ hz hz' => rw [map_add (f := _), hz, hz', add_zero]
      | smul c z _ hz => rw [map_smul, hz, smul_zero]
    intro x hx y hy
    replace hx : x ∈ Submodule.span E (Set.range F.fl.e) := hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      exact h1 a y hy
    | zero => simp
    | add z z' _ _ hz hz' => rw [map_add (f := _), LinearMap.add_apply, hz, hz', add_zero]
    | smul c z _ hz => rw [map_smulₛₗ, LinearMap.smul_apply, hz, smul_zero]
  have hXa_le : ∀ j, Xflag F j ≤ Xsp F := fun j => Submodule.span_mono (Set.image_subset_range _ _)
  have hX_le : Xsp F ≤ Xflag F r :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, i.isLt, rfl⟩)
  have hXa_mono : ∀ {i j : ℕ}, i ≤ j → Xflag F i ≤ Xflag F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun a (ha : a.1 < _) => lt_of_lt_of_le ha hij)
  have hXa0 : Xflag F 0 = ⊥ := by
    show Submodule.span E (F.fl.e '' {i | i.1 < 0}) = ⊥
    simp

  obtain ⟨U0, hU0⟩ := lift_exists_map F.fl.e F'.fl.e F.fl.e_indep
  have hU0X : ∀ j, ∀ x ∈ Xflag F j, U0 x - x ∈ Xflag F (j - 1) := by
    intro j x hx
    replace hx : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      rw [hU0]
      exact hXa_mono (by have : i.1 < j := hi; omega) (he i)
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add (f := _), add_sub_add_comm]
      exact Submodule.add_mem _ hz hz'
    | smul c z _ hz =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hz
  have hFU : ∀ x ∈ Λ, x ∈ Xsp F → U0 x ∈ Λ := hF E S r T Λ g F F' hconv hconv' he U0 hU0
  obtain ⟨P, P', hPP', hPX, hPr, hPi, hP'i, hP'iso⟩ := hI E S Λ (Xsp F) hcm hlat huni hXiso

  obtain ⟨N0, hN0⟩ : ∃ N0 : Module.End E S.V, N0 = (U0 - 1) * P := ⟨_, rfl⟩
  have hN0apply : ∀ x, N0 x = U0 (P x) - P x := fun x => by
    rw [hN0, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  have hN0X : ∀ x, N0 x ∈ Xsp F := fun x => by
    rw [hN0apply]
    exact hXa_le _ (hU0X r (P x) (hX_le (hPr x)))
  have hN0int : LInt Λ N0 := fun l hl => by
    rw [hN0apply]
    exact Submodule.sub_mem _ (hFU _ (hPi l hl) (hPr l)) (hPi l hl)
  have hN0onX : ∀ x ∈ Xsp F, N0 x = U0 x - x := fun x hx => by rw [hN0apply, hPX x hx]
  obtain ⟨N1, hN01, hN1int⟩ := hA E S Λ huni N0 hN0int
  have hN10 : LAdj S N1 N0 := lift_adj_symm hN01
  have hN1X : ∀ x ∈ Xsp F, N1 x = 0 := fun x hx => lift_sep fun w => by
    rw [← hN01 w x, hXiso _ (hN0X w) x hx, map_zero]
  have hN1orth : ∀ x ∈ orth S (Xsp F), N1 x = 0 := fun x hx => lift_sep fun w => by
    rw [← hN01 w x, map_zero]
    have h' : x ∈ LinearMap.ker (S.hT (N0 w)) := by
      simp only [orth, Submodule.mem_iInf] at hx
      exact hx _ (hN0X w)
    exact LinearMap.mem_ker.1 h'
  have hP'P : LAdj S P' P := lift_adj_symm hPP'
  have hPP'0 : ∀ w, P (P' w) = 0 := fun w => lift_sep fun z => by
    rw [← hP'P z (P' w), hP'iso, map_zero]
  have hPN1 : ∀ y, P (N1 y) = 0 := fun y => lift_sep fun w => by
    rw [← hP'P w (N1 y), ← hN01 (P' w) y, hN0apply, hPP'0]
    simp
  have hN0N1 : ∀ y, N0 (N1 y) = 0 := fun y => by rw [hN0apply, hPN1, map_zero, sub_zero]
  have hN0iso : ∀ a b, S.hT (N0 a) (N0 b) = 0 := fun a b => hXiso _ (hN0X a) _ (hN0X b)

  have hN0pow : ∀ k x, (N0 ^ (k + 1)) x ∈ Xflag F (r - k) := by
    intro k
    induction k with
    | zero => intro x; simpa using hX_le (hN0X x)
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply]
      have hy := ih x
      rw [hN0onX _ (hXa_le _ hy)]
      have := hU0X (r - k) _ hy
      rwa [show r - k - 1 = r - (k + 1) by omega] at this
  have hN0nil : N0 ^ (r + 1) = 0 := by
    ext x
    have := hN0pow r x
    rw [Nat.sub_self, hXa0, Submodule.mem_bot] at this
    simpa using this
  have hadjpow : ∀ k a b, S.hT ((N0 ^ k) a) b = S.hT a ((N1 ^ k) b) := by
    intro k
    induction k with
    | zero => intro a b; simp
    | succ k ih =>
      intro a b
      rw [pow_succ', Module.End.mul_apply, hN01, ih, pow_succ, Module.End.mul_apply]
  have hN1nil : N1 ^ (r + 1) = 0 := by
    ext y
    refine lift_sep fun w => ?_
    rw [← hadjpow, hN0nil]
    simp

  obtain ⟨S1, hS1⟩ : ∃ S1 : Module.End E S.V, S1 = ∑ k ∈ Finset.range (r + 1), (-N1) ^ k := ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0 : Module.End E S.V, S0 = ∑ k ∈ Finset.range (r + 1), (-N0) ^ k := ⟨_, rfl⟩
  have hS1l : (1 + N1) * S1 = 1 := by
    have := mul_neg_geom_sum (-N1) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1] at this
  have hS1r : S1 * (1 + N1) = 1 := by
    have := geom_sum_mul_neg (-N1) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN1nil, mul_zero, sub_zero, ← hS1] at this
  have hS0l : (1 + N0) * S0 = 1 := by
    have := mul_neg_geom_sum (-N0) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0] at this
  have hS0r : S0 * (1 + N0) = 1 := by
    have := geom_sum_mul_neg (-N0) (r + 1)
    rwa [sub_neg_eq_add, neg_pow, hN0nil, mul_zero, sub_zero, ← hS0] at this
  have hnn : ((1 + N0) * S1) * ((1 + N1) * S0) = 1 := by
    rw [mul_assoc, ← mul_assoc S1, hS1r, one_mul, hS0l]
  have hnn' : ((1 + N1) * S0) * ((1 + N0) * S1) = 1 := by
    rw [mul_assoc, ← mul_assoc S0, hS0r, one_mul, hS1l]

  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinearMap ((1 + N0) * S1) ((1 + N1) * S0) hnn hnn'
  have hS1fix : ∀ x, N1 x = 0 → S1 x = x := by
    intro x hx
    rw [hS1, LinearMap.sum_apply, Finset.sum_range_succ', pow_zero, Module.End.one_apply,
      Finset.sum_eq_zero fun k _ => by
        rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, hx, neg_zero, map_zero], zero_add]
  have hnfix : ∀ x, N1 x = 0 → n x = x + N0 x := by
    intro x hx
    show ((1 + N0) * S1) x = x + N0 x
    rw [Module.End.mul_apply, hS1fix x hx, LinearMap.add_apply, Module.End.one_apply]
  have hiso : n ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
    intro x y
    have hx : x = (1 + N1) (S1 x) := by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]
    have hy : y = (1 + N1) (S1 y) := by rw [← Module.End.mul_apply, hS1l, Module.End.one_apply]
    show S.hT (((1 + N0) * S1) x) (((1 + N0) * S1) y) = S.hT x y
    rw [Module.End.mul_apply, Module.End.mul_apply]
    conv_rhs => rw [hx, hy]
    generalize S1 x = s
    generalize S1 y = t
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add (f := _)]
    rw [hN0iso s t, hN01 s t, hN10 s t, ← hN01 (N1 s) t, hN0N1]
    simp only [map_zero, LinearMap.zero_apply, add_zero]
    ring

  have lint_pow : ∀ B : Module.End E S.V, LInt Λ B → ∀ k, LInt Λ (B ^ k) := by
    intro B hB k
    induction k with
    | zero => intro l hl; simpa using hl
    | succ k ih =>
      intro l hl
      rw [pow_succ', Module.End.mul_apply]
      exact hB _ (ih l hl)
  have lint_neg : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (-B) := fun B hB l hl => by
    rw [LinearMap.neg_apply]
    exact Submodule.neg_mem _ (hB l hl)
  have lint_sum : ∀ (f : ℕ → Module.End E S.V) (s : Finset ℕ), (∀ k ∈ s, LInt Λ (f k)) →
      LInt Λ (∑ k ∈ s, f k) := fun f s hf l hl => by
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun k hk => hf k hk l hl
  have lint_one_add : ∀ B : Module.End E S.V, LInt Λ B → LInt Λ (1 + B) := fun B hB l hl => by
    rw [LinearMap.add_apply, Module.End.one_apply]
    exact Submodule.add_mem _ hl (hB l hl)
  have lint_mul : ∀ B C : Module.End E S.V, LInt Λ B → LInt Λ C → LInt Λ (B * C) :=
    fun B C hB hC l hl => by
      rw [Module.End.mul_apply]
      exact hB _ (hC l hl)
  have hnint : LInt Λ ((1 + N0) * S1) := lint_mul _ _ (lint_one_add _ hN0int)
    (hS1 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN1int) k)
  have hninvint : LInt Λ ((1 + N1) * S0) := lint_mul _ _ (lint_one_add _ hN1int)
    (hS0 ▸ lint_sum _ _ fun k _ => lint_pow _ (lint_neg _ hN0int) k)
  have hgmap : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact hnint l hl
    · intro l hl
      refine ⟨((1 + N1) * S0) l, hninvint l hl, ?_⟩
      show ((1 + N0) * S1) (((1 + N1) * S0) l) = l
      rw [← Module.End.mul_apply, hnn, Module.End.one_apply]
  refine ⟨n, ⟨⟨hiso, hgmap⟩, ?_, ?_⟩, fun a => ?_⟩
  · intro j x hx
    have hxX : x ∈ Xsp F := hXa_le _ hx
    rw [hnfix x (hN1X x hxX), add_sub_cancel_left, hN0onX x hxX]
    simpa using hU0X (j + 1) x hx
  · intro x hx
    rw [hnfix x (hN1orth x hx), add_sub_cancel_left]
    exact hN0X x
  · have hx : F.fl.e a ∈ Xsp F := Submodule.subset_span ⟨a, rfl⟩
    rw [hnfix _ (hN1X _ hx), hN0onX _ hx, hU0]
    abel

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lift_of_steps (hA : IntegralAdjointUnimodular) (hI : IsotropicIntegralRetraction) (hF : UnitriangularFrameIntegral) (D : D7) : UnitriangularFrameLift D := by
  intro T Λ F F' hfix _ hconv' he _
  obtain ⟨hlat, huni, -, hconv⟩ := hfix
  exact lift_gen hA hI hF D.sp.cm.cmUnram Λ (gS D) F F' hlat huni hconv hconv' he

theorem id_lift (D : D7) : UnitriangularFrameLift D := by
  exact lift_of_steps l_adj (l_iso l_adj l_retr l_theta) l_frame D

end Formalism.MainNotions.BridgeLemma

end
end
end
