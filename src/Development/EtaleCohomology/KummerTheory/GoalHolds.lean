module

public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.FinAdicDeg
public import Development.EtaleCohomology.KummerTheory.FinBock
public import Development.EtaleCohomology.KummerTheory.LimitPf
public import Development.EtaleCohomology.KummerTheory.LimAssemblePf
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
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Development.EtaleCohomology.KummerTheory.FinSHInv
public import Development.EtaleCohomology.KummerTheory.FinStalk
public import Development.EtaleCohomology.KummerTheory.LocalHomotopyEtaleCohomology

-- Source module: Development.EtaleCohomology.KummerTheory.LimExtHlPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem lex_red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (Ht.cast hn hi x) = Ht.cast hn hi (red Q q E n i x) := by
  subst hn hi; rfl

theorem lex_cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    Ht.cast hn hi (x + y) = Ht.cast hn hi x + Ht.cast hn hi y := by
  subst hn hi; rfl

theorem lex_cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    Ht.cast hn hi (m • x) = m • Ht.cast hn hi x := by
  subst hn hi; rfl

theorem lex_ext_red (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (a n i : ℤ) (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold ext
  rw [lex_red_cast, (hA Q q hq _).1, pull_red, pull_red]

theorem lex_ext_add_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x x' : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (x + x') y = ext q pX pY a n i x y + ext q pX pY a n i x' y := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, lex_cast_add]

theorem lex_ext_add_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht q (sch.obj X) a i) (y y' : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), lex_cast_add]

theorem lex_ext_nsmul_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (m • x) y = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, lex_cast_nsmul]

theorem lex_ext_nsmul_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, lex_cast_nsmul]

def lexF (hA : A11) (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0) : Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => ext (l ^ k) pX pY a n i (lev l x k) (lev l y k), fun k => by
    have : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change red (l ^ (k + 1)) (l ^ k) _ n i (ext (l ^ (k + 1)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))) =
      ext (l ^ k) pX pY a n i (x.1 k) (y.1 k)
    exact (lex_ext_red hA _ _ (pow_dvd_pow l (Nat.le_succ k)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))).trans
      (congrArg₂ _ (x.2 k) (y.2 k))⟩

theorem LimExtHl_of : LimExtHl := by
  intro hA l _ X Y S pX pY a n i
  refine ⟨LinearMap.mk₂ ℤ_[l] (lexF hA l pX pY a n i) ?_ ?_ ?_ ?_, fun x y k => ?_⟩
  · intro x x' y
    apply Subtype.ext; funext k
    exact lex_ext_add_left (l ^ k) pX pY a n i (x.1 k) (x'.1 k) (y.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i ((r • x).1 k) (y.1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_left (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · intro x y y'
    apply Subtype.ext; funext k
    exact lex_ext_add_right (l ^ k) pX pY a n i (x.1 k) (y.1 k) (y'.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i (x.1 k) ((r • y).1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_right (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · rfl

end LateralTheory.KummerTheory
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.LimLHPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LimLHPf

theorem cast_add' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by subst hn; subst hi; rfl

theorem cast_nsmul' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    (m • x).cast hn hi = m • x.cast hn hi := by subst hn; subst hi; rfl

theorem red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (x.cast hn hi) = (red Q q E n i x).cast hn hi := by subst hn; subst hi; rfl

theorem ext_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y y' : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold LateralTheory.KummerTheory.ext; rw [map_add (f := _), map_add (f := _), cast_add']

theorem ext_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (m : ℕ) (y : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold LateralTheory.KummerTheory.ext; rw [map_nsmul, map_nsmul, cast_nsmul']

theorem red_ext (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold LateralTheory.KummerTheory.ext
  rw [red_cast, (hA Q q hq _).1, ← pull_red, ← pull_red]

theorem lh_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y y' : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (y + y') = lh q pX pY i r c M n y + lh q pX pY i r c M n y' := by
  unfold LateralTheory.KummerTheory.lh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_add _ _ _ _ _ _ _ _ _

theorem lh_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) (m : ℕ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (m • y) = m • lh q pX pY i r c M n y := by
  unfold LateralTheory.KummerTheory.lh
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_nsmul _ _ _ _ _ _ _ _ _

theorem red_lh (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht Q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht Q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    red Q q _ n i (lh Q pX pY i r c M n y) =
      lh q pX pY i r (fun a s => red Q q _ a i (c a s)) M n (fun a s => red Q q _ _ 0 (y a s)) := by
  unfold LateralTheory.KummerTheory.lh

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact red_ext hA Q q hq _ _ _ _ _ _ _

theorem lev_red (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) E n i (lev l x (k + 1)) = lev l x k := x.2 k

instance nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem dvd_succ (l k : ℕ) : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)

variable {l : ℕ} [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i)

def phiFun (hA : A11) (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k), fun k => by
    change red (l ^ (k + 1)) (l ^ k) _ n i (lh (l ^ (k + 1)) pX pY i r (fun a s => lev l (c a s) (k + 1)) M n
      (fun a s => lev l (y a s) (k + 1))) = _
    rw [red_lh hA _ _ (dvd_succ l k)]
    simp only [lev_red]⟩

def phi (hA : A11) : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
    Hl l (sch.obj (pullback pX pY)) n i where
  toFun := phiFun pX pY n i M r c hA
  map_add' y y' := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k + lev l (y' a s) k) =
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) +
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y' a s) k)
    rw [← lh_add]; rfl)
  map_smul' t y := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => (t • (show HtL l k _ _ _ from lev l (y a s) k))) =
      (t • (show HtL l k _ _ _ from lev l (phiFun pX pY n i M r c hA y) k))
    have h1 : (fun (a : Fin (M + 1)) (s : Fin (r a)) =>
        (t • (show HtL l k (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0 from lev l (y a s) k) : Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)) =
        (PadicInt.toZModPow k t).val • (fun (a : Fin (M + 1)) (s : Fin (r a)) => lev l (y a s) k) :=
      funext fun a => funext fun s => HtL.smul_eq l k k le_rfl _ _ _ t _
    rw [h1, lh_nsmul]
    exact (HtL.smul_eq l k k le_rfl _ _ _ t _).symm)

theorem phi_ker (hA : A11) (N : ℕ)
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
    (hy : phi pX pY n i M r c hA y = 0) : N • y = 0 := by
  funext a s
  apply Subtype.ext; funext k
  have h0 : lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) = 0 := by
    have := congrArg (fun z : Hl l (sch.obj (pullback pX pY)) n i => lev l z k) hy
    exact this
  have := congrFun (congrFun ((hiso k).1 _ h0) a) s
  exact this

theorem phi_coker (hA : A11) (N : ℕ)
    (hfin : ∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0))
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (b : Hl l (sch.obj (pullback pX pY)) n i) : ∃ y, phi pX pY n i M r c hA y = N • b := by
  let D : ℕ → Type 1 := fun k => ∀ a : Fin (M + 1), Fin (r a) → Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0
  let Sl : ℕ → Type 1 := fun k => {z : D k // lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n z = N • lev l b k}
  let f : ∀ k, Sl (k + 1) ⟶ Sl k := fun k => TypeCat.ofHom fun (z : Sl (k + 1)) => (⟨fun a s => red (l ^ (k + 1)) (l ^ k) _ _ 0 (z.1 a s), by
    have h := congrArg (red (l ^ (k + 1)) (l ^ k) _ n i) z.2
    rw [red_lh hA _ _ (dvd_succ l k), map_nsmul, lev_red] at h
    simp only [lev_red] at h
    exact h⟩ : Sl k)
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence f
  have : ∀ j, Finite (F.obj j) := fun j => by
    have := hfin (unop j)
    change Finite (Sl (unop j))
    have : ∀ (a : Fin (M + 1)), Finite (Fin (r a) → Ht (l ^ unop j) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :=
      fun a => by have := hfin (unop j) (n - ((a : ℕ) : ℤ)); infer_instance
    have : Finite (D (unop j)) := Pi.finite
    exact Subtype.finite
  have : ∀ j, Nonempty (F.obj j) := fun j => by
    obtain ⟨z, hz⟩ := (hiso (unop j)).2 (lev l b (unop j))
    exact ⟨(⟨z, hz⟩ : Sl (unop j))⟩
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hstep : ∀ k a s, red (l ^ (k + 1)) (l ^ k) _ _ 0 (((sec (op (k + 1)) : Sl (k + 1)).1) a s) =
      ((sec (op k) : Sl k).1) a s := by
    intro k a s
    have h := hsec (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg (fun z : Sl k => z.1 a s) h
  refine ⟨fun a s => ⟨fun k => ((sec (op k) : Sl k).1) a s, fun k => hstep k a s⟩, ?_⟩
  apply Subtype.ext; funext k
  exact (sec (op k) : Sl k).2

theorem LimLH_of : LimLH := by
  intro hA l _ X Y S pX pY n i M N r c hfin hiso
  exact ⟨phi pX pY n i M r c hA, fun y k => rfl,
    fun y hy => phi_ker pX pY n i M r c hA N hiso y hy, fun b => phi_coker pX pY n i M r c hA N hfin hiso b⟩

end LateralTheory.KummerTheory.LimLHPf
end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.FinLimit

section

@[expose] public section

namespace LateralTheory.Fin.Limit
theorem etale_limit_extension_groups_henselian_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimExtHl := by
  apply LateralTheory.KummerTheory.LimExtHl_of
theorem etale_limit_local_homotopy_compatible_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimLH := by
  apply LateralTheory.KummerTheory.LimLHPf.LimLH_of
theorem etale_limit_cohomology_assembled_from_stages : LateralTheory.KummerTheory.LimAssemble := by
  apply LateralTheory.KummerTheory.LimAssemble_of
theorem etale_cohomology_commutes_with_inverse_limits : LateralTheory.KummerTheory.Limit := by
  apply LateralTheory.KummerTheory.Limit_of <;> first | exact etale_limit_extension_groups_henselian_in_inverse_limits_assembly | exact etale_limit_local_homotopy_compatible_in_inverse_limits_assembly | exact etale_limit_cohomology_assembled_from_stages
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Limit := etale_cohomology_commutes_with_inverse_limits
end LateralTheory.Fin.Limit
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.InvOfField

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem IsoUpTo.comb_mono {q : ℕ} {E : Spc} {n i : ℤ} {r : ℕ} {c : Fin r → Ht q E n i} {N N' : ℕ} (hd : N ∣ N')
    (h : IsoUpTo N (comb q c)) : IsoUpTo N' (comb q c) := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (m • b)
  exact ⟨a, by rw [ha, mul_smul]⟩

theorem inv_of_field (l : ℕ) (k : Type) [Field k] (hl : IsUnit (l : k)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Inv l (sch.obj X) := by
  intro U ⟨x⟩
  have h := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom
  rwa [map_natCast] at h

theorem goal_of (hLH : LH) (hInv : SHInv) (hSt : Stalk) (hB : Bock) (hAd : AdicDeg) (hL : Limit) : GOAL := by
  intro a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by rw [Nat.cast_pow]; exact hl.pow j
  have hA := hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX))
    (fun j m => e4 (l ^ j) k (hu j) pX m i)
  choose r c N hN hQ hI using hA
  obtain ⟨e, he⟩ := hLH a2 a6n b1
  let M : ℕ := n.toNat + 1
  let N' : ℕ := ∏ a ∈ Finset.range (M + 1), N (a : ℕ)
  have hN' : 0 < N' := Finset.prod_pos fun a _ => hN _
  refine hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _)
    (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_
  refine he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)
  exact hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i)
    (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm

end LateralTheory.KummerTheory

end
end
end

-- Source module: Development.EtaleCohomology.KummerTheory.GoalHolds

section

@[expose] public section

namespace LateralTheory.KummerTheory

theorem goal_holds : GOAL :=
  goal_of LateralTheory.Fin.LH.intersectionNumber_baseChange LateralTheory.Fin.SHInv.intersectionNumber_baseChange LateralTheory.Fin.Stalk.intersectionNumber_baseChange LateralTheory.Fin.Bock.intersectionNumber_baseChange
    LateralTheory.Fin.AdicDeg.intersectionNumber_baseChange LateralTheory.Fin.Limit.intersectionNumber_baseChange

end LateralTheory.KummerTheory
end
end
