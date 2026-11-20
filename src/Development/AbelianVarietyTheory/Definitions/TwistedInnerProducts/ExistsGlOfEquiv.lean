import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev Unif : Type _ := sorry

instance : Nonempty (Unif k) := sorry



variable {k}

namespace Unif
variable (q : Unif k)

theorem ne_zero : ((q.1 : 𝒪[k]) : k) ≠ 0 := by sorry

def unit : kˣ := sorry

def inv : k := sorry

theorem mem_max_iff {a : 𝒪[k]} : a ∈ maximalIdeal 𝒪[k] ↔ q.1 ∣ a := by sorry


theorem mem_max : q.1 ∈ maximalIdeal 𝒪[k] := by sorry

@[simp] theorem smul_inv_smul {n : Type*} (x : n → k) : q.1 • q.inv • x = x := by sorry



@[simp] theorem inv_smul_smul {n : Type*} (x : n → k) : q.inv • q.1 • x = x := by sorry


end Unif

variable (k) in

structure Pair (n : Type*) where

  lat : Submodule 𝒪[k] (n → k)
  isLat : lat.IsLattice k

  fn : lat →ₗ[𝒪[k]] 𝓀[k]
  fn_ne : fn ≠ 0

variable {n n' : Type*}

namespace Pair

def HasVal (P : Pair k n) (x : n → k) (a : 𝓀[k]) : Prop := sorry

variable {P Q : Pair k n} {x y e : n → k} {a b : 𝓀[k]}

theorem HasVal.mem (h : P.HasVal x a) : x ∈ P.lat := by sorry

theorem HasVal.unique (h : P.HasVal x a) (h' : P.HasVal x b) : a = b := by sorry

theorem hasVal_fn (P : Pair k n) (x : P.lat) : P.HasVal x (P.fn x) := by sorry

theorem mem_lat_iff : x ∈ P.lat ↔ ∃ a, P.HasVal x a := by sorry

theorem HasVal.add (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x + y) (a + b) := by sorry


theorem HasVal.sub (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x - y) (a - b) := by sorry


theorem HasVal.smul (h : P.HasVal x a) (s : 𝒪[k]) : P.HasVal (s • x) (residue 𝒪[k] s * a) := by sorry



theorem ext (h : ∀ x a, P.HasVal x a ↔ Q.HasVal x a) : P = Q := by sorry













theorem exists_hasVal_one (P : Pair k n) : ∃ e, P.HasVal e 1 := by sorry







def ker (P : Pair k n) : Submodule 𝒪[k] (n → k) := sorry

theorem mem_ker : x ∈ P.ker ↔ P.HasVal x 0 := by sorry


theorem ker_le (P : Pair k n) : P.ker ≤ P.lat := by sorry

theorem smul_mem_ker {s : 𝒪[k]} (hs : s ∈ maximalIdeal 𝒪[k]) (hx : x ∈ P.lat) : s • x ∈ P.ker := by sorry




theorem ker_isLat (P : Pair k n) : P.ker.IsLattice k := by sorry










def vec (P : Pair k n) : n → k := sorry

theorem hasVal_vec (P : Pair k n) : P.HasVal P.vec 1 := by sorry

theorem hasVal_iff (he : P.HasVal e 1) :
    P.HasVal x a ↔ ∃ s : 𝒪[k], residue 𝒪[k] s = a ∧ x - s • e ∈ P.ker := by sorry







theorem hasVal_one_iff (he : P.HasVal e 1) : P.HasVal x 1 ↔ x - e ∈ P.ker := by sorry


theorem sub_vec_mem (he : P.HasVal e 1) : e - P.vec ∈ P.ker := by sorry

theorem lat_eq (he : P.HasVal e 1) : P.lat = P.ker ⊔ Submodule.span 𝒪[k] {e} := by sorry





theorem ext_ker (hk : P.ker = Q.ker) (he : P.HasVal e 1) (he' : Q.HasVal e 1) : P = Q := by sorry


end Pair

structure IsGlue (L : Submodule 𝒪[k] (n → k)) (e : n → k) : Prop where
  isLat : L.IsLattice k
  not_mem : e ∉ L
  smul_mem : ∀ s ∈ maximalIdeal 𝒪[k], s • e ∈ L

theorem isGlue_iff (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {e : n → k} :
    IsGlue L e ↔ L.IsLattice k ∧ e ∉ L ∧ q.1 • e ∈ L := by sorry





theorem Pair.isGlue {P : Pair k n} {e : n → k} (he : P.HasVal e 1) : IsGlue P.ker e := by sorry


theorem IsGlue.smul_mem_iff {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) {s : 𝒪[k]} :
    s • e ∈ L ↔ s ∈ maximalIdeal 𝒪[k] := by sorry






theorem IsGlue.exists_pair {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) :
    ∃ P : Pair k n, P.ker = L ∧ P.HasVal e 1 := by sorry









































def glue {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) : Pair k n := sorry

section
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}

@[simp] theorem glue_ker (h : IsGlue L e) : (glue h).ker = L := by sorry

theorem glue_hasVal (h : IsGlue L e) : (glue h).HasVal e 1 := by sorry

theorem glue_lat (h : IsGlue L e) : (glue h).lat = L ⊔ Submodule.span 𝒪[k] {e} := by sorry


theorem eq_glue_iff (h : IsGlue L e) {P : Pair k n} : P = glue h ↔ P.ker = L ∧ P.HasVal e 1 := by sorry


theorem Pair.glue_self {P : Pair k n} (he : P.HasVal e 1) : glue (Pair.isGlue he) = P := by sorry


theorem glue_eq_glue_iff (h : IsGlue L e) (h' : IsGlue L' e') : glue h = glue h' ↔ L = L' ∧ e' - e ∈ L := by sorry


end

variable (k) in

structure GluePair (n : Type*) where

  ker : Submodule 𝒪[k] (n → k)
  isLat : ker.IsLattice k

  cls : (n → k) ⧸ ker
  cls_ne : cls ≠ 0
  smul_cls : ∀ s ∈ maximalIdeal 𝒪[k], s • cls = 0

def Pair.toGlue (P : Pair k n) : GluePair k n where
  ker := sorry





theorem Pair.toGlue_bijective : Function.Bijective (Pair.toGlue : Pair k n → GluePair k n) := by sorry

















def Pair.glueEquiv : Pair k n ≃ GluePair k n := sorry

namespace Pair

instance (P : Pair k n) : P.lat.IsLattice k := sorry
instance (P : Pair k n) : P.ker.IsLattice k := sorry

instance : SMul 𝓀[k]ˣ (Pair k n) where
  smul c P := sorry

@[simp] theorem dia_lat (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).lat = P.lat := by sorry

theorem dia_hasVal {c : 𝓀[k]ˣ} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (c • P).HasVal x a ↔ P.HasVal x ((c⁻¹ : 𝓀[k]ˣ) * a) := by sorry




instance : MulAction 𝓀[k]ˣ (Pair k n) where
  one_smul P := sorry


@[simp] theorem dia_ker (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).ker = P.ker := by sorry



theorem dia_hasVal_one {c : 𝓀[k]ˣ} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) {s : 𝒪[k]}
    (hs : residue 𝒪[k] s = (c⁻¹ : 𝓀[k]ˣ)) : (c • P).HasVal (s • e) 1 := by sorry



open Classical in

def ev (P : Pair k n) (x : n → k) : 𝓀[k] := sorry

theorem hasVal_ev {P : Pair k n} {x : n → k} (h : x ∈ P.lat) : P.HasVal x (P.ev x) := by sorry

theorem HasVal.ev_eq {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) : P.ev x = a := by sorry


end Pair

def Red (L : Submodule 𝒪[k] (n → k)) : Type _ := sorry

namespace Red
variable (L : Submodule 𝒪[k] (n → k))

instance : AddCommGroup (Red L) := sorry

instance : Module 𝒪[k] (Red L) := sorry

instance : Module 𝓀[k] (Red L) := sorry

instance : IsScalarTower 𝒪[k] 𝓀[k] (Red L) := sorry



def mk : L →ₗ[𝒪[k]] Red L := sorry

theorem mk_surjective : Function.Surjective (mk L) := by sorry

variable {L}

theorem mk_eq_zero (q : Unif k) {x : L} : mk L x = 0 ↔ q.inv • (x : n → k) ∈ L := by sorry








theorem residue_smul (s : 𝒪[k]) (x : Red L) : residue 𝒪[k] s • x = s • x := by sorry

def out (x : Red L) : L := sorry

@[simp] theorem mk_out (x : Red L) : mk L x.out = x := by sorry

instance [L.IsLattice k] : Module.Finite 𝓀[k] (Red L) := sorry



instance [L.IsLattice k] : Finite (Red L) := sorry

instance [L.IsLattice k] : Finite (Module.Dual 𝓀[k] (Red L)) := sorry

theorem finrank_eq [Fintype n] [L.IsLattice k] : Module.finrank 𝓀[k] (Red L) = Fintype.card n := by sorry




theorem card_eq [Fintype n] [L.IsLattice k] : Nat.card (Red L) = SplitWeil.resCard k ^ Fintype.card n := by sorry



end Red

def Pair.red (P : Pair k n) : Module.Dual 𝓀[k] (Red P.lat) := sorry





@[simp] theorem Pair.red_mk (P : Pair k n) (x : P.lat) : P.red (Red.mk _ x) = P.fn x := by sorry

theorem Pair.red_ne (P : Pair k n) : P.red ≠ 0 := by sorry


section
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]

def ofDual (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : Pair k n where
  lat := sorry






@[simp] theorem ofDual_lat (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : (ofDual L f).lat = L := by sorry

theorem ofDual_hasVal (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) (x : L) :
    (ofDual L f).HasVal x (f.1 (Red.mk L x)) := by sorry

theorem Pair.ofDual_red (P : Pair k n) : ofDual P.lat ⟨P.red, P.red_ne⟩ = P := by sorry

def latEquiv : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} ≃ {P : Pair k n // P.lat = L} := sorry










variable (q : Unif k)

theorem isGlue_inv_smul {x : L} (hx : Red.mk L x ≠ 0) : IsGlue L (q.inv • (x : n → k)) := by sorry


def up (x : {x : Red L // x ≠ 0}) : Pair k n := sorry


@[simp] theorem up_ker (x : {x : Red L // x ≠ 0}) : (up L q x).ker = L := by sorry

theorem up_hasVal_iff (x : {x : Red L // x ≠ 0}) (y : L) :
    (up L q x).HasVal (q.inv • (y : n → k)) 1 ↔ Red.mk L y = x.1 := by sorry



theorem up_mk {y : L} (hy : Red.mk L y ≠ 0) : up L q ⟨_, hy⟩ = glue (isGlue_inv_smul L q hy) := by sorry


def kerEquiv : {x : Red L // x ≠ 0} ≃ {P : Pair k n // P.ker = L} := sorry














end

theorem finite_lat (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.lat = L}.Finite := by sorry




theorem finite_ker (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.ker = L}.Finite := by sorry





def withLat (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := sorry

def withKer (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := sorry

@[simp] theorem mem_withLat {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withLat L ↔ P.lat = L := by sorry


@[simp] theorem mem_withKer {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withKer L ↔ P.ker = L := by sorry


theorem sum_withLat {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withLat L, F P = ∑ f, F (ofDual L f) := by sorry




theorem sum_withKer {M : Type*} [AddCommMonoid M] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k)
    [Fintype {x : Red L // x ≠ 0}] (F : Pair k n → M) :
    ∑ P ∈ withKer L, F P = ∑ x, F (up L q x) := by sorry




def cross (q : Unif k) (P₁ P : Pair k n) : 𝓀[k] := sorry

theorem cross_hasVal (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) {e : n → k} (he : P₁.HasVal e 1) :
    P.HasVal (q.1 • e) (cross q P₁ P) := by sorry




theorem cross_up (q : Unif k) (P : Pair k n) (x : {x : Red P.lat // x ≠ 0}) :
    cross q (up P.lat q x) P = P.red x.1 := by sorry




theorem cross_up_ofDual (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (x : {x : Red L // x ≠ 0})
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : cross q (up L q x) (ofDual L f) = f.1 x.1 := by sorry




theorem cross_dia_right (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q P₁ (c • P) = c * cross q P₁ P := by sorry



theorem cross_dia_left (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q (c • P₁) P = (c⁻¹ : 𝓀[k]ˣ) * cross q P₁ P := by sorry





section Action
variable [Fintype n] [DecidableEq n]

theorem mem_smul_iff {g : GL n k} {L : Submodule 𝒪[k] (n → k)} {x : n → k} : x ∈ g • L ↔ g⁻¹ • x ∈ L := by sorry



instance isLattice_smul (g : GL n k) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsFullLattice k] : (g • L).IsLattice k := sorry











abbrev latStab (L : Submodule 𝒪[k] (n → k)) : Subgroup (GL n k) := sorry

namespace Pair

instance : SMul (GL n k) (Pair k n) where
  smul g P := sorry









@[simp] theorem smul_lat (g : GL n k) (P : Pair k n) : (g • P).lat = g • P.lat := by sorry

theorem smul_hasVal {g : GL n k} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (g • P).HasVal x a ↔ P.HasVal (g⁻¹ • x) a := by sorry


instance : MulAction (GL n k) (Pair k n) where
  one_smul P := sorry


instance : SMulCommClass (GL n k) 𝓀[k]ˣ (Pair k n) where
  smul_comm g c P := sorry

theorem HasVal.gl_smul {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) (g : GL n k) :
    (g • P).HasVal (g • x) a := by sorry

@[simp] theorem smul_ker (g : GL n k) (P : Pair k n) : (g • P).ker = g • P.ker := by sorry



theorem smul_eq_iff {g : GL n k} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) :
    g • P = P ↔ g • P.ker = P.ker ∧ g • e - e ∈ P.ker := by sorry




end Pair

theorem cross_smul (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (g : GL n k) :
    cross q (g • P₁) (g • P) = cross q P₁ P := by sorry




theorem exists_gl_of_equiv {L L' : Submodule 𝒪[k] (n → k)} [L.IsLattice k] [L'.IsLattice k] (e : L ≃ₗ[𝒪[k]] L') :
    ∃ g : GL n k, ∀ x : L, g • (x : n → k) = e x := by sorry













omit [Fintype n] [DecidableEq n] in

theorem Pair.exists_split (P : Pair k n) :
    ∃ (K : Submodule 𝒪[k] P.lat) (e : (K × 𝒪[k]) ≃ₗ[𝒪[k]] P.lat), ∀ z, P.fn (e z) = residue 𝒪[k] z.2 := by sorry





















instance : MulAction.IsPretransitive (GL n k) (Pair k n) where
  exists_smul_eq P Q := sorry























end Action

section Std
variable [Fintype n]

variable (k n) in

def stdLat : Submodule 𝒪[k] (n → k) := sorry

omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_stdLat {x : n → k} : x ∈ stdLat k n ↔ ∀ i, x i ∈ 𝒪[k] := by sorry


instance : (stdLat k n).IsLattice k := sorry










variable (k) in

def stdPair (i : n) : Pair k n where
  lat := sorry










theorem stdPair_hasVal {i : n} {x : n → k} {a : 𝓀[k]} :
    (stdPair k i).HasVal x a ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], residue 𝒪[k] ⟨x i, h i⟩ = a := by sorry


instance [Nonempty n] : Nonempty (Pair k n) := sorry

end Std

end GlobalTheory.LatPair
