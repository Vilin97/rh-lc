module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonTensor
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvFGExact

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cochains

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

abbrev cw (W : ObjectProperty C) : Cx.{max u v w} R := CH.cx (W.ι ⋙ F)

abbrev supP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∨ V T

abbrev infP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∧ V T

variable {U V : ObjectProperty C}

theorem le_supL : U ≤ supP U V := fun _ h => Or.inl h
theorem le_supR : V ≤ supP U V := fun _ h => Or.inr h
theorem inf_leL : infP U V ≤ U := fun _ h => h.1
theorem inf_leR : infP U V ≤ V := fun _ h => h.2

def liftW {W P : ObjectProperty C} (hP : Cosieve P) {n : ℕ} (t : ComposableArrows W.FullSubcategory n)
    (h : P (t.obj 0).obj) : ComposableArrows P.FullSubcategory n :=
  liftCh hP (t ⋙ W.ι) h

variable (U V)

def mvF : Cx.Hom (cw F (supP U V)) (prodCx (cw F U) (cw F V)) (RingHom.id R) where
  f n := LinearMap.prod ((resU F le_supL).pullC n) ((resU F le_supR).pullC n)
  comm n x := Prod.ext ((resU F le_supL).d_pullC n x) ((resU F le_supR).d_pullC n x)

def mvG : Cx.Hom (prodCx (cw F U) (cw F V)) (cw F (infP U V)) (RingHom.id R) where
  f n := ((resU F inf_leL).pullC n).comp (LinearMap.fst R _ _) - ((resU F inf_leR).pullC n).comp (LinearMap.snd R _ _)
  comm n x := by
    change CH.d _ n ((resU F inf_leL).pullC n x.1 - (resU F inf_leR).pullC n x.2) =
      (resU F inf_leL).pullC (n + 1) (CH.d _ n x.1) - (resU F inf_leR).pullC (n + 1) (CH.d _ n x.2)
    rw [map_sub, (resU F inf_leL).d_pullC, (resU F inf_leR).d_pullC]

variable {U V}

theorem mvF_inj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Injective ((mvF F U V).f n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  funext t
  rcases (t.obj 0).property with h | h
  · exact congrFun (congrArg Prod.fst hx) (liftW hU t h)
  · exact congrFun (congrArg Prod.snd hx) (liftW hV t h)

open Classical in
theorem mvFG_exact (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Exact ((mvF F U V).f n) ((mvG F U V).f n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, b⟩ := y
    have hab : ∀ s : ComposableArrows (infP U V).FullSubcategory n,
        (resU F inf_leL).pullC n a s = (resU F inf_leR).pullC n b s := fun s =>
      sub_eq_zero.1 (congrFun hy s)
    refine ⟨fun t => if h : U (t.obj 0).obj then a (liftW hU t h) else
      b (liftW hV t ((t.obj 0).property.resolve_left h)), Prod.ext ?_ ?_⟩
    · funext s
      exact dif_pos (s.obj 0).property
    · funext s
      by_cases h : U (s.obj 0).obj
      · refine (dif_pos h).trans ?_
        exact hab (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) s ⟨h, (s.obj 0).property⟩)
      · exact dif_neg h
  · rintro ⟨x, rfl⟩
    refine sub_eq_zero.2 ?_
    rfl


open Classical in
def extV (hU : Cosieve U) (hV : Cosieve V) {n : ℕ} (y : CH.Cn ((infP U V).ι ⋙ F) n) : CH.Cn (U.ι ⋙ F) n :=
  fun t => if h : V (t.obj 0).obj then
    y (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) t ⟨(t.obj 0).property, h⟩) else 0

theorem mvG_surj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Surjective ((mvG F U V).f n) := by
  intro y
  refine ⟨(extV F hU hV y, 0), funext fun s => ?_⟩
  have e1 : (resU F inf_leL).pullC n (extV F hU hV y) s = y s := dif_pos (s.obj 0).property.2
  have e2 : (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = 0 := congrFun (map_zero _) s
  change (resU F inf_leL).pullC n (extV F hU hV y) s - (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = y s
  rw [e1, e2, sub_zero]

end Cochains

section Family

universe w' v' u'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] (G : C' ⥤ C) {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{w} R)) (F' : C' ⥤ ModuleCat.{w'} R')
  (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T)
  (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))

def Phi {W : ObjectProperty C} {W' : ObjectProperty C'} (h : ∀ T, W' T → W (G.obj T)) (i : ι) (n : N i) :
    Cx.Hom (cw (F i) W) (cw F' W') σ :=
  (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h).hom

variable {G F F' τ hτ}

theorem phi_lin (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {W : ObjectProperty C} {W' : ObjectProperty C'}
    (h : ∀ T, W' T → W (G.obj T)) : Lin (Phi G F F' τ hτ h) :=
  ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩

theorem lin_prod {K L : ι → Cx.{w} R} {K' L' : Cx.{w'} R'} {φ : ∀ i, N i → Cx.Hom (K i) K' σ}
    {ψ : ∀ i, N i → Cx.Hom (L i) L' σ} (hφ : Lin φ) (hψ : Lin ψ) : Lin fun i n => prodHom (φ i n) (ψ i n) :=
  ⟨fun i n n' k x => Prod.ext (hφ.1 i n n' k x.1) (hψ.1 i n n' k x.2),
    fun i r n k x => Prod.ext (hφ.2 i r n k x.1) (hψ.2 i r n k x.2)⟩

theorem bc_sup [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {U V : ObjectProperty C} {U' V' : ObjectProperty C'}
    (hU : Cosieve U) (hV : Cosieve V) (hU' : Cosieve U') (hV' : Cosieve V')
    (hu : ∀ T, U' T → U (G.obj T)) (hv : ∀ T, V' T → V (G.obj T))
    (tU : BC (Phi G F F' τ hτ hu)) (tV : BC (Phi G F F' τ hτ hv))
    (tI : BC (Phi G F F' τ hτ (W := infP U V) (W' := infP U' V') fun T h => ⟨hu T h.1, hv T h.2⟩)) :
    BC (Phi G F F' τ hτ (W := supP U V) (W' := supP U' V') fun T h => h.imp (hu T) (hv T)) := by
  refine (bc_ses (fun i => mvF (F i) U V) (fun i => mvG (F i) U V) (mvF F' U' V') (mvG F' U' V')
    (fun i n => mvF_inj _ hU hV n) (fun i n => mvFG_exact _ hU hV n) (fun i n => mvG_surj _ hU hV n)
    (fun n => mvF_inj _ hU' hV' n) (fun n => mvFG_exact _ hU' hV' n) (fun n => mvG_surj _ hU' hV' n)
    _ (fun i n => prodHom (Phi G F F' τ hτ hu i n) (Phi G F F' τ hτ hv i n)) _
    (phi_lin hadd hsm _) (lin_prod (phi_lin hadd hsm _) (phi_lin hadd hsm _)) (phi_lin hadd hsm _)
    ?_ ?_).1 (bc_prod _ _ (phi_lin hadd hsm _) (phi_lin hadd hsm _) tU tV) tI
  · exact fun i m k x => rfl
  · intro i m k x
    funext s
    exact map_sub (τ i m _) _ _

end Family

end GlobalTheory.CompanionTheory.CosieveBC
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u w' v' u'

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cover

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {G : C' ⥤ C} {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] {F : ι → (C ⥤ ModuleCat.{w} R)} {F' : C' ⥤ ModuleCat.{w'} R'}
  {τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T}
  {hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x)}

theorem subsingleton_H {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Subsingleton ((cw F W).H j) := by
  have : Subsingleton ((cw F W).X j) := ⟨fun _ _ => funext fun s => (h _ (s.obj 0).property).elim⟩
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  refine (CrystallineSemistableComparison.CechClassBoundaries.cls_eq_zero a ha).2 ?_
  rw [Subsingleton.elim a 0]
  exact zero_mem _

theorem bc_congr [DecidableEq ι] {W W₂ : ObjectProperty C} {W' W₂' : ObjectProperty C'} (e : ∀ T, W T ↔ W₂ T)
    (e' : ∀ T, W' T ↔ W₂' T) (h : ∀ T, W' T → W (G.obj T)) (h₂ : ∀ T, W₂' T → W₂ (G.obj T))
    (t : BC (Phi G F F' τ hτ h)) : BC (Phi G F F' τ hτ h₂) := by
  obtain rfl : W = W₂ := funext fun T => propext (e T)
  obtain rfl : W' = W₂' := funext fun T => propext (e' T)
  exact t

theorem Wc_insert {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : supP (Wc U A S) (capS U (insert a S)) T ↔ Wc U (insert a A) S T := by
  constructor
  · rintro (⟨⟨b, hb, hT⟩, hS⟩ | h)
    · exact ⟨⟨b, Finset.mem_insert_of_mem hb, hT⟩, hS⟩
    · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
        fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨⟨b, hb, hT⟩, hS⟩
    rcases Finset.mem_insert.1 hb with rfl | h
    · refine Or.inr fun c hc => ?_
      rcases Finset.mem_insert.1 hc with rfl | h'
      · exact hT
      · exact hS c h'
    · exact Or.inl ⟨⟨b, h, hT⟩, hS⟩

theorem Wc_inf {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : Wc U A (insert a S) T ↔ infP (Wc U A S) (capS U (insert a S)) T :=
  ⟨fun h => ⟨⟨h.1, fun b hb => h.2 b (Finset.mem_insert_of_mem hb)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem wc_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (A S : Finset α) (T : C') (hT : Wc U' A S T) : Wc U A S (G.obj T) := by
  obtain ⟨⟨a, ha, hT⟩, hS⟩ := hT
  exact ⟨⟨a, ha, h a T hT⟩, fun b hb => h b T (hS b hb)⟩

theorem cap_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (S : Finset α) (T : C') (hT : capS U' S T) : capS U S (G.obj T) :=
  fun b hb => h b T (hT b hb)

theorem bc_Wc [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {α : Type} [DecidableEq α]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {U : α → ObjectProperty C} {U' : α → ObjectProperty C'} (hU : ∀ a, Cosieve (U a)) (hU' : ∀ a, Cosieve (U' a))
    (h : ∀ a T, U' a T → U a (G.obj T))
    (hcap : ∀ S : Finset α, S.Nonempty → BC (Phi G F F' τ hτ (cap_le h S))) (A : Finset α) :
    ∀ S : Finset α, BC (Phi G F F' τ hτ (wc_le h A S)) := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j
    have e : ∀ {D : Type u} [Category.{v} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have e' : ∀ {D : Type u'} [Category.{v'} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have s1 := fun i => subsingleton_H (F i) (e U) j
    have s2 := subsingleton_H F' (e' U') j
    exact tens_subsingleton _
  | insert a A ha ih =>
    intro S
    have key := bc_sup (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm (cosieve_Wc hU A S)
      (cosieve_capS hU (insert a S)) (cosieve_Wc hU' A S) (cosieve_capS hU' (insert a S))
      (wc_le h A S) (cap_le h (insert a S)) (ih S) (hcap _ (Finset.insert_nonempty _ _))
      (bc_congr (Wc_inf U a A S) (Wc_inf U' a A S) _ _ (ih (insert a S)))
    exact bc_congr (Wc_insert U a A S) (Wc_insert U' a A S) _ _ key

theorem restrict_bij {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F W.ι).hom.f n) := by
  have hW : Cosieve W := fun _ _ _ _ => hall _
  refine ⟨fun x y hxy => funext fun s => congrFun hxy (liftCh hW s (hall _)), fun y => ⟨extZ hW y, pull_extZ hW y⟩⟩

def resEquiv {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (j : ℕ) : CH.H F j ≃ₗ[R] (cw F W).H j :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F W.ι).hom.mapH j) (CrystallineSemistableComparison.P.mapH_bij _ (restrict_bij F hall) j)

theorem tens_top [Fintype ι] [DecidableEq ι]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {W : ObjectProperty C} {W' : ObjectProperty C'} (hall : ∀ T, W T) (hall' : ∀ T, W' T)
    (h : ∀ T, W' T → W (G.obj T)) (t : BC (Phi G F F' τ hτ h)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  have lq : Lin (K := fun i => CH.cx (F i)) (K' := CH.cx F') (σ := σ)
      fun i n => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).hom :=
    ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩
  refine tens_of_bij (bal_mapH (phi_lin hadd hsm h) j) (bal_mapH lq j) (fun i => resEquiv (F i) hall j)
    (resEquiv F' hall' j).toAddEquiv (fun i n x => ?_) (t j)
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

end Cover

theorem base_change_of_cover : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (U : A → ObjectProperty C) (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T) (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS U S) j) (M' := HU F' (capS U' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS U S) (U' := capS U' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ U U' hU hU' hc hc' h H j
  classical
  have key := bc_Wc (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm hU hU' h
    (fun S hS j => H S hS j) Finset.univ ∅
  refine tens_top hadd hsm (W := Wc U Finset.univ ∅) (W' := Wc U' Finset.univ ∅) (fun T => ?_) (fun T => ?_) _ key j
  · obtain ⟨a, ha⟩ := hc T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩
  · obtain ⟨a, ha⟩ := hc' T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩

end GlobalTheory.CompanionTheory.CosieveBC
end
end
end
