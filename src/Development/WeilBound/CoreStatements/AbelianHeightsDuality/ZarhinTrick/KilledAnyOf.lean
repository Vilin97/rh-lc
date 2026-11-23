module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiPtsA

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

namespace PositivityTheory.PrwZar.QiP

variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]

theorem spMap_comp {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (φ : F →ₐ[R] S) (ψ : S →ₐ[R] T) : spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  simp [spMap, ← Spec.map_comp]
  rfl

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def mulPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) : F →ₐ[R] S :=
  (hs.mul S φ φ').choose

theorem mulPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) :
    spMap (mulPt hs φ φ') ≫ h = (spMap φ ≫ h) * (spMap φ' ≫ h) :=
  (hs.mul S φ φ').choose_spec

def onePt (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : F →ₐ[R] S :=
  (hs.one S).choose

theorem onePt_spec (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] :
    spMap (onePt hs S) ≫ h = 1 :=
  (hs.one S).choose_spec

theorem pt_ext (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] {φ φ' : F →ₐ[R] S}
    (e : spMap φ ≫ h = spMap φ' ≫ h) : φ = φ' :=
  hs.mono S φ φ' e

def powPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) : ℕ → (F →ₐ[R] S)
  | 0 => onePt hs S
  | n + 1 => mulPt hs (powPt hs φ n) φ

theorem powPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) (n : ℕ) :
    spMap (powPt hs φ n) ≫ h = (spMap φ ≫ h) ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact onePt_spec hs S
  | succ n ih => rw [pow_succ, ← ih]; exact mulPt_spec hs _ _

variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

theorem comp_mulPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ φ' : F →ₐ[R] S) :
    ψ.comp (mulPt hs φ φ') = mulPt hs (ψ.comp φ) (ψ.comp φ') := by
  apply pt_ext hs
  rw [mulPt_spec, ← spMap_comp, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, Category.assoc,
    mulPt_spec, MonObj.comp_mul]

theorem comp_onePt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) : ψ.comp (onePt hs S) = onePt hs T := by
  apply pt_ext hs
  rw [onePt_spec, ← spMap_comp, Category.assoc, onePt_spec, MonObj.comp_one]

theorem comp_powPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ : F →ₐ[R] S) (n : ℕ) :
    ψ.comp (powPt hs φ n) = powPt hs (ψ.comp φ) n := by
  apply pt_ext hs
  rw [powPt_spec, ← spMap_comp, Category.assoc, powPt_spec, MonObj.comp_pow, ← Category.assoc, spMap_comp]

theorem powPt_mul (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) (a b : ℕ) :
    powPt hs φ (a * b) = powPt hs (powPt hs φ a) b := by
  apply pt_ext hs
  rw [powPt_spec, powPt_spec, powPt_spec, pow_mul]

theorem mulPt_onePt (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs (onePt hs S) φ = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.one_mul]

theorem mulPt_onePt' (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs φ (onePt hs S) = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.mul_one]

end PositivityTheory.PrwZar.QiP
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

open TensorProduct

namespace PositivityTheory.PrwZar.QiP

open GlobalTheory.CompanionTheory.Ar.GR

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Field C] [Algebra R C] {F : Type} [CommRing F] [Algebra R F]

def uu : F →ₐ[R] (C ⊗[R] F) := (Algebra.TensorProduct.includeRight : F →ₐ[R] C ⊗[R] F)

def lft {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    (C ⊗[R] F) →ₐ[C] T :=
  Algebra.TensorProduct.lift (Algebra.ofId C T) g (fun _ _ => Commute.all _ _)

theorem lft_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    ((lft g).restrictScalars R).comp (uu (C := C)) = g := by
  ext x
  simp [lft, uu]

theorem ext_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T]
    (x y : (C ⊗[R] F) →ₐ[C] T)
    (e : (x.restrictScalars R).comp (uu (C := C)) = (y.restrictScalars R).comp (uu (C := C))) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact e

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def u1 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeLeft : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def u2 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeRight : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def dlt (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  lft (mulPt hs (u1 (C := C)) u2)

def eps (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] C :=
  lft (onePt hs C)

theorem eps_uu (hs : IsFinFlatSub G F h) :
    ((((Algebra.ofId C (C ⊗[R] F)).comp (eps (C := C) hs)).restrictScalars R).comp (uu (C := C))) = onePt hs (C ⊗[R] F) := by
  rw [← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]
  rfl

theorem mul_dlt_uu (hs : IsFinFlatSub G F h) (f g : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F)) :
    ((((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C))) = mulPt hs ((f.restrictScalars R).comp uu) ((g.restrictScalars R).comp uu) := by
  have e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp
        (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl
  rw [e, dlt, lft_uu, comp_mulPt]
  congr 1
  · ext x
    simp [u1, uu]
  · ext x
    simp [u2, uu]

theorem counitL (hs : IsFinFlatSub G F h) : Qi.CounitL (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt hs _

theorem counitR (hs : IsFinFlatSub G F h) : Qi.CounitR (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt' hs _

theorem pw_uu (hs : IsFinFlatSub G F h) (n : ℕ) :
    ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n).restrictScalars R).comp uu = powPt hs uu n := by
  induction n with
  | zero => exact eps_uu hs
  | succ n ih =>
    change (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n)
      (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _
    rw [mul_dlt_uu, ih]
    rfl

theorem pw_mul (hs : IsFinFlatSub G F h) (a b : ℕ) :
    Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (a * b) = (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b) := by
  apply ext_uu
  rw [pw_uu, powPt_mul]
  have hc : (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp
      (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl
  rw [hc, pw_uu, comp_powPt, pw_uu]

def ptGrp (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : Subgroup (sp (R₀ := R) S ⟶ G) where
  carrier := {g | ∃ φ : F →ₐ[R] S, spMap φ ≫ h = g}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨φ', rfl⟩
    exact ⟨mulPt hs φ φ', mulPt_spec hs φ φ'⟩
  one_mem' := ⟨onePt hs S, onePt_spec hs S⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    obtain ⟨χ, hχ⟩ := hs.inv S φ
    exact ⟨χ, eq_inv_of_mul_eq_one_left hχ⟩

theorem pts_killed [Module.Finite R F] (hs : IsFinFlatSub G F h) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (C ⊗[R] F) →ₐ[C] C, x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) m) = eps hs := by
  haveI : Finite (ptGrp hs C) :=
    Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C))
      (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)
  refine ⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩
  apply ext_uu
  have hx : ((x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp
      (uu (C := C)) = (x.restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl
  have he : ((eps (C := C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _
  rw [hx, pw_uu, comp_powPt, he]
  apply pt_ext hs
  rw [powPt_spec, onePt_spec]
  have h1 := pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)
  exact congrArg Subtype.val h1

theorem uu_injective [Module.Flat R F] (hR : Function.Injective (algebraMap R C)) :
    Function.Injective (uu (R := R) (C := C) (F := F)) := Algebra.TensorProduct.includeRight_injective hR

end BaseChange

end PositivityTheory.PrwZar.QiP

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR QiP

theorem killedAny_of (hc : Qi.KilledCore) : KilledAny := by
  intro C _ _ v R _ _ hv G _ _ F _ _ h hs
  haveI := hs.fin
  haveI := hs.proj
  obtain ⟨N, hN0, hN⟩ := hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs)
    (pts_killed hs)
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have key : powPt hs (AlgHom.id R F) N = onePt hs F := by
    have e1 := pw_uu (C := C) hs N
    have e0 := pw_uu (C := C) hs 0
    rw [hN, e0] at e1
    have a1 : (uu (R := R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by
      rw [comp_powPt, AlgHom.comp_id]
    have a0 : (uu (R := R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by
      rw [comp_onePt]
      rfl
    ext y
    apply uu_injective (C := C) hinj
    exact congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))
  refine ⟨N, hN0, fun S _ _ φ => ?_⟩
  rw [← powPt_spec hs, ← onePt_spec hs S]
  have e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F) := by rw [key]
  rw [comp_powPt, comp_onePt, AlgHom.comp_id] at e
  rw [e]

end PositivityTheory.PrwZar
end
end
end
