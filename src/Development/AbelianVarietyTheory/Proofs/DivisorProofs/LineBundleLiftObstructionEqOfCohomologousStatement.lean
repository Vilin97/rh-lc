module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionEqOfCohomologousCocycles

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObU_of_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c hfun hrel hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hlift : ∀ T, ∃ τ : (L.B T)ˣ, L.p T (τ : L.B T) = (t T : F.obj T) := by
    intro T
    obtain ⟨b, hb⟩ := L.surj T (t T : F.obj T)
    obtain ⟨b', hb'⟩ := L.surj T (((t T)⁻¹ : (F.obj T)ˣ) : F.obj T)
    have hn : L.p T (b * b' - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hb, hb']; simp
    rw [L.ker] at hn
    have hnil : IsNilpotent (b * b' - 1) := by
      refine ⟨2, ?_⟩
      have h2 : (b * b' - 1) ^ 2 ∈ (I.map (algebraMap R (L.B T))) ^ 2 := Ideal.pow_mem_pow hn 2
      rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h2
      simpa using h2
    have hu : IsUnit (b * b') := by simpa using hnil.isUnit_one_add
    exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simp [hb]⟩
  choose τ hτ using hlift
  let ρu : ∀ {T T' : C} (_ : T ⟶ T'), (L.B T)ˣ →* (L.B T')ˣ := fun a ↦ Units.map (L.ρ a).toRingHom.toMonoidHom
  refine ⟨fun T T' a ↦ τ T' * v T T' a * (ρu a (τ T))⁻¹, σ, z, ?_, hσ, hc, ?_⟩
  · intro T T' a
    have hm : IsUnit (mp F a (t T : F.obj T)) := (t T).isUnit.map (mp F a)
    have hinv : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
      have := (ρu a (τ T)).inv_mul
      simpa [ρu] using this
    refine (hm.mul_left_inj).mp ?_
    have key : L.p T' (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.p T' (L.ρ a (τ T : L.B T)) = 1 := by
      rw [← map_mul, hinv, map_one]
    rw [hrel, ← hτ T, ← L.nat a]
    simp only [Units.val_mul, map_mul]
    rw [_root_.mul_assoc _ (L.p T' _), key, _root_.mul_one, hτ T', hv]
  · intro T T' T'' a b
    refine ⟨(hz T T' T'' a b).1, ?_⟩
    have hzb := (hz T T' T'' a b).2
    have e1 : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have h : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
        simpa [ρu] using (ρu a (τ T)).inv_mul
      rw [← map_mul, h, map_one]
    have e2 : (((ρu b (τ T'))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (τ T' : L.B T') = 1 := by
      have := (ρu b (τ T')).inv_mul
      simpa [ρu] using this
    have e3 : (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have := (ρu (a ≫ b) (τ T)).inv_mul
      rw [← hfun a b]
      simpa [ρu] using this
    have he : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) = (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') := by
      linear_combination (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * e1 - (L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T'))) * e3
    simp only [Units.val_mul, map_mul]
    rw [he]
    linear_combination ((τ T'' : L.B T'') * L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * e2 + ((τ T'' : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * hzb

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionEqOfCohomologousCocyclesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lifting_obstruction_eq_of_cohomologous_cocycles : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  first | exact @GlobalTheory.LBObs.isObU_of_cob | exact GlobalTheory.LBObs.isObU_of_cob | (intros; apply GlobalTheory.LBObs.isObU_of_cob <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionUnique

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem mul_eq_zero_of_mem_map {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x x' : B} (hx : x ∈ I.map (algebraMap R B)) (hx' : x' ∈ I.map (algebraMap R B)) : x * x' = 0 := by
  have h := Ideal.mul_mem_mul hx hx'
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact (Submodule.mem_bot _).1 h

theorem isSig_unique {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
    [Algebra R₀ R₁] (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (hσ' : α.IsSig p σ')
    (y : R₁ ⊗[R₀] B₀) : σ' y = σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx']

theorem isObU_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  have hσσ : ∀ T y, σ' T y = σ T y := fun T y ↦ isSig_unique α (L.p T) (L.surj T) (σ T) (σ' T) (hσ T) (hσ' T) y
  have hy : ∀ (T T' : C) (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F.obj T', α.KerQ y ∧
      σ T' y = (v' T T' a : L.B T') * ((v T T' a)⁻¹ : (L.B T')ˣ) - 1 := by
    intro T T' a
    refine (sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
      (σ T') (hσ T')).2.2.2 _ ((L.ker T' _).1 ?_)
    rw [map_sub, map_mul, hv', ← hv, ← map_mul, Units.mul_inv, map_one, sub_self]
  choose y hyK hyσ using hy
  rw [H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -y T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L.smooth T''
  haveI : Module.Flat R (L.B T'') := Algebra.Smooth.flat R _
  have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T')
    (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b) (L.nat b)
    (σ T') (σ T'') (hσ T') (hσ T'')
  have bas := sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  have em : ∀ x, mp (ext R₁ F) b x = extHom R₁ (mp F b) x := fun _ ↦ rfl
  simp only [d1_apply, Pi.sub_apply, map_neg, em]
  rw [← sub_eq_zero]
  apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
    (L.ker T'') (σ T'') (hσ T'')
  · have k1 := nat.2 _ (hyK T T' a)
    have k2 := hyK T T'' (a ≫ b)
    have k3 := hyK T' T'' b
    have k4 := (hz T T' T'' a b).1
    have k5 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at k1 k2 k3 k4 k5 ⊢
    simp only [map_sub, map_add (f := _), map_neg, k1, k2, k3, k4, k5]
    simp
  ·
    have e1 := (hz T T' T'' a b).2
    have e2 := (hz' T T' T'' a b).2
    rw [hσσ] at e2
    set P := σ T'' (extHom R₁ (mp F b) (y T T' a)) with hP
    set Q := σ T'' (y T' T'' b) with hQ
    set Y := σ T'' (y T T'' (a ≫ b)) with hY
    set Z := σ T'' (z.1 T T' T'' a b) with hZ
    set Z' := σ T'' (z'.1 T T' T'' a b) with hZ'
    have va : (v' T T' a : L.B T') = (1 + σ T' (y T T' a)) * (v T T' a : L.B T') := by
      rw [hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vb : (v' T' T'' b : L.B T'') = (1 + Q) * (v T' T'' b : L.B T'') := by
      rw [hQ, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    have vab : (v' T T'' (a ≫ b) : L.B T'') = (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      rw [hY, hyσ, add_sub_cancel, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    rw [va, vb, vab, map_mul, map_add (f := _), map_one, nat.1] at e2
    rw [← hP] at e2
    have mem : ∀ x, σ T'' x ∈ I.map (algebraMap R (L.B T'')) := bas.1
    have sq : ∀ x x', σ T'' x * σ T'' x' = 0 := fun x x' ↦ mul_eq_zero_of_mem_map hI (mem x) (mem x')
    have hPQ : P * Q = 0 := sq _ _
    have hPZ : P * Z = 0 := sq _ _
    have hQZ : Q * Z = 0 := sq _ _
    have hZY : Z' * Y = 0 := sq _ _
    have hV : (v T T'' (a ≫ b) : L.B T'') * ((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) = 1 := Units.mul_inv _
    simp only [map_sub, map_add (f := _), map_neg]
    rw [← hP, ← hQ, ← hY, ← hZ, ← hZ']
    have E : (1 + P) * (1 + Q) * (1 + Z) * (v T T'' (a ≫ b) : L.B T'') =
        (1 + Z') * (1 + Y) * (v T T'' (a ≫ b) : L.B T'') := by
      linear_combination e2 - (1 + P) * (1 + Q) * e1
    linear_combination -(((v T T'' (a ≫ b))⁻¹ : (L.B T'')ˣ) : L.B T'') * E
      + ((1 + P) * (1 + Q) * (1 + Z) - (1 + Z') * (1 + Y)) * hV + (1 + Z) * hPQ + hPZ + hQZ - hZY

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionUniqueStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.unitCocycleLiftObstruction_unique : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u c' → c = c' := by
  first | exact @GlobalTheory.LBObs.isObU_unique | exact GlobalTheory.LBObs.isObU_unique | (intros; apply GlobalTheory.LBObs.isObU_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfCohomologous

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LBObs.obU_eq_of_cohomologous : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c' → c = c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c c' hF ht hc hc'
  exact GlobalTheory.T.unitCocycleLiftObstruction_unique R R₀ I hI π hπ hk R₁ α C F L u' c c'
    (GlobalTheory.T.lifting_obstruction_eq_of_cohomologous_cocycles R R₀ I hI π hπ hk R₁ α C F L u u' t c hF ht hc) hc'
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfCohomologousStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_eq_of_cohomologous : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c' → c = c' := by
  first | exact @GlobalTheory.LBObs.obU_eq_of_cohomologous | exact GlobalTheory.LBObs.obU_eq_of_cohomologous | (intros; apply GlobalTheory.LBObs.obU_eq_of_cohomologous <;> assumption)
end
end
