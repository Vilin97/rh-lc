module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameThinAffineBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameThinAffineBasisStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∃ (C : Type) (_ : Category.{0} C) (_ : Quiver.IsThin C) (G : C ⥤ AffOp X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, opOf G T')ˣ), IsBas (opOf G) ∧ IsFrame L (opOf G) (opOf_le G) u := by
  first | exact @GlobalTheory.LBFrameEx.exists_frame | exact GlobalTheory.LBFrameEx.exists_frame | (intros; apply GlobalTheory.LBFrameEx.exists_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCocycleLiftObstruction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem exists_isObU : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u hL hu
  have hmul : ∀ T (x y : L.B T), x ∈ I.map (algebraMap R (L.B T)) → y ∈ I.map (algebraMap R (L.B T)) →
      x * y = 0 := by
    intro T x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    rw [← pow_two, ← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
    exact (Ideal.mem_bot).1 h
  have hv : ∀ (T T' : C) (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' (v : L.B T') = (u T T' a : F.obj T') := by
    intro T T' a
    obtain ⟨x, hx⟩ := L.surj T' (u T T' a : F.obj T')
    obtain ⟨y, hy⟩ := L.surj T' (↑(u T T' a)⁻¹ : F.obj T')
    have hn : x * y - 1 ∈ I.map (algebraMap R (L.B T')) := by
      rw [← L.ker T', map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
    have hn2 := hmul T' _ _ hn hn
    exact ⟨⟨x, y * (1 - (x * y - 1)), by linear_combination (-1 : L.B T') * hn2,
      by linear_combination (-1 : L.B T') * hn2⟩, hx⟩
  choose v hvp using hv
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hbas := fun T ↦ sig_basic R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
    (L.ker T) (σ T) (hσ T)
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * ↑(v T T'' (a ≫ b))⁻¹ - 1 := by
    intro T T' T'' a b
    refine (hbas T'').2.2.2 _ ?_
    have hpinv : L.p T'' ↑(v T T'' (a ≫ b))⁻¹ = ↑(u T T'' (a ≫ b))⁻¹ :=
      Units.eq_inv_of_mul_eq_one_left (by rw [← hvp, ← map_mul, Units.mul_inv, map_one])
    rw [← L.ker T'', map_sub, map_mul, map_mul, map_one, L.nat, hvp, hvp, hpinv, ← hu a b, Units.mul_inv, sub_self]
  choose z hzK hzσ using hz
  have heq : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''),
      L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'') := by
    intro T T' T'' a b
    rw [hzσ, add_sub_cancel, mul_assoc _ _ (v T T'' (a ≫ b) : L.B T''), Units.inv_mul, _root_.mul_one]
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add (f := _), k1, k2, k3, k4, sub_self, add_zero]
    · have m1 : L.ρ c (σ T'' (z T T' T'' a b)) ∈ I.map (algebraMap R (L.B T''')) := by
        rw [nat.1]; exact (hbas T''').1 _
      have m2 := (hbas T''').1 (z T T'' T''' (a ≫ b) c)
      have m3 := (hbas T''').1 (z T T' T''' a (b ≫ c))
      have m4 := (hbas T''').1 (z T' T'' T''' b c)
      have h12 := hmul T''' _ _ m1 m2
      have h43 := hmul T''' _ _ m4 m3
      have hA := congrArg (L.ρ c) (heq T T' T'' a b)
      rw [map_mul, map_mul, map_add (f := _), map_one] at hA
      have hB := heq T T'' T''' (a ≫ b) c
      have hC := heq T T' T''' a (b ≫ c)
      have hD := heq T' T'' T''' b c
      have hF := hL b c (v T T' a : L.B T')
      rw [Category.assoc] at hB
      rw [em, map_sub, map_add (f := _), map_add (f := _), ← nat.1]
      set E1 := L.ρ c (σ T'' (z T T' T'' a b))
      set E2 := σ T''' (z T T'' T''' (a ≫ b) c)
      set E3 := σ T''' (z T T' T''' a (b ≫ c))
      set E4 := σ T''' (z T' T'' T''' b c)
      set V := v T T''' (a ≫ b ≫ c)
      have hVW : (V : L.B T''') * ↑V⁻¹ = 1 := Units.mul_inv V
      have key1 : (1 + E1) * (1 + E2) * (V : L.B T''') = (1 + E4) * (1 + E3) * (V : L.B T''') := by
        linear_combination (-(1 + E1)) * hB - (v T'' T''' c : L.B T''') * hA + (1 + E4) * hC
          + L.ρ (b ≫ c) (v T T' a : L.B T') * hD
          - L.ρ c (v T' T'' b : L.B T'') * (v T'' T''' c : L.B T''') * hF
      have key2 : (1 + E1) * (1 + E2) = (1 + E4) * (1 + E3) := by
        linear_combination (↑V⁻¹ : L.B T''') * key1 - ((1 + E1) * (1 + E2) - (1 + E4) * (1 + E3)) * hVW
      linear_combination key2 - h12 + h43
  refine ⟨H2.mk _ ⟨_, hZ⟩, v, σ, ⟨_, hZ⟩, hvp, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, heq T T' T'' a b⟩⟩

end GlobalTheory.LBObs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCocycleLiftObstructionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitCocycleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  first | exact @GlobalTheory.LBObs.exists_isObU | exact GlobalTheory.LBObs.exists_isObU | (intros; apply GlobalTheory.LBObs.exists_isObU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiplicativeOneCocycleOpensOfIsLineBundleFra

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.FrameCoc

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCoc_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  intro X C _ V hV L u hL hF T T' T'' a b
  obtain ⟨τ, -, hτ⟩ := hF
  have key : ∀ m : L.ι, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (res (hV b) (u T T' a) * u T' T'' b) := by
    intro m
    have h1 := hτ T T'' (a ≫ b) m
    have h2 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (hτ T T' a m)
    have h3 := hτ T' T'' b m
    rw [res_res', map_mul, res_res', h3] at h2
    rw [h1] at h2
    apply mul_right_cancel (b := τ T'' m)
    rw [h2, map_mul, res_res', ← _root_.mul_assoc]
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun m => V T'' ⊓ L.U m) (V T'') (fun m => homOfLE inf_le_left) ?_ _ _ ?_
  · rw [← inf_iSup_eq, hL.cover, inf_top_eq]
  · intro m
    exact congrArg Units.val (key m)

end GlobalTheory.LBObs.FrameCoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiplicativeOneCocycleOpensOfIsLineBundleFraStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  first | exact @GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | exact GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame | (intros; apply GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstruction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.ObEx

theorem exists_isObL : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L hL
  obtain ⟨C, _, _, G, u, hB, hF⟩ := GlobalTheory.T.exists_lineBundle_frame_thin_affine_basis X₀ L hL
  have hc := GlobalTheory.T.isMultiplicativeOneCocycleOpens_of_isLineBundleFrameOnBasis X₀ C (opOf G) (opOf_le G) L u hL hF
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_unitCocycleLiftObstruction R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u
    ((ofSys_isFun S).restrict G) (fun T T' T'' a b ↦ congrArg Units.val (hc a b))
  obtain ⟨c, rfl⟩ := (GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X₀ s₀ C G hB.1 hB.2).2.2 d
  exact ⟨c, C, inferInstance, inferInstance, G, hB, u, hF, hd⟩

end GlobalTheory.LBObs.ObEx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstructionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  first | exact @GlobalTheory.LBObs.ObEx.exists_isObL | exact GlobalTheory.LBObs.ObEx.exists_isObL | (intros; apply GlobalTheory.LBObs.ObEx.exists_isObL <;> assumption)
end
end
