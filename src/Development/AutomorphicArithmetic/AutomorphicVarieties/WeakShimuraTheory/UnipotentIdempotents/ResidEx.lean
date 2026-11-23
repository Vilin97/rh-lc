module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CbFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.WtRoot

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Descend

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (M : Type) [Group M] (χ : G L Ω →* M), IsOpen (χ.ker : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ χ.ker) → ∃ χ' : V.frame.G₀ →* M, IsOpen (χ'.ker : Set V.frame.G₀) ∧ ∀ g, χ' (V.pr g) = χ g := by
  intro l _ L Ω _ _ _ _ _ _ s V M _ χ hopen hine
  obtain ⟨hsurj, hquot, hker⟩ := phiKer V
  have hle : V.pr.ker ≤ χ.ker := hker χ.ker (Subgroup.isClosed_of_isOpen _ hopen) hine
  let χ₀ : ↥V.η.ker →* M :=
    (QuotientGroup.lift V.pr.ker χ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm.toMonoidHom
  have hcomp : ∀ g, χ₀ (V.pr g) = χ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm (V.pr g) =
        (QuotientGroup.mk g : G L Ω ⧸ V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hpre : (V.pr : G L Ω → ↥V.η.ker) ⁻¹' (χ₀.ker : Set ↥V.η.ker) = (χ.ker : Set (G L Ω)) := by
    ext g
    simp [MonoidHom.mem_ker, hcomp]
  have hop : IsOpen (χ₀.ker : Set ↥V.η.ker) := hquot.isOpen_preimage.mp (hpre ▸ hopen)
  exact ⟨χ₀, hop, hcomp⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.StarOp

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (χ : Fin n → F.G₀ →* Rˣ) (π : Equiv.Perm (Fin n)), (∀ i g, χ i (F.conj g) * χ (π i) g * F.eps O R g ^ ((n : ℤ) - 1) = 1) → F.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
  intro l _ F O _ _ R _ _ n χ π hχ B _ _ _ _ y
  let Ψ : Fin n → MonoidAlgebra B F.G₀ →ₐ[B] B := fun i =>
    MonoidAlgebra.lift B B F.G₀ ((Units.coeHom B).comp (W.pushCh (algebraMap R B) (χ i)))
  have hrep : ∀ z, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => Ψ i z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
      congr 1
      funext i
      rw [map_add (f := _)]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, Ψ]
      ext i j
      simp [W.diagRep, W.pushCh, Matrix.diagonal_apply]
  have hst : ∀ i z, Ψ i (F.star O B n z) = Ψ (π i) z := by
    intro i z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single g b =>
      simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, Ψ]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, map_smul,
        MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, W.pushCh, Units.coe_map,
        smul_eq_mul]
      congr 1
      have he : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O R B]
      have key : F.eps O R g ^ (1 - (n : ℤ)) * χ i (F.conj g)⁻¹ = χ (π i) g := by
        have h := hχ i g
        have hb : χ (π i) g = ((χ i) (F.conj g) * F.eps O R g ^ ((n : ℤ) - 1))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_left_comm, ← mul_assoc]
          exact h
        rw [hb, mul_inv, show (1 : ℤ) - n = -((n : ℤ) - 1) by ring, zpow_neg, map_inv, mul_comm]
      rw [he, ← map_zpow, Units.coe_map, ← key, Units.val_mul]
      simp
  show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (F.star O B n y)) =
    Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
  rw [hrep, hrep, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [hst]
  exact Equiv.prod_comp π (fun i => Ψ i y)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.ResidEx

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.residEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → T.Ok → V.S' = Y.s.S → ∃ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) ∧ (∀ (v : W.Vl l T.L) i (g : Dec (F := T.L) (Y.s.A v)), r.psib v i g = r.chib i (V.pr g)) ∧ (∀ v i, r.th v i = 1) := by
  intro Ω _ _ _ l _ c D T c' h X Y V hG hT hS
  have hcb := cbFacts X hG
  have hpr := prFacts l T.L Ω Y.s V
  have hd : ∀ i, ∃ χ : V.η.ker →* (ResidueField c'.O)ˣ, IsOpen (χ.ker : Set V.η.ker) ∧
      ∀ g, χ (V.pr g) = X.cb i g := fun i =>
    descend l T.L Ω Y.s V _ (X.cb i) (hcb.1 i)
      (fun A v hA hv => hcb.2.1 i A (Y.away A v hA (by rwa [hS] at hv)))
  choose χ hχo hχ using hd
  have hinj : Function.Injective χ := by
    intro i j hij
    apply cbInj X hT
    exact MonoidHom.ext fun g => by rw [← hχ, ← hχ, hij]
  have hpol : V.frame.IsPolar c'.O (W.GDet.ofRep (W.diagRep χ)) := by
    apply polar V.frame c'.O (ResidueField c'.O) 4 χ Fin.revPerm
    intro i g
    obtain ⟨g1, rfl⟩ := hpr.1 g
    obtain ⟨g', hg', hconj⟩ := hpr.2.1 g1
    obtain ⟨σ, hσ, hσc⟩ := Y.cc
    have key := hcb.2.2 σ hσ g1 g' (hσc g1 g' hg') i
    have heps := hpr.2.2.1 c'.O (ResidueField c'.O) g1
    rw [hconj]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Fin.revPerm_apply]
    erw [hχ i g', hχ i.rev g1, heps, IsLocalRing.ResidueField.algebraMap_eq]
    have e3 : ((4 : ℕ) : ℤ) - 1 = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, zpow_natCast]
    exact key
  refine ⟨W.Resid.mk χ hχo hinj hpol (fun v i => (χ i).comp (V.frame.φ v)) ?_ (fun _ _ => 1)
    (fun _ _ _ _ => rfl), fun i g => hχ i g, fun v i g => rfl, fun v i => rfl⟩
  intro v i
  exact (hχo i).preimage (V.frame.φ_cont v)
end
end
