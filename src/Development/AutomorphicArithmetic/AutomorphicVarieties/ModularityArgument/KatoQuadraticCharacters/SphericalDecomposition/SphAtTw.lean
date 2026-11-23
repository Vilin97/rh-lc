module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrdinaryNormalFormUnramifiedSourceStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfVanishOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UnramifiedZeta.ZetaUr

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoConj

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.conj :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep r') := by
  intro l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk
  let f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l) :=
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]
  have hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ => rfl
  have hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x,
      Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ _ _ => rfl
  have hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x) := by
    intro g x
    rw [hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]
    congr 2
    group
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy
    rwa [hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩
    rw [hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcont : Continuous (fun g => f (c g)) := by
    simp only [hfa]
    exact continuous_const.matrix_mulVec hc.1
  have hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r) := by
    refine ⟨hcont, fun g g' => ?_⟩
    have h1 := congrArg f (hc.2 g g')
    simpa only [map_add (f := _), hf] using h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))
  obtain ⟨m', rfl⟩ := hsurj m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩
  have := hm g
  simp only [map_sub, hf]
  exact this
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdLOfZetaUr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem repIso_symm_srcL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W W' : R2 Ω l}
    (h : RepIso W W') : RepIso W' W := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, fun s => ?_⟩
  rw [hg s]
  group

theorem vanishOrdL_of_zetaUr : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ZetaUr → VanishOrdL := by
  intro hC hZ l _ hl Ω _ _ _ ι e he W hW hS
  obtain ⟨S, A, W', g, hiso, hnf, hsrc⟩ := GlobalTheory.T.exists_ordinary_normal_form_unramified_source l Ω ι e W hl he hW hS
  have hes : ES W' A := hZ l Ω ι e S A W' g hnf hsrc
  have hv : BlochKatoSelmerVanishes l (Loc.colRep W') := GlobalTheory.Ord2.es_vanish hC l Ω e S A W' hnf hes
  exact UpperTheory.V.X.Kato.conj l ℚ Ω 2 W' W (repIso_symm_srcL hiso) hv

end GlobalTheory.Ord2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphAtTw

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

private theorem sphAt_tw {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ι : Qbar l ≃+* ℂ} {e : ℕ} {W : R2 Ω l}
    (h : SphAt ι e W) {N : ℕ} {θ : G ℚ Ω →* (Qbar l)ˣ} (hN : 1 ≤ N) (hθ : KillsMu N θ) : SphAt ι e (Af.tw W θ) := by
  intro M φ hM hφ
  rw [TwDet.tw_tw]
  exact h (M * N) (φ * θ) (Nat.mul_pos hM hN)
    (TwDet.killsMu_mul (TwDet.killsMu_dvd hφ (dvd_mul_right M N)) (TwDet.killsMu_dvd hθ (dvd_mul_left N M)))

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twoS :
    GlobalTheory.Mem.LiteralAutomorphy.LitCoh → SrcS → KatoTwoS := by
  intro hC hSrc l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hS
  have hV : VanishOrdL := GlobalTheory.Ord2.vanishOrdL_of_zetaUr hC Final.zetaUr
  obtain ⟨hdt, ha⟩ := u.adm hf
  have h1 : Af.tw W 1 = W := by
    ext s i j
    change mat (Af.tw W 1) s i j = mat W s i j
    rw [TwDet.tw_coe]
    simp
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hV l u.l_odd Ω ι e u.e_pos W ha (hSrc l Ω ι e W u.l_odd u.e_pos ha hS)
  · rw [← hdt]
    obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (TwDet.ker_open ha.cont ha.det2)
      (Abelianization.commutator_subset_ker (dt W))
    have ha' := admissible_twist_by_det l Ω ι e W ha
    exact hV l u.l_odd Ω ι e u.e_pos _ ha'
      (hSrc l Ω ι e _ u.l_odd u.e_pos ha' (sphAt_tw hS hM fun s hs => hMk s hs))
end
end
