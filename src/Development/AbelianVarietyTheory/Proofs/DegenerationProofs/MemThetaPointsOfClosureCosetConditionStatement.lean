module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTateIsoZetaEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPointStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCosetStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfield

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ThetaDescent

theorem exists_full_of_theta_in_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  intro hv h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K κ _ _ _ _ _ i m ρ z v o' hm _ hρ hz hth
  haveI := c.fin
  have hr : H.rt0 ∈ c.F := c.le (baseKA l).ρ.2
  have hζ : zeta l.A ∈ c.F := c.le (baseKA l).ζ.2
  obtain ⟨b, hb⟩ := exists_embedding H c.F hr ρ (i.injective (by rw [map_pow, ← hρ, o'.ρ_sq, map_neg, map_natCast]))
  have hp : IsPrimitiveRoot (i (b ⟨_, hζ⟩)) l.A :=
    ((IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (ζ := ⟨_, hζ⟩)
      (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective).map_of_injective
        b.injective).map_of_injective i.injective
  obtain ⟨I, hI⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l κ _ _ _ o'.I l.A _ l.A_pos hp
  obtain ⟨y, ⟨hy, φ, h₁, h₂, h₃, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hv h6 hU hX hT hE hA E H D l Xo c W₀ Y κ (i.comp b)).1
    { o' with I := I } (fun r h => by
      obtain rfl : r = ⟨_, hr⟩ := Subtype.ext h
      exact hρ.trans (congrArg i hb.symm)) (fun r h => by
      obtain rfl : r = ⟨_, hζ⟩ := Subtype.ext h
      exact hI)
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨o, h₄, h₅⟩ := exists_full hv.1.1 hv.1.2.1.secBaseChangeAny (pullback.snd _ _)
    (IntermediateField.inclusion c.le).toRingHom pullback.condition Y.oF b i y hy o' φ h₁ h₂ h₃ m hm z v hz hth
  exact ⟨o, h₄.trans hb, h₅⟩

end GlobalTheory.Ex.ThetaDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  first | exact @GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | exact GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | (intros; apply GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPointStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_specialisation_with_thetaPoint : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C], (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) → ∀ (o : Full D C) (M : Mdl o), IsProper M.t.G.hom → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (res : S →+* κ), (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) → ∀ (m : ℕ) (v : D.La → S), Odd m → 3 ≤ m → o.Theta m (fun x => v x) → (∃ x, res (v x) ≠ 0) → ∃ o' : Full D κ, (∀ r : S, (r : C) = o.ρ → o'.ρ = res r) ∧ (∀ n, 0 < n → ∀ z : S, (z : C) = o.I.ζ n → (o'.I.ζ n : κ) = res z) ∧ o'.Theta m fun x => res (v x) := by
  first | exact @GlobalTheory.Ex.Specialise.exists_specialisation | exact GlobalTheory.Ex.Specialise.exists_specialisation | (intros; apply GlobalTheory.Ex.Specialise.exists_specialisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetCondition

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ClosurePoint

theorem exists_full_of_closure_of_cosets :
    HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y K _ _ _ n j ρ z v hn hodd hj hc hvan hcos
  have hm : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  have hm3 : 3 ≤ n ^ j := hn3.trans (Nat.le_self_pow (by omega) n)
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hcos 0
    exact hx (by rw [h]; rfl)
  obtain ⟨C, _, _, _, _, _, S, κ, _, _, res, i, o, M, v', r', z', hnorm, hS, hres, hth, hv', hr', hρ,
    hz', hz⟩ := GlobalTheory.T.exists_trait_specialisation_of_mem_closure_thetaPoints h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K (n ^ j) ρ z v hm hc hv0 hvan
  have hunit : ∀ x, v x ≠ 0 → ‖(v' x : C)‖ = 1 := by
    intro x hx
    have hle : ‖(v' x : C)‖ ≤ 1 := (hS _).1 (v' x).2
    by_contra hne
    have h0 := hres (v' x) (lt_of_le_of_ne hle hne)
    rw [hv' x] at h0
    exact hx (i.injective (by rw [h0, map_zero]))
  have hprop : IsProper M.t.G.hom :=
    GlobalTheory.T.isProper_of_theta_unit_in_every_coset h1 h2 h3 h4 h5 h6 h7 E H D C o M n j hn hodd (hnorm n hn.pos) hj
      (fun x => v' x) hth (fun x => (hS _).1 (v' x).2)
      (fun x => (hcos x).imp fun h hh => hunit _ hh)
  obtain ⟨o', hρ', hζ', hth'⟩ := GlobalTheory.T.exists_specialisation_with_thetaPoint h1 h2 h3 h4 h5 h6 h7 E H D C hnorm o M hprop S hS κ res
    hres (n ^ j) v' hm hm3 hth (by
      obtain ⟨x, hx⟩ := hcos 0
      exact ⟨_, by rw [hv']; exact (map_ne_zero i).2 hx⟩)
  refine GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K κ i (n ^ j) ρ z v o' hm hc
    ((hρ' r' hr').trans hρ) ((hζ' _ (by positivity) z' hz').trans hz) ?_
  have : (fun x => res (v' x)) = fun x => i (v x) := funext hv'
  rwa [this] at hth'

end GlobalTheory.Ex.ClosurePoint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetConditionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  first | exact @GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | exact GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | (intros; apply GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets <;> assumption)
end
end
