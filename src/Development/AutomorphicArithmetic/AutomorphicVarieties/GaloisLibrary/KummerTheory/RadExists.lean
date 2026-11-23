module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.Linter.Style
public import Mathlib.FieldTheory.Galois.Infinite

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HilbertNinety

section

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g

    rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Imports

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.h90 :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (f : G K Ω → Ω), IsLocallyConstant f → (∀ g, f g ≠ 0) → (∀ g h, f (g * h) = f g * g (f h)) → ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β :=
  _root_.UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radExists :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n), IsPrimitiveRoot ζ n → (∀ g : G K Ω, g ζ = ζ ^ (η g).val) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + η g * z h) →
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  intro K Ω _ _ _ _ _ n _ ζ η z hζ hη hz hc
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := UpperTheory.V.Kum.h90 K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n hβ0 ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩
end
end
