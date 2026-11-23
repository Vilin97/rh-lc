module

public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteContinuousCrossedHomomorphismsStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensionsStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1OfFiniteCrossedHoms

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Glob

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

noncomputable def oneCochainFun {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) : G → A.V :=
  fun g => c.1 (fun _ => g)

theorem oneCochainFun_injective {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) : Function.Injective (oneCochainFun A) := by
  intro c c' h
  apply Subtype.ext
  funext x
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hx]
  exact congrFun h (x 0)

theorem oneCochainFun_isLocallyConstant {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    (A : Rep.{0} k G) (c : locallyConstantCochains A 1) :
    IsLocallyConstant (oneCochainFun A c) := by
  have hc : IsLocallyConstant (c : (Fin 1 → G) → A) := c.2
  exact hc.comp_continuous (continuous_pi fun _ => continuous_id)

theorem oneCochainFun_cocycle {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] (c : locallyConstantCochains A 1)
    (hc : (dLocallyConstant A 1).hom c = 0) (g h : G) :
    oneCochainFun A c (g * h) = oneCochainFun A c g + A.ρ g (oneCochainFun A c h) := by
  have key : A.ρ g ((c : (Fin 1 → G) → A) (fun i => ![g, h] i.succ)) +
      ∑ j : Fin 2, (-1 : k) ^ ((j : ℕ) + 1) •
        (c : (Fin 1 → G) → A) (Fin.contractNth j (· * ·) ![g, h]) = 0 := by
    have h1 := congrFun (congrArg Subtype.val hc) ![g, h]
    rw [dLocallyConstant_hom_apply] at h1
    exact h1
  rw [Fin.sum_univ_two] at key
  have e1 : (fun i : Fin 1 => ![g, h] i.succ) = fun _ => h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e2 : Fin.contractNth (0 : Fin 2) (· * ·) ![g, h] = fun _ => g * h := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have e3 : Fin.contractNth (1 : Fin 2) (· * ·) ![g, h] = fun _ => g := funext fun i => by
    rw [Subsingleton.elim i 0]
    rfl
  have p0 : (-1 : k) ^ (((0 : Fin 2) : ℕ) + 1) = -1 := by
    show (-1 : k) ^ 1 = -1
    exact pow_one _
  have p1 : (-1 : k) ^ (((1 : Fin 2) : ℕ) + 1) = 1 := by
    show (-1 : k) ^ 2 = 1
    exact neg_one_sq
  rw [e1, e2, e3, p0, p1, neg_one_smul, one_smul] at key
  show (c : (Fin 1 → G) → A) (fun _ => g * h) =
    (c : (Fin 1 → G) → A) (fun _ => g) + A.ρ g ((c : (Fin 1 → G) → A) (fun _ => h))
  rw [← sub_eq_zero, ← neg_eq_zero, ← key]
  abel

theorem finite_cohomology_one_of_finite_cocycles :
    ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (A : Rep.{0} k G) [IsDiscreteRep A],
      {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite →
        Finite (cohomology A 1) := by
  intro k G _ _ _ _ A _ hfin
  have hd : ∀ z : (cochainsComplex A).cycles 1,
      (dLocallyConstant A 1).hom (((cochainsComplex A).iCycles 1).hom z) = 0 := by
    intro z
    have h1 : (cochainsComplex A).iCycles 1 ≫ (cochainsComplex A).d 1 (1 + 1) = 0 :=
      (cochainsComplex A).iCycles_d 1 (1 + 1)
    rw [cochainsComplex_d] at h1
    exact congrArg (fun φ => φ.hom z) h1
  have hinj : Function.Injective ((cochainsComplex A).iCycles 1).hom :=
    (ModuleCat.mono_iff_injective ((cochainsComplex A).iCycles 1)).1 inferInstance
  have hS : ∀ z : (cochainsComplex A).cycles 1,
      oneCochainFun A (((cochainsComplex A).iCycles 1).hom z) ∈
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)} :=
    fun z => ⟨oneCochainFun_isLocallyConstant A _, oneCochainFun_cocycle A _ (hd z)⟩
  have hFin : Finite ((cochainsComplex A).cycles 1) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun z => (⟨_, hS z⟩ :
        {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}))
      (fun z₁ z₂ hz => hinj (oneCochainFun_injective A (congrArg Subtype.val hz)))
  have hepi : Epi ((cochainsComplex A).homologyπ 1) := inferInstance
  have hsurj : Function.Surjective ((cochainsComplex A).homologyπ 1).hom :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex A).homologyπ 1)).1 hepi
  exact Finite.of_surjective _ hsurj

end GlobalTheory.CompanionTheory.Glob
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1OfFiniteCrossedHomsStatement

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finite_H1_of_finite_crossed_homs : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite → Finite (cohomology A 1) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | exact GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Glob.finite_cohomology_one_of_finite_cocycles <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem openSubgroups_finite_of_fields_finite :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))

end GlobalTheory.CompanionTheory.GlobalFiniteness
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndexStatement

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem _root_.GlobalTheory.T.finitely_many_open_subgroups_bounded_index : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))), (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧ Module.finrank F E ≤ N}.Finite) → ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) | IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | exact GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.openSubgroups_finite_of_fields_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutside

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GSFin

theorem finite_cohomology_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 1) := by
  intro F Ω _ _ _ _ _ l _ r S _ A _ hA _
  exact GlobalTheory.T.finite_H1_of_finite_crossed_homs _ _ A (GlobalTheory.T.finite_continuous_crossed_homomorphisms _ _ A hA (GlobalTheory.T.finitely_many_open_subgroups_bounded_index F Ω _ (GlobalTheory.T.hermite_finitely_many_unramified_extensions F Ω S)))

end GlobalTheory.CompanionTheory.GSFin
end
end
