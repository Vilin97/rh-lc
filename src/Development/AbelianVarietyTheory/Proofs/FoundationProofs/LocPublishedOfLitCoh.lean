module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Formalism.ConjugateSelfDual.Statement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrictStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerVanishesOfDualVanishesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiterature

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

theorem _root_.GlobalTheory.T.crystallineClass_restrict_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  first | exact @GlobalTheory.Ord2.bk_locEmb | exact GlobalTheory.Ord2.bk_locEmb | (intros; apply GlobalTheory.Ord2.bk_locEmb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeightStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

theorem _root_.GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w → ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  first | exact @GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | exact GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight | (intros; apply GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertia

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertiaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

theorem _root_.GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m → (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) → Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  first | exact @GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | exact GlobalTheory.hasWeight_neg_of_pow_cyc_inertia | (intros; apply GlobalTheory.hasWeight_neg_of_pow_cyc_inertia <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinary

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  first | exact @GlobalTheory.Ord2.bk_unr_gr | exact GlobalTheory.Ord2.bk_unr_gr | (intros; apply GlobalTheory.Ord2.bk_unr_gr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiteratureStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.strict_vanishing_dual_of_literature : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.StrictKill.main | exact GlobalTheory.Ord2.StrictKill.main | (intros; apply GlobalTheory.Ord2.StrictKill.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocPublishedOfLitCoh

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem localGaloisCohomology_of_galoisCohomology (h : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) : Loc.LocalPublishedTheorems :=
  ⟨h.lfK, h.ltK, h.leK, h.lf, h.lt, h.le, h.bk⟩

theorem es_vanish : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → BlochKatoSelmerVanishes l (Loc.colRep W) := by
  intro hLit l _ Ω _ _ _ e S A W hNf hES c hc hBK
  have hStr : StrZero (dual1 W) A := GlobalTheory.T.strict_vanishing_dual_of_literature hLit l Ω e S A W hNf hES
  have hGrD : GrZero (dual1 W) A := GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict hLit l Ω e S A W hNf hES hStr
  have hGr : GrZero W A := GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes hLit l Ω e S A W hNf hGrD
  obtain ⟨hU, hG⟩ := GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary (localGaloisCohomology_of_galoisCohomology hLit) l Ω e S A W hNf c hc hBK
  exact hGr c hc hU hG

end GlobalTheory.Ord2
end
end
