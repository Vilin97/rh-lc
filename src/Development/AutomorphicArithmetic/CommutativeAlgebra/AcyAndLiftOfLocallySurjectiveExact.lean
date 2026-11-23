module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveClHypercohomologySingletonZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Mathlib.Algebra.Order.Star.Int
import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.AcyRightOfShortExact

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_right_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₂ → Acy Q S.X₃ := by
  intro Q S hS h1 h2 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).2.1
  haveI := h1 P hP (n + 1) (by omega)
  haveI := h2 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₃ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToKernelOfShortExactVanishingSecti

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → (∀ U : Scheme.{0}, Q U → Subsingleton (Sec S.X₃ U)) → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₂, ∃ h : (free ℤ).obj P ⟶ S.X₁, h ≫ S.f = f := by
  intro Q S hS hQ P hP f
  have hsub := UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q S.X₃ hQ P hP 0
  have hz : f ≫ S.g = 0 := by
    apply (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1
    exact Subsingleton.elim _ _
  haveI := hS.mono_f
  exact ⟨hS.exact.lift f hz, hS.exact.lift_f f hz⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.HypercohomologyPostClEqClComp

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToMiddleOfShortExactAcy

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_middle_of_shortExact_acy :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₃, ∃ h : (free ℤ).obj P ⟶ S.X₂, h ≫ S.g = f := by
  intro Q S hS hA P hP f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) 0).2.1
  have hsub := hA P hP (0 + 1) (by norm_num)
  have h0 : HK.ext ℤ (sgl ((free ℤ).obj P)) z 0 (0 + 1) rfl (cl f) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (e (cl f)).1 h0
  obtain ⟨h, rfl⟩ := (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).2 y
  refine ⟨h, (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1 ?_⟩
  rw [← UpperTheory.hypercohomology_post_cl_eq_cl_comp]
  exact hy
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.AcyAndLiftOfLocallySurjectiveExact

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem restriction_trans {F : Shv ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

private theorem res_map_of_sheaf_morphism {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U) (b : Sec F U) :
    Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem map_map_eq_zero {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) (h : φ ≫ ψ = 0) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = 0 := by
  have h2 := congrArg (fun t : F ⟶ H => (t.hom.app (op U)).hom a) h
  simpa [Sec.map] using h2

private theorem local_bind {U : Scheme.{0}} {P R : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => R W (k ≫ g)) : Loc U R := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose T hT hTR using fun (V : Scheme.{0}) (g : V ⟶ U) (H : S.arrows g) => h V g (hSP V g H)
  refine ⟨Sieve.bind S.arrows fun Y f H => T Y f H, ?_, ?_⟩
  · exact Scheme.etaleTopology.bind_covering hS fun Y f H => hT Y f H
  · rintro W _ ⟨Y, k, g, H, hk, rfl⟩
    exact hTR Y g H W k hk

theorem UpperTheory.acy_and_lift_of_locally_surjective_exact :
    ∀ (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → ∀ (A C₁ Z : Shv ℤ) (i : A ⟶ C₁) (d : C₁ ⟶ Z) (w : i ≫ d = 0), Mono i → (ShortComplex.mk i d w).Exact → (∀ U : Scheme.{0}, Q U → ∀ b : Sec Z U, Loc U fun V g => ∃ a : Sec C₁ V, Sec.map d a = Sec.res g b) → Acy Q A → Acy Q C₁ → Acy Q Z ∧ ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ Z, ∃ h : (free ℤ).obj P ⟶ C₁, h ≫ d = f := by
  intro Q hQ A C₁ Z i d w hi hex hloc hA hC
  have hfac : Abelian.factorThruImage d ≫ Abelian.image.ι d = d := Abelian.image.fac d
  have w1 : i ≫ Abelian.factorThruImage d = 0 := by
    rw [← cancel_mono (Abelian.image.ι d), Category.assoc, hfac, w, zero_comp]
  let S1 := ShortComplex.mk i (Abelian.factorThruImage d) w1
  have hS1ex : S1.Exact := by
    let φ : S1 ⟶ ShortComplex.mk i d w :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι d
        comm₁₂ := by simp [S1]
        comm₂₃ := by simp [S1, hfac] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  have hS1 : S1.ShortExact := { exact := hS1ex, mono_f := hi, epi_g := by dsimp [S1]; infer_instance }
  have w2 : Abelian.image.ι d ≫ cokernel.π d = 0 := by
    rw [← cancel_epi (Abelian.factorThruImage d), ← Category.assoc, hfac, cokernel.condition, comp_zero]
  let S2 := ShortComplex.mk (Abelian.image.ι d) (cokernel.π d) w2
  have hS2 : S2.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := by dsimp [S2]; infer_instance
      epi_g := by dsimp [S2]; infer_instance }
  have hsub : ∀ U : Scheme.{0}, Q U → Subsingleton (Sec (cokernel d) U) := by
    intro U hU
    refine ⟨fun s t => ?_⟩
    have hz : ∀ s : Sec (cokernel d) U, s = 0 := by
      intro s
      have hl := ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (cokernel.π d)).2.2.1.1 inferInstance) U s
      have hl2 : Loc U fun W k => Sec.res k s = Sec.res k (0 : Sec (cokernel d) U) := by
        refine local_bind hl ?_
        rintro V g ⟨z, hz⟩
        obtain ⟨T, hT, hTz⟩ := hloc V (hQ g hU) z
        refine ⟨T, hT, ?_⟩
        rintro W k hk
        obtain ⟨a, ha⟩ := hTz W k hk
        rw [restriction_trans, ← hz, res_map_of_sheaf_morphism, ← ha, map_map_eq_zero d (cokernel.π d) (cokernel.condition d)]
        simp [Sec.res]
      exact (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ (cokernel d) U).1 s 0 hl2
    rw [hz s, hz t]
  have hI : Acy Q (Abelian.image d) := UpperTheory.acy_right_of_shortExact Q S1 hS1 hA hC
  have hK : Acy Q (cokernel d) := fun P hP n _ => UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q _ hsub P hP n
  refine ⟨UpperTheory.acy_middle_of_shortExact Q S2 hS2 hI hK, ?_⟩
  intro P hP f
  obtain ⟨h1, hh1⟩ := UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections Q S2 hS2 hsub P hP f
  obtain ⟨h2, hh2⟩ := UpperTheory.exists_lift_free_to_middle_of_shortExact_acy Q S1 hS1 hA P hP h1
  refine ⟨h2, ?_⟩
  dsimp [S1, S2] at hh1 hh2
  rw [← hfac, ← Category.assoc, hh2, hh1]
end
end
