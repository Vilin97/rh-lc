module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleEqChainMapShiftCompatClassesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamilyStatement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyI

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.cone_kinj_and_bijective_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ),
    D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) →
    (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R,
      ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  intro R _ D C f m hD hC iD iC
  refine ⟨?_, ?_⟩
  · haveI : ∀ n, Injective ((mappingCone f).X n) := fun n =>
      Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
        (@Injective.instBiprod _ _ _ _ _ _ (iD (n + 1)) (iC n))
    haveI : (mappingCone f).IsStrictlyGE (m - 1) := CochainComplex.isStrictlyGE_mappingCone f m m (m - 1) (by omega)
    exact isKInjective_of_injective _ (m - 1)
  · intro K
    have ex := fun n => GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f n
    constructor
    · intro hb n
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ x : CohomologyClass K (mappingCone f) n, x = 0 := by
        intro x
        have h1 : cpush K f (n + 1) (cpost K (mappingCone.fst f) n (n + 1) rfl x) = 0 :=
          ((ex n).2.2 _).2 ⟨x, rfl⟩
        have h2 : cpost K (mappingCone.fst f) n (n + 1) rfl x = 0 :=
          (hb (n + 1)).1 (by rw [h1, map_zero])
        obtain ⟨y, rfl⟩ := ((ex n).2.1 x).1 h2
        obtain ⟨z, rfl⟩ := (hb n).2 y
        exact ((ex n).1 _).2 ⟨z, rfl⟩
      rw [h0 x, h0 y]
    · intro hs n
      refine ⟨?_, fun y => ?_⟩
      · rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by ring⟩
        obtain ⟨w, rfl⟩ := ((ex k).2.2 z).1 hz
        rw [Subsingleton.elim w 0, map_zero]
      · exact ((ex n).1 y).1 (Subsingleton.elim _ _)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyIStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R, ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  first | (exact @GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (exact GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (intros; apply GlobalTheory.EtC.cone_kinj_and_bijective_iff  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClasses

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SchLocExact

variable {R : Type} [CommRing R]

theorem map_res {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map ψ (Sec.res g x) = Sec.res g (Sec.map ψ x) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => f.hom x) (ψ.hom.naturality g.op)

theorem map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem res_res {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  simp [Sec.res]

theorem res_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem subsingleton_of_homotopyEquiv {K L M : Cx R} (e : HomotopyEquiv K L) (n : ℤ)
    (h : Subsingleton (CohomologyClass L M n)) : Subsingleton (CohomologyClass K M n) := by
  suffices H : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (H x).trans (H y).symm⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h0 : cpull e.inv M n (CohomologyClass.mk α) = 0 := Subsingleton.elim _ _
  have key : cpull e.hom M n (cpull e.inv M n (CohomologyClass.mk α)) = CohomologyClass.mk α := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom e.hom) (zcomp (Cocycle.ofHom e.inv) α (zero_add n)) (zero_add n)) =
      CohomologyClass.mk α
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨n.negOnePow • (Cochain.ofHomotopy e.homotopyHomInvId).comp α.1 (by omega), ?_⟩
    rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
    ext p q hpq
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq, smul_smul]
  rw [← key, h0, map_zero]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ m' hm] at h0
  exact h0

end GlobalTheory.EtC.SchLocExact


open GlobalTheory.EtC.SchLocExact in
theorem GlobalTheory.EtC.sch_loc_exact : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}),
    (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U),
    Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  intro R _ M U hU n b hb
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  have hs : Subsingleton (CohomologyClass (sgl ((free R).obj (yoneda.obj U))) M n) :=
    subsingleton_of_homotopyEquiv (e (yoneda.obj U)) n (hU n)
  obtain ⟨hex, -, -, -⟩ := GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X n)
  obtain ⟨φ, hφ⟩ := hex (fun V x => Sec.res x b) (fun V W g x => res_res g x b)
  have hφd : φ ≫ M.d n (n + 1) = 0 := by
    apply (GlobalTheory.EtC.free_hom_sections R (yoneda.obj U) (M.X (n + 1))).2.1
    intro W x
    rw [map_comp, hφ, map_res, hb]
    simp [Sec.map, Sec.res]
  obtain ⟨ψ, hψ⟩ := lift_of_subsingleton (m' := n - 1) (by omega) hs φ hφd
  let a0 : Sec (M.X (n - 1)) U := Sec.map ψ (freeGen R (yoneda.obj U) U (𝟙 U))
  have ha0 : Sec.map (M.d (n - 1) n) a0 = b := by
    simp only [a0]
    rw [← map_comp, hψ, hφ, res_id]
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g a0, ?_⟩⟩
  rw [map_res, ha0]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsComplexExactEtaleLocallyOfNoClassesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes : ∀ (R : Type) [CommRing R] (M : Cx R) (U : Scheme.{0}), (∀ n, Subsingleton (CohomologyClass ((chains R).obj (sch.obj U)) M n)) → ∀ (n : ℤ) (b : Sec (M.X n) U), Sec.map (M.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (M.X (n - 1)) V, Sec.map (M.d (n - 1) n) a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.sch_loc_exact) | (exact GlobalTheory.EtC.sch_loc_exact) | (intros; apply GlobalTheory.EtC.sch_loc_exact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexMapQuasiIsoOfUnitSchemes

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.DiscSupp

theorem assemble : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) (n - d j)) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j) := by
  intro R _ ι _ L C d ψ m₀ hL hLi
  choose L' g hb hi he using fun j => GlobalTheory.T.cocycle_eq_chainMap_shift_compat_classes R (L j) C (d j) (ψ j)
  choose e he using he
  have hm : ∀ j, (L' j).IsStrictlyGE (m₀ - ∑ k, |d k|) := fun j => by
    haveI := hb j m₀ (hL j)
    refine isStrictlyGE_of_ge (L' j) _ (m₀ + d j) ?_
    have h1 : |d j| ≤ ∑ k, |d k| := Finset.single_le_sum (f := fun k => |d k|) (fun k _ => abs_nonneg (d k)) (Finset.mem_univ j)
    have h2 := neg_abs_le (d j)
    omega
  obtain ⟨D, f, hD, hDi, hs⟩ := GlobalTheory.T.exists_biproduct_chainMap_of_injective_family R L' C g (m₀ - ∑ k, |d k|) hm (fun j => hi j (hLi j))
  refine ⟨D, f, _, hD, hDi, fun K n => ?_⟩
  obtain ⟨e', he'⟩ := hs K n
  refine ⟨(Equiv.piCongrRight fun j => e j K n).trans e', fun a => ?_⟩
  simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, he']
  exact Finset.sum_congr rfl fun j _ => he j K n (a j)

theorem bijective_disc : ∀ (q : ℕ) [NeZero q] {ι : Type} [Fintype ι] (L : ι → Cx (ZMod q)) (C : Cx (ZMod q)) (d : ι → ℤ) (ψ : ∀ j, Cocycle (L j) C (d j)) (m₀ : ℤ), (∀ j, (L j).IsStrictlyGE m₀) → C.IsStrictlyGE m₀ → (∀ j n, CategoryTheory.Injective ((L j).X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (sch.obj U)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j)) → ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) (L j) (n - d j) => ∑ j, cpost _ (ψ j) (n - d j) n (by omega) (a j) := by
  intro q _ ι _ L C d ψ m₀ hL hC hLi hCi hU F hF
  obtain ⟨D, f, m, hD, hDi, he⟩ := assemble (ZMod q) L C d ψ m₀ hL hLi
  have hD' : D.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge D _ _ (min_le_left _ _)
  have hC' : C.IsStrictlyGE (min m m₀) := isStrictlyGE_of_ge C _ _ (min_le_right _ _)
  obtain ⟨hKI, hcone⟩ := GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff (ZMod q) f (min m m₀) hD' hC' hDi hCi
  have key : ∀ K : Cx (ZMod q), (∀ n : ℤ, Function.Bijective fun a : ∀ j, CohomologyClass K (L j) (n - d j) =>
      ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n) := by
    intro K
    rw [← hcone K]
    refine forall_congr' fun n => ?_
    obtain ⟨e, he'⟩ := he K n
    have : (fun a : ∀ j, CohomologyClass K (L j) (n - d j) => ∑ j, cpost K (ψ j) (n - d j) n (by omega) (a j)) =
        (cpush K f n) ∘ e := funext fun a => (he' a).symm
    rw [this]
    exact Function.Bijective.of_comp_iff _ e.bijective
  refine (key _).mpr ?_
  exact GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support (ZMod q) (disc.obj F) (mappingCone f) (fun U hU' n b hb =>
    GlobalTheory.T.sectionsComplex_exact_etaleLocally_of_no_classes (ZMod q) (mappingCone f) U ((key _).mp (hU U (hF U hU'))) n b hb)

end GlobalTheory.EtC.DiscSupp

end
end
end
