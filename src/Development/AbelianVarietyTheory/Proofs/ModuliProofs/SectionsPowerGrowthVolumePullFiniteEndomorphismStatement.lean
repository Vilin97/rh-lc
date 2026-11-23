module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TendstoOfSandwich
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Mathlib.AlgebraicGeometry.QuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGlobalSectionsFunctionFieldIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def gen (U : X.Opens) (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U _ h).hom

theorem generic_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hx⟩

theorem gen_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    gen V hV (rs X h a) = gen U (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem gen_injective (U : X.Opens) (h : genericPoint X ∈ U) : Function.Injective (gen U h) :=
  germ_injective_of_isIntegral X _ h

theorem eq_of_gen {U : X.Opens} {a b : Γ(X, U)} (h : ∀ hU, gen U hU a = gen U hU b) : a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact gen_injective U hU (h hU)
  · have hb : U = ⊥ := by
      ext x
      exact ⟨fun hx => (hU (generic_mem hx)).elim, fun hx => hx.elim⟩
    subst hb
    exact Subsingleton.elim _ _

theorem exists_gen_eq (U : X.Opens) (f : X.functionField)
    (hf : ∀ x ∈ U, ∃ (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)), gen V (generic_mem hx) a = f) :
    ∃ a : Γ(X, U), ∀ hU, gen U hU a = f := by
  choose V hx a ha using hf
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => U ⊓ V x.1 x.2) U
    (fun x => homOfLE inf_le_left)
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hxU, hx x hxU⟩)
    (fun x => rs X inf_le_right (a x.1 x.2))
    (fun x y => eq_of_gen (X := X) fun h =>
      ((gen_rs inf_le_left h _).trans ((gen_rs _ _ _).trans (ha _ _))).trans
        ((gen_rs inf_le_right h _).trans ((gen_rs _ _ _).trans (ha _ _))).symm)
  refine ⟨s, fun hU => ?_⟩
  have h1 : rs X (inf_le_left : U ⊓ V _ hU ≤ U) s = rs X inf_le_right (a _ hU) := hs ⟨_, hU⟩
  exact (gen_rs (inf_le_left : U ⊓ V _ hU ≤ U) ⟨hU, hx _ hU⟩ s).symm.trans
    ((congrArg _ h1).trans ((gen_rs _ _ _).trans (ha _ _)))

def tr (N : LB X) (i j : N.ι) (hi : genericPoint X ∈ N.U i) (hj : genericPoint X ∈ N.U j) :
    X.functionField := gen (N.U i ⊓ N.U j) ⟨hi, hj⟩ (N.g i j).val

theorem tr_mul {N : LB X} (hN : N.IsLB) (i j k : N.ι) (hi) (hj) (hk) :
    tr N i j hi hj * tr N j k hj hk = tr N i k hi hk := by
  have h := congrArg (fun u => gen (N.U i ⊓ N.U j ⊓ N.U k) ⟨⟨hi, hj⟩, hk⟩ (Units.val u))
    (hN.cocycle i j k)
  simp only [Units.val_mul, map_mul] at h
  exact (congrArg₂ (· * ·) (gen_rs _ _ _) (gen_rs _ _ _)).symm.trans (h.trans (gen_rs _ _ _))

theorem tr_ne_zero (N : LB X) (i j : N.ι) (hi) (hj) : tr N i j hi hj ≠ 0 :=
  ((N.g i j).isUnit.map _).ne_zero

theorem tr_self {N : LB X} (hN : N.IsLB) (i : N.ι) (hi) : tr N i i hi hi = 1 :=
  mul_left_cancel₀ (tr_ne_zero N i i hi hi) ((tr_mul hN i i i hi hi hi).trans (_root_.mul_one _).symm)

theorem gen_sec {N : LB X} (s : N.Sec) (i j : N.ι) (hi) (hj) :
    gen _ hi (s.f i) = tr N i j hi hj * gen _ hj (s.f j) := by
  have h := congrArg (gen (N.U i ⊓ N.U j) ⟨hi, hj⟩) (s.compat i j)
  rw [map_mul] at h
  exact (gen_rs _ _ _).symm.trans (h.trans (congrArg _ (gen_rs _ _ _)))

theorem gen_constFn (p : X ⟶ Sp K) (U : X.Opens) (h) (a : K) :
    gen U h (constFn p U a) = gen ⊤ trivial (constFn p ⊤ a) := by
  rw [← gen_rs le_top h]
  congr 1
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : U ≤ ⊤)).op)).symm

theorem exists_sec {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (f : X.functionField)
    (hf : ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) :
    ∃ s : N.Sec, gen _ h₀ (s.f j₀) = f := by
  have H : ∀ j, ∃ a : Γ(X, N.U j), ∀ hj, gen _ hj a = tr N j j₀ hj h₀ * f := by
    intro j
    by_cases hj : genericPoint X ∈ N.U j
    · obtain ⟨a, ha⟩ := exists_gen_eq (N.U j) (tr N j j₀ hj h₀ * f) fun x hx => by
        obtain ⟨i, hi⟩ := hc x
        obtain ⟨a, ha⟩ := hf i
        refine ⟨N.U j ⊓ W i, ⟨hx, hi⟩,
          rs X (inf_le_inf_left _ (hW i)) (N.g j (c i)).val * rs X inf_le_right a, ?_⟩
        rw [map_mul, gen_rs, gen_rs, ha, ← tr_mul hN j (c i) j₀ hj (hW i (hη i)) h₀]
        unfold tr
        ring
      exact ⟨a, ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using H
  refine ⟨⟨a, fun i j => eq_of_gen fun h => ?_⟩, ?_⟩
  · rw [map_mul]
    refine (gen_rs _ _ _).trans ((ha i h.1).trans ?_)
    rw [← tr_mul hN i j j₀ h.1 h.2 h₀, _root_.mul_assoc, ← ha j h.2]
    exact congrArg _ (gen_rs (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) h (a j)).symm
  · rw [ha, tr_self hN, _root_.one_mul]

theorem lineBundle_global_sections_functionField_iff [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (V : Submodule K X.functionField)
    (hV : ∀ f, f ∈ V ↔ ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) (r : ℕ) :
    SectionsHaveFiniteDimension p N r ↔ Module.Finite K V ∧ Module.finrank K V = r := by
  let θ : N.Sec → V := fun s => ⟨gen _ h₀ (s.f j₀), (hV _).2 fun i =>
    ⟨rs X (hW i) (s.f (c i)), by rw [gen_rs, gen_sec s (c i) j₀ _ h₀, _root_.mul_comm]⟩⟩
  have hθ : Function.Surjective θ := fun f => by
    obtain ⟨s, hs⟩ := exists_sec hN j₀ h₀ W c hW hη hc f ((hV f).1 f.2)
    exact ⟨s, Subtype.ext hs⟩
  have key : ∀ (s : Fin r → N.Sec) (t : N.Sec) (a : Fin r → K),
      (∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j) ↔ ∑ i, a i • θ (s i) = θ t := by
    intro s t a
    have e : ∀ j hj, gen _ hj (∑ i, constFn p _ (a i) * (s i).f j) =
        tr N j j₀ hj h₀ * ((∑ i, a i • θ (s i) : V) : X.functionField) := by
      intro j hj

      rw [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, gen_constFn, ← halg, gen_sec (s i) j j₀ hj h₀, SetLike.val_smul, Algebra.smul_def]
      ring
    constructor
    · intro h
      apply Subtype.ext
      have := e j₀ h₀
      rw [tr_self hN, _root_.one_mul, ← h j₀] at this
      exact this.symm
    · intro h j
      refine eq_of_gen fun hj => ?_
      rw [e, h, gen_sec t j j₀ hj h₀]
  constructor
  · rintro ⟨s, hs⟩
    have hb : Function.Bijective (Fintype.linearCombination K fun i => θ (s i)) := by
      rw [Function.bijective_iff_existsUnique]
      intro f
      obtain ⟨t, rfl⟩ := hθ f
      simpa only [key, Fintype.linearCombination_apply] using hs t
    have E := LinearEquiv.ofBijective _ hb
    exact ⟨Module.Finite.equiv E, by rw [← E.finrank_eq, Module.finrank_fin_fun]⟩
  · rintro ⟨hf, hr⟩
    let b := Module.finBasisOfFinrankEq K V hr
    choose s hs using fun i => hθ (b i)
    refine ⟨s, fun t => ?_⟩
    simp only [key, hs]
    refine ⟨b.equivFun (θ t), b.sum_equivFun _, fun a ha => ?_⟩
    rw [← ha, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

def ffMap (ψ : X ⟶ Y) (hψ : ψ (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (x := ψ (genericPoint X)) (y := genericPoint Y)
    (hψ ▸ specializes_rfl) ≫ ψ.stalkMap (genericPoint X)).hom

theorem ffMap_gen (ψ : X ⟶ Y) (hψ) (U : Y.Opens) (h) (h') (a : Γ(Y, U)) :
    ffMap ψ hψ (gen U h a) = gen (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom a) := by
  have := Y.presheaf.germ_stalkSpecializes_apply (x := ψ (genericPoint X)) h
    (hψ ▸ specializes_rfl) a
  exact (congrArg (ψ.stalkMap (genericPoint X)).hom this).trans
    (ψ.germ_stalkMap_apply U _ h' a)

omit [IsIntegral Y] in
theorem tr_linComb (N : LB Y) (ψ : X ⟶ Y) (ε : ℤ) (e : ℕ) (hε : ε = e) (J J' : PUnit → N.ι)
    (h) (h') (h'') :
    tr (LB.LinComb N (K := PUnit) (fun _ => ψ) (fun _ => ε)) J J' h h' =
      gen (ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩))) h'' ((ψ.app _).hom (N.g _ _).val) ^ e := by
  subst hε
  unfold tr LB.LinComb
  dsimp only
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  exact congrArg (· ^ e) (gen_rs _ _ _)

theorem tr_lbPow (N : LB X) (e : ℕ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (lbPow N e) J J' h h' = tr N (J ⟨⟩) (J' ⟨⟩) k k' ^ e := by
  rw [tr_linComb N (𝟙 X) e e rfl J J' h h' ⟨k, k'⟩]
  rfl

theorem tr_pull (N : LB Y) (ψ : X ⟶ Y) (hψ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (N.pull ψ) J J' h h' = ffMap ψ hψ (tr N (J ⟨⟩) (J' ⟨⟩) k k') := by
  have h'' : genericPoint X ∈ ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩)) :=
    ⟨LB.wchart_le N _ J ⟨⟩ h, LB.wchart_le N _ J' ⟨⟩ h'⟩
  rw [tr_linComb N ψ 1 1 rfl J J' h h' h'', pow_one]
  exact (ffMap_gen ψ hψ _ _ _ _).symm

theorem tr_pw (N : LB X) (d : ℕ) (i j : N.ι) (h) (h') :
    tr (pw N d) i j h h' = tr N i j h h' ^ d := by
  unfold tr pw
  dsimp only
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

theorem mem_basicOpen_iff {U : X.Opens} (h) (a : Γ(X, U)) :
    genericPoint X ∈ X.basicOpen a ↔ gen U h a ≠ 0 :=
  (X.mem_basicOpen a _ h).trans (isUnit_iff_ne_zero (G₀ := X.functionField))

theorem eventually_mul_pow {W D : X.Opens} (hW : IsAffineOpen W) (h) (u : Γ(X, W))
    (hu : gen W h u ≠ 0) (hD : X.basicOpen u ≤ D) (hD') (a : Γ(X, D)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ b, gen W h b = gen D hD' a * gen W h u ^ n := by
  have := hW.isLocalization_basicOpen u
  have hb := (mem_basicOpen_iff h u).2 hu
  obtain ⟨⟨b, _, m, rfl⟩, hm⟩ := IsLocalization.surj (Submonoid.powers u) (rs X hD a)
  have h1 : gen D hD' a * gen W h u ^ m = gen W h b := by
    have h2 := congrArg (gen _ hb) hm
    rw [map_mul, gen_rs] at h2
    have h3 : ∀ x : Γ(X, W), gen _ hb (algebraMap Γ(X, W) Γ(X, X.basicOpen u) x) = gen W h x :=
      fun x => gen_rs (X.basicOpen_le u) hb x
    rw [h3, h3, map_pow] at h2
    exact h2
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨b * u ^ k, by rw [map_mul, map_pow, ← h1, pow_add, _root_.mul_assoc]⟩

theorem exists_frac {D : X.Opens} (hD : IsAffineOpen D) (h) (t : X.functionField) :
    ∃ a b : Γ(X, D), gen D h b ≠ 0 ∧ t * gen D h b = gen D h a := by
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X D hD
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, D)) t
  exact ⟨a, b, fun h0 => nonZeroDivisors.ne_zero hb (gen_injective D h (h0.trans (map_zero _).symm)),
    hab⟩

end GlobalTheory.VolFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def regAlg [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    (U : X.Opens) (h : genericPoint X ∈ U) : Subalgebra K X.functionField :=
  { (gen U h).rangeS with
    algebraMap_mem' := fun a => ⟨constFn p U a, (gen_constFn p U h a).trans (halg a).symm⟩ }

theorem mem_regAlg [Algebra K X.functionField] {p : X ⟶ Sp K} {halg} {U : X.Opens} {h}
    {f : X.functionField} : f ∈ regAlg p halg U h ↔ ∃ a, gen U h a = f := Iff.rfl

theorem sections_power_integral_iff_affine_cover [Algebra K X.functionField] (p : X ⟶ Sp K) (halg)
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (y : κ → X.functionField)
    (hy : ∀ i, tr N (c i) j₀ (hW i (hη i)) h₀ = y i) (e r : ℕ) :
    SectionsHaveFiniteDimension p (lbPow N e) r ↔ Module.Finite K (piece (fun i => regAlg p halg (W i) (hη i)) y e) ∧
      Module.finrank K (piece (fun i => regAlg p halg (W i) (hη i)) y e) = r := by
  refine lineBundle_global_sections_functionField_iff p halg (N := lbPow N e) (LB.isLB_linComb hN _ _) (fun _ => j₀)
    (Set.mem_iInter.2 fun _ => h₀) W (fun i _ => c i)
    (fun i _ hx => Set.mem_iInter.2 fun _ => hW i hx) hη hc _ (fun f => ?_) r
  refine forall_congr' fun i => ?_
  refine mem_regAlg.trans (exists_congr fun a => Eq.congr_right (congrArg (f * ·) ?_))
  exact ((tr_lbPow N e (fun _ => c i) (fun _ => j₀) _ _ (hW i (hη i)) h₀).trans
    (congrArg (· ^ e) (hy i))).symm

def constFF (p : X ⟶ Sp K) : K →+* X.functionField :=
  (gen ⊤ trivial).comp ((p.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem den_of_section [Algebra K Y.functionField] (p : Y ⟶ Sp K) (halg) (M : LB Y) (j₀ : M.ι) (h₀)
    {κ : Type} [Finite κ] (W : κ → Y.Opens) (c : κ → M.ι) (hW : ∀ i, W i ≤ M.U (c i))
    (hη : ∀ i, genericPoint Y ∈ W i) (haff : ∀ i, IsAffineOpen (W i)) (d : ℕ) (s : (pw M d).Sec)
    (hs : IsAffineOpen (Out.nonzeroLocus s)) (hs' : genericPoint Y ∈ Out.nonzeroLocus s) :
    Den (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀) := by
  let σ := gen _ h₀ (s.f j₀)
  have hσ : σ ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hs'
    have hk' : genericPoint Y ∈ M.U k := Y.basicOpen_le _ hk
    have h1 := (mem_basicOpen_iff hk' (s.f k)).1 hk
    exact right_ne_zero_of_mul ((gen_sec s k j₀ hk' h₀).symm.trans_ne h1)
  let u : ∀ i, Γ(Y, W i) := fun i => rs Y (hW i) (s.f (c i))
  have hu : ∀ i, gen _ (hη i) (u i) = tr M (c i) j₀ (hW i (hη i)) h₀ ^ d * σ := fun i =>
    (gen_rs _ _ _).trans ((gen_sec s (c i) j₀ (hW i (hη i)) h₀).trans
      (congrArg (· * σ) (tr_pw M d _ _ _ _)))
  have hu0 : ∀ i, gen _ (hη i) (u i) ≠ 0 := fun i => by
    rw [hu]
    exact mul_ne_zero (pow_ne_zero _ (tr_ne_zero _ _ _ _ _)) hσ
  have hD : ∀ i, Y.basicOpen (u i) ≤ Out.nonzeroLocus s := fun i =>
    (Y.basicOpen_res (s.f (c i)) (homOfLE (hW i)).op).le.trans
      (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) (c i)))
  have ev : ∀ a : Γ(Y, Out.nonzeroLocus s), ∀ᶠ n : ℕ in Filter.atTop, gen _ hs' a * σ ^ n ∈
      piece (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀)
        (d * n) := by
    intro a
    simp only [mem_piece]
    refine Filter.eventually_all.2 fun i => ?_
    filter_upwards [eventually_mul_pow (haff i) (hη i) (u i) (hu0 i) (hD i) hs' a] with n hn
    obtain ⟨b, hb⟩ := hn
    refine ⟨b, hb.trans ?_⟩
    rw [hu]
    ring
  intro t
  obtain ⟨a, b, hb, hab⟩ := exists_frac hs hs' t
  obtain ⟨n, hna, hnb⟩ := ((ev a).and (ev b)).exists
  refine ⟨d * n, _, hnb, mul_ne_zero hb (pow_ne_zero _ hσ), ?_⟩
  rw [← hab] at hna
  convert hna using 1
  ring

omit [IsIntegral Y] in
theorem exists_affine_cover [CompactSpace Y] {M : LB Y} (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → Y.Opens) (c : κ → M.ι), (∀ i, W i ≤ M.U (c i)) ∧
      (∀ i, ∃ x, x ∈ W i) ∧ (∀ i, IsAffineOpen (W i)) ∧ ∀ x, ∃ i, x ∈ W i := by
  have h : ∀ y : Y, ∃ (j : M.ι) (W : Y.Opens), IsAffineOpen W ∧ y ∈ W ∧ W ≤ M.U j := by
    intro y
    have hy : y ∈ ⨆ i, M.U i := hM.cover ▸ trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨W, hW, h1, h2⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨j, W, hW, h1, h2⟩
  choose c W h1 h2 h3 using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, h2 y⟩)
  refine ⟨t, inferInstance, fun y => W y, fun y => c y, fun y => h3 y, fun y => ⟨y, h2 y⟩,
    fun y => h1 y, fun x => ?_⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hx⟩

theorem vol_pull [CompactSpace Y] (p : Y ⟶ Sp K) (ψ : X ⟶ Y) [IsFinite ψ]
    (hψ : ψ (genericPoint X) = genericPoint Y) {D : ℕ} (hD : MapDeg ψ D) {M : LB Y} (hM : M.IsLB)
    (d : ℕ) (s : (pw M d).Sec) (hs : IsAffineOpen (Out.nonzeroLocus s))
    (hs' : genericPoint Y ∈ Out.nonzeroLocus s) {g : ℕ} {δ : ℝ} (hv : Vol p M g δ) :
    Vol (ψ ≫ p) (M.pull ψ) g (D * δ) := by
  obtain ⟨κ, _, W, c, hW, hne, haff, hc⟩ := exists_affine_cover hM
  have hη : ∀ i, genericPoint Y ∈ W i := fun i => generic_mem (hne i).choose_spec
  have hη' : ∀ i, genericPoint X ∈ ψ ⁻¹ᵁ W i := fun i => show ψ _ ∈ W i from hψ ▸ hη i
  obtain ⟨i₀, -⟩ := hc (genericPoint Y)
  letI : Algebra K Y.functionField := (constFF p).toAlgebra
  letI : Algebra K X.functionField := (constFF (ψ ≫ p)).toAlgebra
  letI : Algebra Y.functionField X.functionField := (ffMap ψ hψ).toAlgebra
  have halg : ∀ a, algebraMap K Y.functionField a = gen ⊤ trivial (constFn p ⊤ a) := fun _ => rfl
  have halg' : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn (ψ ≫ p) ⊤ a) :=
    fun _ => rfl
  have hφ : ∀ a, algebraMap Y.functionField X.functionField a = ffMap ψ hψ a := fun _ => rfl
  haveI : IsScalarTower K Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hφ, halg, halg', ffMap_gen ψ hψ ⊤ trivial trivial]
    congr 1
    unfold constFn
    rw [Scheme.Hom.app_eq_appLE]
    exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE ψ p ⊤ ⊤ ⊤ (fun _ _ => trivial) (fun _ _ => trivial))).symm
  let R := fun i => regAlg p halg (W i) (hη i)
  let R' := fun i => regAlg (ψ ≫ p) halg' (ψ ⁻¹ᵁ W i) (hη' i)
  let y := fun i => tr M (c i) (c i₀) (hW i (hη i)) (hW i₀ (hη i₀))
  have hden : Den R y := den_of_section p halg M (c i₀) _ W c hW hη haff d s hs hs'
  have H : ∀ e r, SectionsHaveFiniteDimension p (lbPow M e) r ↔
      Module.Finite K (piece R y e) ∧ Module.finrank K (piece R y e) = r :=
    sections_power_integral_iff_affine_cover p halg hM (c i₀) (hW i₀ (hη i₀)) W c hW hη hc y fun _ => rfl
  have hW' : ∀ i, ψ ⁻¹ᵁ W i ≤ (M.pull ψ).U (fun _ => c i) := fun i =>
    le_trans (fun _ hx => hW i hx) (AbLaw.le_pull M ψ (le_refl (M.U (c i))))
  have H' : ∀ e r, SectionsHaveFiniteDimension (ψ ≫ p) (lbPow (M.pull ψ) e) r ↔
      Module.Finite K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) ∧
        Module.finrank K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) = r :=
    sections_power_integral_iff_affine_cover (ψ ≫ p) halg' (N := M.pull ψ) (LB.isLB_linComb hM _ _) (fun _ => c i₀)
      (hW' i₀ (hη' i₀)) (fun i => ψ ⁻¹ᵁ W i) (fun i _ => c i) hW' hη' (fun x => hc (ψ x)) _
      fun i => tr_pull M ψ hψ _ _ _ _ (hW i (hη i)) (hW i₀ (hη i₀))
  have hR : ∀ i, ∀ a ∈ R i, algebraMap _ X.functionField a ∈ R' i := by
    rintro i _ ⟨a, rfl⟩
    exact ⟨_, (ffMap_gen ψ hψ _ _ _ a).symm⟩
  have hS : ∀ i, ∀ t : X.functionField, ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a := by
    intro i t
    obtain ⟨a, b, hb, hab⟩ := exists_frac ((haff i).preimage ψ) (hη' i) t
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb, hab⟩
  have hG : ∀ i, ∃ (n : ℕ) (v : Fin n → X.functionField), ∀ t ∈ R' i,
      ∃ w : Fin n → Y.functionField, (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • v l := by
    intro i
    letI := (ψ.app (W i)).hom.toAlgebra
    haveI : Module.Finite Γ(Y, W i) Γ(X, ψ ⁻¹ᵁ W i) := IsFinite.finite_app ψ (W i) (haff i)
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(Y, W i)) (M := Γ(X, ψ ⁻¹ᵁ W i))
    refine ⟨n, fun l => gen _ (hη' i) (v l), ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hv ▸ Submodule.mem_top : t ∈ Submodule.span Γ(Y, W i) (Set.range v))
    refine ⟨fun l => gen _ (hη i) (w l), fun l => ⟨_, rfl⟩, ?_⟩

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ffMap_gen ψ hψ _ _ (hη' i)]
    rfl
  haveI : Module.Finite Y.functionField X.functionField := by
    obtain ⟨n, v, hv⟩ := hG i₀
    exact finite_of_frac (R' i₀) (hS i₀) v fun t ht => (hv t ht).imp fun _ h => h.2
  have hrank : Module.finrank Y.functionField X.functionField = D := by
    haveI : Nonempty (W i₀) := ⟨⟨_, hη i₀⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ W i₀) := ⟨⟨_, hη' i₀⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Y _ (haff i₀)
    haveI := functionField_isFractionRing_of_isAffineOpen X _ ((haff i₀).preimage ψ)
    letI := (ψ.app (W i₀)).hom.toAlgebra
    letI : Algebra Γ(Y, W i₀) X.functionField :=
      ((gen _ (hη' i₀)).comp (ψ.app (W i₀)).hom).toAlgebra
    haveI : IsScalarTower Γ(Y, W i₀) Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower Γ(Y, W i₀) Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => (ffMap_gen ψ hψ _ (hη i₀) (hη' i₀) a).symm
    rw [IsFractionRing.finrank_eq Γ(Y, W i₀) Y.functionField Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField]
    exact Module.finrank_eq_of_rank_eq (hD _ (haff i₀) ⟨_, hη i₀⟩)
  obtain ⟨h, hh, hlim⟩ := hv
  have hfin := fun e => ((H e _).1 (hh e)).1
  have hrk := fun e => ((H e _).1 (hh e)).2
  obtain ⟨c₁, hup⟩ := upper (R' := R') hden hG hfin
  obtain ⟨c₂, hlo⟩ := lower hden hR hS fun e => (hup e).1
  refine ⟨_, fun e => (H' e _).2 ⟨(hup e).1, rfl⟩,
    tendsto_of_sandwich h _ D g c₂ c₁ δ hlim (fun e => ?_) fun e => ?_⟩
  · rw [← hrk, ← hrank]
    exact hlo e (hfin e)
  · rw [← hrk, ← hrank]
    exact (hup e).2

end GlobalTheory.VolFin

namespace GlobalTheory

theorem vol_pull_of_isFinite : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  intro K _ _ P α D M δ hα hfin hD hM hamp hv
  haveI := polAV_isIntegral_of_isAlgClosed K P
  haveI := P.isAb.proper
  haveI : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hsurj := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  have hψ : α.left (genericPoint P.A.left) = genericPoint P.A.left := by
    have := (genericPoint_spec P.A.left).image α.left.continuous
    rw [Set.image_univ, α.left.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨d, -, n, s, hcov, hs⟩ := (Unif.relAmple_iff_veryAmpleBy K P.A M hM).1 hamp
  have hx : genericPoint P.A.left ∈ ⨆ i, Out.nonzeroLocus (s i) := hcov ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have := VolFin.vol_pull P.A.hom α.left hψ hD hM d (s i) (hs i).1 hi hv
  rwa [Over.w α] at this

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphismStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  first | exact @GlobalTheory.vol_pull_of_isFinite | exact GlobalTheory.vol_pull_of_isFinite | (intros; apply GlobalTheory.vol_pull_of_isFinite <;> assumption)
end
end
