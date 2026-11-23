module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGenLiftOfIsNilpotent

section

@[expose] public section

noncomputable section

namespace GlobalTheory.NilGen

section General

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}

theorem exists_ratio (hL : L.IsLB) (p : Z ⟶ Y) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') (u : LB.Sec (LB.LinComb L φ ε)) :
    ∃ h : Γ(Z, ⊤), ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val := by
  obtain ⟨t, ht⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (pullMulSec u p (LB.invGen L _ _ g) (DVR.invGen_isGen _ _ _ _ hg))
  have le : (⊤ : Z.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Z.presheaf.map (homOfLE le).op).hom (t.f PEmpty.elim), fun y J hJ => ?_⟩
  have e := ht Z (𝟙 Z) y J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, Category.id_comp,
    sval_of t (𝟙 Z) y J PEmpty.elim (fun k => k.elim)] at e
  refine Eq.trans ?_ (congrArg₂ (· * ·) ((gs_res (𝟙 Z) y le trivial _).trans e).symm rfl)
  exact (Units.inv_mul_cancel_right _ _).symm

def ratioIdeal (p : Z ⟶ Y) (hp : Function.Surjective p.appTop.hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb L φ' ε')) : Ideal Γ(Z, ⊤) where
  carrier := {h | ∃ u : LB.Sec (LB.LinComb L φ ε),
    ∀ y J, Good L y J → sval u p y J = gs (𝟙 Z) y ⊤ h * (val g (𝟙 Z) y J).val}
  zero_mem' := ⟨DVR.SecOps.secZero, fun y J hJ => by
    rw [gs_zero (𝟙 Z) y ⊤ trivial, zero_mul]
    exact gs_zero p y _ (hJ.mem φ p)⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨DVR.SecOps.secAdd u v, fun y J hJ => ?_⟩
    rw [gs_add (𝟙 Z) y ⊤ trivial, add_mul, ← hu y J hJ, ← hv y J hJ]
    exact gs_add p y _ (hJ.mem φ p) _ _
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨c, rfl⟩ := hp c
    refine ⟨DVR.SecOps.secScale c u, fun y J hJ => ?_⟩
    rw [smul_eq_mul, gs_mul (𝟙 Z) y ⊤ trivial, mul_assoc, ← hu y J hJ]
    refine (gs_mul p y _ (hJ.mem φ p) _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (gs_res p y le_top (hJ.mem φ p) c).trans ?_
    exact ((gs_pull (𝟙 Z) p y ⊤ trivial c).trans (by rw [Category.id_comp])).symm

theorem ratioIdeal_eq_top [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (g : LB.Gen (LB.LinComb L φ' ε')) (hg : g.IsGen)
    (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') : ratioIdeal p hp φ ε g = ⊤ := by
  have hM : (LB.LinComb L φ ε).IsLB := DVR.linComb_isLB _ hL _ _
  rw [← Ideal.span_eq (ratioIdeal p hp φ ε g), ← (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff]
  refine top_unique fun y _ => ?_
  obtain ⟨k, hk⟩ := exists_chart hM (p y)
  obtain ⟨r, hr, hy⟩ := (isAffineOpen_top Y).exists_basicOpen_le (V := (LB.LinComb L φ ε).U k) ⟨p y, hk⟩ trivial
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_basicOpen hM r k hr
  obtain ⟨h, hh⟩ := exists_ratio hL p g hg hF u
  refine Opens.mem_iSup.2 ⟨⟨h, u, hh⟩, ?_⟩
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
  have h₁ : IsUnit (sval u p y J) :=
    (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).1 (hu.ge hy)
  rw [hh y J hJ] at h₁
  exact (isUnit_gs_iff (𝟙 Z) y ⊤ trivial h).1 (isUnit_of_mul_isUnit_left h₁)

theorem exists_gen_lift [IsAffine Y] [IsAffine Z] (hL : L.IsLB) (p : Z ⟶ Y)
    (hp : Function.Surjective p.appTop.hom) (hp' : Function.Surjective p) (g : LB.Gen (LB.LinComb L φ' ε'))
    (hg : g.IsGen) (hF : FormEq (fun k => p ≫ φ k) ε φ' ε') :
    ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' p) g := by
  obtain ⟨u, hu⟩ : (1 : Γ(Z, ⊤)) ∈ ratioIdeal p hp φ ε g := by
    rw [ratioIdeal_eq_top hL p hp g hg hF]; trivial
  have hu' : ∀ y J, Good L y J → sval u p y J = (val g (𝟙 Z) y J).val := fun y J hJ => by
    rw [hu y J hJ, gs_eq (𝟙 Z) y ⊤ trivial, map_one, map_one, one_mul]
  have hn : ∀ x, x ∈ nonzeroLocus u := fun x => by
    obtain ⟨y, rfl⟩ := hp' x
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
    refine (mem_nonzeroLocus_iff_pull u p y (k := fun k => J (p ≫ φ k)) (Good.mem hJ φ p)).2 ?_
    exact (congrArg IsUnit (hu' y J hJ)).mpr (Units.isUnit _)
  have hun : ∀ j, IsUnit (u.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    have := (mem_nonzeroLocus_iff_isUnit u hx).1 (hn x)
    rw [gs_eq (𝟙 Y) x _ hx] at this
    exact this
  refine ⟨⟨fun j => (hun j).unit⟩, fun i j => Units.ext (u.compat i j), corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, Category.id_comp]
  exact Units.ext ((gs_unit p y _ (hJ.mem φ p) _).symm.trans (hu' y J hJ))

theorem surjective_appTop_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π) :
    Function.Surjective (spMap π).appTop.hom := by
  have e : (spMap π).appTop = (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom π ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2

theorem surjective_spMap {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) : Function.Surjective (spMap π) := fun x => by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha => by
    obtain ⟨n, hn⟩ := hn
    have h : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
    exact x.isPrime.mem_of_pow_mem n (h ▸ x.asIdeal.zero_mem)
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem exists_gen_lift_of_isNilpotent : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (K : Type) [Fintype K] (φ : K → (Sp A ⟶ X)) (ε : K → ℤ) (K' : Type) [Fintype K'] (φ' : K' → (Sp B ⟶ X)) (ε' : K' → ℤ) (g : LB.Gen (LB.LinComb L φ' ε')), g.IsGen → (∀ (U : Type) [CommGroup U] (h : (Sp B ⟶ X) → U), ∏ k, h (spMap π ≫ φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k) → ∃ g' : LB.Gen (LB.LinComb L φ ε), g'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε g' (spMap π)) g :=
  fun _ _ hL _ _ _ _ π hπ hn _ _ _ _ _ _ _ _ g hg hF =>
    exists_gen_lift hL (spMap π) (surjective_appTop_spMap π hπ) (surjective_spMap π hπ hn) g hg hF

end GlobalTheory.NilGen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

noncomputable section

namespace GlobalTheory.ChartFrames

section Alg

variable {S Ix : Type} [CommRing S]

theorem nilpotent_of_le (m : ℕ) (I : Ideal (Jet S Ix m))
    (h : ∀ p : MvPolynomial Ix S, Ideal.Quotient.mk _ p ∈ I → p ∈ orig S Ix) : IsNilpotent I := by
  refine ⟨m + 1, le_bot_iff.1 ?_⟩
  have h1 : I ≤ Ideal.map (Ideal.Quotient.mk (orig S Ix ^ (m + 1))) (orig S Ix) := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.mem_map_of_mem _ (h p ha)
  refine (Ideal.pow_right_mono h1 _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem trunc_surj (m : ℕ) :
    Function.Surjective ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem trunc_nil (m : ℕ) : IsNilpotent
    (RingHom.ker ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m)) :=
  nilpotent_of_le _ _ fun p hp => by
    have : Ideal.Quotient.mk (orig S Ix ^ (m + 1)) p = 0 := hp
    exact Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.Quotient.eq_zero_iff_mem.1 this)

theorem aug_surj (m : ℕ) : Function.Surjective ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S) :=
  fun a => ⟨algebraMap S _ a, (jetAug : Jet S Ix m →ₐ[S] S).commutes a⟩

theorem aug_nil (m : ℕ) : IsNilpotent (RingHom.ker ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S)) :=
  nilpotent_of_le _ _ fun p hp => by
    have h1 : MvPolynomial.aeval (fun _ => (0 : S)) p = 0 := hp
    have h2 : MvPolynomial.constantCoeff p = 0 := by simpa using h1
    simpa [h2] using sub_const_mem_orig p

variable (d : ℕ)

theorem aug_axis0 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis0 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem aug_axis1 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis1 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem trunc_axis0 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis0 d (m + 1)) =
    (axis0 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem trunc_axis1 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis1 d (m + 1)) =
    (axis1 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem aug_trunc (m : ℕ) : (jetAug : Jet S Ix m →ₐ[S] S).comp (jetTrunc : Jet S Ix (m + 1) →ₐ[S] _) = jetAug := by
  apply jet_hom_ext
  intro p
  rfl

theorem cancel₀ {U : Type} [CommGroup U] (a b : U) : a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [mul_right_comm a, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem cancel₁ {U : Type} [CommGroup U] (a b : U) : a * a⁻¹ * b⁻¹ * b = 1 := by
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem exists_norm {T : Over X0} (p q : T ⟶ t.G) (s₁ s₂ s₀ : T ⟶ T)
    (h₁ : s₁ ≫ (p * q) = p) (h₂ : s₂ ≫ (p * q) = q) (h₀ : s₀ ≫ (p * q) = 1)
    (g₁ : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (p * q).left) (fun _ => 1))) (hg₁ : g₁.IsGen) :
    ∃ e : LB.Gen (LB.LinComb t.PP.L (cφG t ![p, q]) (cε 2)), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good t.PP.L z J →
        val e r z J = val g₁ r z J * (val g₁ (r ≫ s₁.left) z J)⁻¹ * (val g₁ (r ≫ s₂.left) z J)⁻¹ *
          val g₁ (r ≫ s₀.left) z J := by
  obtain ⟨e, he, hv⟩ := exists_gen t.PP.isLB (φ' := cφG t ![p, q]) (ε' := cε 2) (fun U _ h => by
      have hc := prod_cube2 t.G (fun w : T ⟶ t.G => h w.left) ![p, q]
      refine Eq.trans ?_ hc.symm
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, h₁, h₂, h₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, zpow_neg, zpow_one]
      ac_rfl)
    (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ g₁
      (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₁.left))) (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₂.left)))
      (LB.pullGen t.PP.L _ _ g₁ s₀.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg₁
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _))) (DVR.pullGen_isGen _ _ _ _ hg₁ _))
  refine ⟨e, he, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem exists_tower {Ix : Type} (P : ∀ m, overAt x0 (Jet S Ix m) ⟶ t.G)
    (h0 : Formalism.L2.Pj.homAt x0 (jetAug : Jet S Ix 0 →ₐ[S] S) ≫ P 0 = 1)
    (htr : ∀ m, Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) ≫ P (m + 1) = P m) :
    ∃ g₁ : ∀ m, LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)), (∀ m, (g₁ m).IsGen) ∧
      ∀ m (Z : Scheme.{0}) (r : Z ⟶ (overAt x0 (Jet S Ix m)).left) (z : Z) (J), Good t.PP.L z J →
        val (g₁ (m + 1)) (r ≫ (Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m)).left) z J =
          val (g₁ m) r z J := by
  obtain ⟨g0, hg0, -⟩ := GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix 0) S _ (aug_surj 0) (aug_nil 0)
    PUnit.{1} (fun _ => (P 0).left) (fun _ => 1) PUnit.{1} (fun _ => (overAt x0 S).hom ≫ eSec t.G) (fun _ => 1)
    (LB.pullGen t.PP.L (fun _ : PUnit.{1} => eSec t.G) (fun _ => 1) t.PP.rig (overAt x0 S).hom)
    (DVR.pullGen_isGen _ _ _ _ t.PP.rigGen _) (fun U _ h => by
      have := congrArg Over.Hom.left h0
      exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  have step := fun m (g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1))) (hg : g.IsGen) =>
    GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix (m + 1)) (Jet S Ix m) _ (trunc_surj m) (trunc_nil m)
      PUnit.{1} (fun _ => (P (m + 1)).left) (fun _ => 1) PUnit.{1} (fun _ => (P m).left) (fun _ => 1) g hg
      (fun U _ h => by
        have := congrArg Over.Hom.left (htr m)
        exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  choose f hf hc using step
  let g₁ : ∀ m, {g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)) // g.IsGen} :=
    fun m => Nat.rec ⟨g0, hg0⟩ (fun m g => ⟨f m g.1 g.2, hf m g.1 g.2⟩) m
  refine ⟨fun m => (g₁ m).1, fun m => (g₁ m).2, fun m Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (hc m (g₁ m).1 (g₁ m).2) r)

end Geo

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch

  let c : ∀ m, Fin 2 → (jOG x0 d m 2 ⟶ jOG x0 d m 1) := fun m i => Formalism.L2.Pj.homAt x0 (jetCopy d m i)
  let a0 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis0 d m)
  let a1 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis1 d m)
  let o : ∀ m n, overAt x0 S ⟶ jOG x0 d m n := fun m n => Formalism.L2.Pj.homAt x0 jetAug
  let u : ∀ m n, jOG x0 d m n ⟶ overAt x0 S := fun m n => Formalism.L2.Pj.homAt x0 (Algebra.ofId S _)
  let tr : ∀ m n, jOG x0 d m n ⟶ jOG x0 d (m + 1) n := fun m n => Formalism.L2.Pj.homAt x0 jetTrunc
  have a0c0 : ∀ m, a0 m ≫ c m 0 = u m 1 ≫ o m 1 := fun m => by
    simp only [a0, c, u, o, homAt_comp, first_axis_at_first_copy]
  have a0c1 : ∀ m, a0 m ≫ c m 1 = 𝟙 _ := fun m => by
    simp only [a0, c, homAt_comp, first_axis_at_second_copy, homAt_id]
  have a1c0 : ∀ m, a1 m ≫ c m 0 = 𝟙 _ := fun m => by
    simp only [a1, c, homAt_comp, second_axis_at_first_copy, homAt_id]
  have a1c1 : ∀ m, a1 m ≫ c m 1 = u m 1 ≫ o m 1 := fun m => by
    simp only [a1, c, u, o, homAt_comp, second_axis_at_second_copy]
  have oa0 : ∀ m, o m 1 ≫ a0 m = o m 2 := fun m => by
    simp only [a0, o, homAt_comp, aug_axis0]
  have oa1 : ∀ m, o m 1 ≫ a1 m = o m 2 := fun m => by
    simp only [a1, o, homAt_comp, aug_axis1]
  have oc : ∀ m i, o m 2 ≫ c m i = o m 1 := fun m i => by
    simp only [c, o, homAt_comp, aug_copy]
  have a0u : ∀ m, a0 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a0, u, homAt_comp, Algebra.comp_ofId]
  have a1u : ∀ m, a1 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a1, u, homAt_comp, Algebra.comp_ofId]
  have tru : ∀ m, tr m 2 ≫ u (m + 1) 2 = u m 2 := fun m => by
    simp only [tr, u, homAt_comp, Algebra.comp_ofId]
  have otr : ∀ m, o m 2 ≫ tr m 2 = o (m + 1) 2 := fun m => by
    simp only [tr, o, homAt_comp, aug_trunc]
  have trc : ∀ m i, tr m 2 ≫ c (m + 1) i = c m i ≫ tr m 1 := fun m i => by
    simp only [tr, c, homAt_comp, copy_trunc]
  have tra0 : ∀ m, tr m 1 ≫ a0 (m + 1) = a0 m ≫ tr m 2 := fun m => by
    simp only [tr, a0, homAt_comp, trunc_axis0]
  have tra1 : ∀ m, tr m 1 ≫ a1 (m + 1) = a1 m ≫ tr m 2 := fun m => by
    simp only [tr, a1, homAt_comp, trunc_axis1]
  have ox : ∀ m, o m 1 ≫ x m = 1 := hch.zero
  have trx : ∀ m, tr m 1 ≫ x (m + 1) = x m := hch.trunc
  have hj : ∀ m i, jptG t x0 d x m i = c m i ≫ x m := fun _ _ => rfl
  obtain ⟨g₁, hg₁, hg₁t⟩ := exists_tower t x0
    (fun m => jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2))
    (by
      change o 0 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (oc 0), ox, _root_.mul_one])
    (fun m => by
      change tr m 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (trc m), trx])
  have key := fun m => exists_norm t (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))
    (c m 0 ≫ a1 m) (c m 1 ≫ a0 m) (u m 2 ≫ o m 2)
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), ox,
      MonObj.comp_one, _root_.mul_one])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), ox,
      MonObj.comp_one, _root_.one_mul])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (oc m), ox, MonObj.comp_one, _root_.mul_one])
    (g₁ m) (hg₁ m)
  choose e he hv using key
  refine ⟨e, he, fun m => corr_of_val t.PP.isLB fun y J hJ => ?_, fun m => ⟨corr_of_val t.PP.isLB fun y J hJ => ?_,
    corr_of_val t.PP.isLB fun y J hJ => ?_⟩⟩
  · refine (val_pull hJ _ _ _).trans ((hv (m + 1) _ _ y J hJ).trans (Eq.trans ?_ (hv m _ _ y J hJ).symm))
    have e1 : ∀ (s : jOG x0 d m 2 ⟶ jOG x0 d m 2) (s' : jOG x0 d (m + 1) 2 ⟶ jOG x0 d (m + 1) 2),
        tr m 2 ≫ s' = s ≫ tr m 2 →
        val (g₁ (m + 1)) ((𝟙 _ ≫ (tr m 2).left) ≫ s'.left) y J = val (g₁ m) (𝟙 _ ≫ s.left) y J := by
      intro s s' hs
      rw [Category.assoc, ← Over.comp_left, hs, Over.comp_left, ← Category.assoc]
      exact hg₁t m _ _ y J hJ
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (hg₁t m _ _ y J hJ)
      (congrArg _ (e1 _ _ ?_))) (congrArg _ (e1 _ _ ?_))) (e1 _ _ ?_)
    · simp only [Category.assoc, reassoc_of% (trc m), tra1]
    · simp only [Category.assoc, reassoc_of% (trc m), tra0]
    · simp only [Category.assoc, reassoc_of% (tru m), otr]
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a0 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), reassoc_of% (a0u m), oa1]
    exact cancel₀ _ _
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a1 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), reassoc_of% (a1u m), oa0]
    exact cancel₁ _ _

end GlobalTheory.ChartFrames
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_frames_cubeDefect_along_chart_over_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  first | exact @GlobalTheory.ChartFrames.exists_frames | exact GlobalTheory.ChartFrames.exists_frames | (intros; apply GlobalTheory.ChartFrames.exists_frames <;> assumption)
end
end
