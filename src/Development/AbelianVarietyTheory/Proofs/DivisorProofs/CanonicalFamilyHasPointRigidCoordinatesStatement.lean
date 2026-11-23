module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseValueMemDescendedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinatesStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
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
public import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMaximalIdealOfTrdegLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace GlobalTheory

theorem eq_maximalIdeal_of_trdeg_le (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra F A] (hA : Algebra.EssFiniteType F A) (p : Ideal A)
    (hp : p.IsPrime)
    (htr : Algebra.trdeg F (FractionRing (A ⧸ p)) ≤ Algebra.trdeg F (ResidueField A)) :
    p = maximalIdeal A := by
  classical
  by_contra hne
  have hle : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  obtain ⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  haveI := hA
  haveI : Algebra.EssFiniteType F (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A))
      (IsLocalRing.residue_surjective)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField A)
  haveI : Finite s := finite_of_isTranscendenceBasis hs
  let f : A ⧸ p →ₐ[F] ResidueField A :=
    Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by
      simpa [IsLocalRing.residue_eq_zero_iff] using hle hx)
  have hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x := fun x => rfl
  choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1
  let z : s → A ⧸ p := fun i => Ideal.Quotient.mk p (y i)
  have hfz : f ∘ z = ((↑) : s → ResidueField A) := by
    funext i
    simp only [Function.comp_apply, z, hfmk, hy]
  have hz : AlgebraicIndependent F z := by
    have h1 := hs.1
    rw [← hfz] at h1
    exact h1.of_comp f
  set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef
  have hb0 : b ≠ 0 := by
    rw [hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hap
  have hbk : b ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk p a) = 0
    rw [hfmk, IsLocalRing.residue_eq_zero_iff]
    exact ham
  have hinj := algebraicIndependent_iff_injective_aeval.mp hs.1
  have htrans : Transcendental (Algebra.adjoin F (Set.range z)) b := by
    intro halg
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker] at hc
    have hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R := F) z).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨g, hg⟩ := hc2
    have h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0 := by
      rw [← hfz]
      change MvPolynomial.aeval (fun i => f (z i)) g = 0
      rw [← MvPolynomial.comp_aeval_apply]
      change f ((MvPolynomial.aeval z).toRingHom g) = 0
      rw [hg]
      exact hc
    have hg0 : g = 0 := hinj (by rw [h0, map_zero])
    rw [Ideal.mem_bot]
    apply Subtype.ext
    rw [← hg, hg0, map_zero]
    rfl
  have hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z) :=
    AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩
  have hopt' := hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p)))
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))
  have hc1 := hopt'.cardinalMk_le_trdeg
  rw [← hs.cardinalMk_eq_trdeg] at htr
  have hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s := hc1.trans htr
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hle2
  haveI := Fintype.ofFinite s
  have := Fintype.card_le_of_embedding e
  rw [Fintype.card_option] at this
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosed

section

@[expose] public section

open IsLocalRing NumberField

namespace GlobalTheory.PointAlg

theorem trdeg_le_of_hom_algClosure (X Y Z : Type) [Field X] [Field Y] [Field Z] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* AlgebraicClosure Z) (e : Y →+* Z) (he : Function.Surjective e) :
    Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ Y := by
  letI : Algebra ℚ Z := (e.comp (algebraMap ℚ Y)).toAlgebra
  have h1 : Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ (AlgebraicClosure Z) :=
    trdeg_le_of_injective f.toRatAlgHom f.injective
  have h2 : Algebra.trdeg ℚ Z ≤ Algebra.trdeg ℚ Y :=
    trdeg_le_of_surjective e.toRatAlgHom he
  have h3 := trdeg_add_eq ℚ Z (A := AlgebraicClosure Z)
  rw [trdeg_eq_zero (R := Z) (A := AlgebraicClosure Z), add_zero] at h3
  exact h1.trans (h3.ge.trans h2)

theorem closed_point_of_values (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R]
    [IsLocalRing R] [Field K] (b : F →+* A) (hb : b.EssFiniteType) (ψ : A →+* R) (hψ : GlobalTheory.TChart.IsComplAt ψ)
    (ev : R →+* K) (k₀ : Subfield K) (hk : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)))
    (hev : ∀ a, ev (ψ a) ∈ k₀) : (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  obtain ⟨j⟩ := hk
  obtain ⟨-, -, -, hmap, hres⟩ := hψ
  set q : Ideal A := (maximalIdeal R).comap ψ with hq
  haveI hqp : q.IsPrime := Ideal.comap_isPrime ψ _
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := fun y => by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let Φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  have hΦ : ∀ a, Φ (algebraMap A L a) = ψ a := fun a => IsLocalization.lift_eq hu a
  have hne : ∀ a, IsUnit (ψ a) → ev (ψ a) ≠ 0 := fun a h => (h.map ev).ne_zero
  have hΦk : ∀ x, ev (Φ x) ∈ k₀ := by
    intro x
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg (fun t => ev (Φ t)) h
    simp only [map_mul, hΦ] at h2
    rw [eq_div_of_mul_eq (hne _ (hu s)) h2]
    exact k₀.div_mem (hev _) (hev _)
  haveI : IsLocalHom Φ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg Φ h
    simp only [map_mul, hΦ] at h2
    have ha : IsUnit (ψ a) := h2 ▸ hx.mul (hu s)
    have ha' : a ∈ q.primeCompl := fun h => (mem_maximalIdeal _).mp h ha
    have := IsLocalization.map_units L ⟨a, ha'⟩
    simp only at h
    exact isUnit_of_mul_isUnit_left (h ▸ this)
  have hsurj : Function.Surjective (ResidueField.map Φ) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    obtain ⟨a, s, hs, h⟩ := hres r
    rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at h
    refine ⟨residue L (algebraMap A L a) / residue L (algebraMap A L s), ?_⟩
    rw [map_div₀, ResidueField.map_residue, ResidueField.map_residue, hΦ, hΦ, ← h]
    exact mul_div_cancel_right₀ _ (hs.map (residue R)).ne_zero
  let g : L →+* AlgebraicClosure (ResidueField R) := j.comp ((ev.comp Φ).codRestrict k₀ hΦk)
  haveI hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have hE : ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).EssFiniteType := by
    refine RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp ?_ hb) ?_
    · exact RingHom.essFiniteType_algebraMap.mpr inferInstance
    · exact RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization L q.primeCompl)
  letI : Algebra ℚ L := ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).toAlgebra
  have hmax : RingHom.ker g = maximalIdeal L :=
    GlobalTheory.eq_maximalIdeal_of_trdeg_le ℚ L hE _ hP
      (trdeg_le_of_hom_algClosure _ _ _
        (IsFractionRing.lift (K := FractionRing (L ⧸ RingHom.ker g)) (RingHom.kerLift_injective g))
        (ResidueField.map Φ) hsurj)
  have h0 : ∀ r ∈ maximalIdeal R, ev r = 0 := by
    have : maximalIdeal R ≤ RingHom.ker ev := by
      rw [← hmap, Ideal.map_le_iff_le_comap]
      intro a ha
      have h1 : algebraMap A L a ∈ RingHom.ker g := by
        rw [hmax]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q a).mpr ha
      rw [RingHom.mem_ker] at h1
      have h2 := congrArg Subtype.val (j.injective (h1.trans (map_zero j).symm))
      change ev (Φ (algebraMap A L a)) = 0 at h2
      rw [hΦ] at h2
      exact h2
    exact fun r hr => this hr
  refine ⟨h0, fun r => ?_⟩
  obtain ⟨a, s, hs, h⟩ := hres r
  have h2 := h0 _ h
  rw [map_sub, map_mul, sub_eq_zero] at h2
  rw [eq_div_of_mul_eq (hne _ hs) h2]
  exact k₀.div_mem (hev _) (hev _)

end GlobalTheory.PointAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.closedPoint_of_values_in_small_algClosed : ∀ (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Field K] (b : F →+* A), b.EssFiniteType → ∀ ψ : A →+* R, GlobalTheory.TChart.IsComplAt ψ → ∀ (ev : R →+* K) (k₀ : Subfield K), Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → (∀ a, ev (ψ a) ∈ k₀) → (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  first | exact @GlobalTheory.PointAlg.closed_point_of_values | exact GlobalTheory.PointAlg.closed_point_of_values | (intros; apply GlobalTheory.PointAlg.closed_point_of_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.canon_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn
  obtain ⟨ε', τ₀, hε', hFB, hTau⟩ := GlobalTheory.T.canonicalFamily_periods_in_coordinates Xo c φ R hB C Cn
  refine ⟨Cn.N, fun k => Cn.ψ (MvPolynomial.X k), ε', τ₀, fun i => Cn.bd i, ?_, fun k => Cn.tor k, hTau, ?_⟩
  · intro i
    rw [hε', Cn.cone i]
  · intro K _ _ ev k₀ hk₀ hemb hsep
    obtain ⟨h1, h2, h3⟩ := hsep
    have hbase : ∀ a, ev ((Cn.ψ.comp MvPolynomial.C) a) ∈ k₀ :=
      GlobalTheory.T.canonicalFamily_base_value_mem_descended_point Cn.L C.P.D.toPre C.P.oD (Cn.ψ.comp MvPolynomial.C) (fun k => Cn.ψ (MvPolynomial.X k))
        (fun k => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) Cn.e Cn.data K ev k₀ hk₀ h2
    have htor := h3 Cn.L.W (Cn.ψ.comp MvPolynomial.C) hFB hbase
    have hX : ∀ k, ev (Cn.ψ (MvPolynomial.X k)) ∈ k₀ := by
      rintro (i | i)
      · have := h1 i
        simp only at this
        rw [this]; exact k₀.zero_mem
      · exact htor i
    have hall : ∀ a : MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W, ev (Cn.ψ a) ∈ k₀ := by
      intro a
      induction a using MvPolynomial.induction_on with
      | C a => exact hbase a
      | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact k₀.add_mem hp hq
      | mul_X p k hp => rw [map_mul, map_mul]; exact k₀.mul_mem hp (hX k)
    have hft : ((MvPolynomial.C : Cn.L.W →+* MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W).comp Cn.L.b).EssFiniteType := by
      refine RingHom.EssFiniteType.comp Cn.L.ft ?_
      exact (RingHom.FiniteType.essFiniteType (by
        rw [← MvPolynomial.algebraMap_eq]
        exact RingHom.finiteType_algebraMap.mpr inferInstance))
    exact GlobalTheory.T.closedPoint_of_values_in_small_algClosed c.F (MvPolynomial (Fin C.m ⊕ Fin Cn.N) Cn.L.W) R K (MvPolynomial.C.comp Cn.L.b) hft Cn.ψ Cn.compl
      ev k₀ hemb hall
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), HasRigidCoords C := by
  first | exact @GlobalTheory.UCanon.canon_hasRigidCoords | exact GlobalTheory.UCanon.canon_hasRigidCoords | (intros; apply GlobalTheory.UCanon.canon_hasRigidCoords <;> assumption)
end
end
