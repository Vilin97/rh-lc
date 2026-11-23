module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAlgebraMap

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial HomogeneousLocalization
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Desc.GrSpec

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}

def ring (hN : GradedFam c₀ N) : Subring F[X] where
  carrier := {p | ∀ k, p.coeff k ∈ N k}
  mul_mem' {p q} hp hq k := by
    rw [coeff_mul]
    refine Finset.sum_induction _ (· ∈ N k) (fun a b ha hb => hN.add k a ha b hb) (hN.zero k) ?_
    rintro ⟨i, j⟩ hij
    have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
    subst hij'
    exact hN.mul i j _ (hp i) _ (hq j)
  one_mem' k := by
    rw [coeff_one]
    split_ifs with h
    · subst h; exact hN.one
    · exact hN.zero k
  add_mem' {p q} hp hq k := by rw [coeff_add]; exact hN.add k _ (hp k) _ (hq k)
  zero_mem' k := by rw [coeff_zero]; exact hN.zero k
  neg_mem' {p} hp k := by
    rw [coeff_neg]
    have := hN.smul k (-1) _ (hp k)
    simpa using this

theorem monomial_mem (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) : monomial k b ∈ ring hN := by
  intro j
  rw [coeff_monomial_apply]
  split_ifs with h
  · subst h; exact hb
  · exact hN.zero j

def piece (hN : GradedFam c₀ N) (k : ℕ) : AddSubgroup (ring hN) where
  carrier := {p | ∀ j, j ≠ k → (p : F[X]).coeff j = 0}
  add_mem' {p q} hp hq j hj := by
    rw [Subring.coe_add, coeff_add, hp j hj, hq j hj, add_zero]
  zero_mem' j _ := by rw [Subring.coe_zero, coeff_zero]
  neg_mem' {p} hp j hj := by rw [Subring.coe_neg, coeff_neg, hp j hj, neg_zero]

theorem mem_piece_iff (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} :
    p ∈ piece hN k ↔ (p : F[X]) = monomial k ((p : F[X]).coeff k) := by
  constructor
  · intro hp
    ext j
    rw [coeff_monomial_apply]
    split_ifs with h
    · rw [h]
    · exact hp j (Ne.symm h)
  · intro hp j hj
    rw [hp, coeff_monomial_of_ne _ hj]

def hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : ring hN := ⟨monomial k b, monomial_mem hN hb⟩

@[simp] theorem coe_hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) :
    (hel hN k b hb : F[X]) = monomial k b := rfl

theorem hel_mem (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : hel hN k b hb ∈ piece hN k := by
  rw [mem_piece_iff, coe_hel, coeff_monomial_same]

theorem hel_ne_zero (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) (h : b ≠ 0) : hel hN k b hb ≠ 0 := by
  intro e
  have := congrArg (fun p : ring hN => (p : F[X]).coeff k) e
  simp at this
  exact h this

def comp (hN : GradedFam c₀ N) (k : ℕ) : ring hN →+ piece hN k where
  toFun p := ⟨⟨monomial k ((p : F[X]).coeff k), monomial_mem hN (p.2 k)⟩, by
    intro j hj; exact coeff_monomial_of_ne _ hj⟩
  map_zero' := by ext; simp
  map_add' p q := by ext; simp

theorem comp_eq_zero (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : (p : F[X]).coeff k = 0) : comp hN k p = 0 := by
  ext; simp [comp, h]

theorem comp_of_mem (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : p ∈ piece hN k) : (comp hN k p : ring hN) = p := by
  ext1; exact ((mem_piece_iff hN).1 h).symm

def dec (hN : GradedFam c₀ N) (p : ring hN) : DirectSum ℕ (fun k => piece hN k) :=
  ∑ k ∈ (p : F[X]).support, DirectSum.of (fun k => piece hN k) k (comp hN k p)

theorem dec_eq (hN : GradedFam c₀ N) (p : ring hN) (S : Finset ℕ) (hS : (p : F[X]).support ⊆ S) :
    dec hN p = ∑ k ∈ S, DirectSum.of (fun k => piece hN k) k (comp hN k p) := by
  refine Finset.sum_subset hS fun k _ hk => ?_
  rw [comp_eq_zero hN (notMem_support_iff.1 hk), map_zero]

def decHom (hN : GradedFam c₀ N) : ring hN →+ DirectSum ℕ (fun k => piece hN k) where
  toFun := dec hN
  map_zero' := by simp [dec]
  map_add' p q := by
    classical
    set S := (p : F[X]).support ∪ (q : F[X]).support ∪ ((p + q : ring hN) : F[X]).support
    rw [dec_eq hN _ S (fun x hx => Finset.mem_union_right _ hx),
      dec_eq hN p S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)),
      dec_eq hN q S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add (f := _), map_add (f := _)]

instance gradedMonoid (hN : GradedFam c₀ N) : SetLike.GradedMonoid (piece hN) where
  one_mem j hj := by
    change (1 : F[X]).coeff j = 0
    rw [coeff_one, if_neg hj]
  mul_mem i j a b ha hb := by
    rw [mem_piece_iff] at ha hb
    intro l hl
    rw [Subring.coe_mul, ha, hb, monomial_mul_monomial, coeff_monomial_of_ne _ hl]

instance gradedRing (hN : GradedFam c₀ N) : GradedRing (piece hN) :=
  { gradedMonoid hN with
    toDecomposition := DirectSum.Decomposition.ofAddHom (piece hN) (decHom hN)
      (by
        refine AddMonoidHom.ext fun p => Subtype.ext ?_
        change (((DirectSum.coeAddMonoidHom (piece hN)) (dec hN p) : ring hN) : F[X]) = p

        rw [dec, map_sum]
        simp only [DirectSum.coeAddMonoidHom_of]
        rw [AddSubmonoidClass.coe_finsetSum]
        exact (as_sum_support _).symm)
      (by
        refine DirectSum.addHom_ext fun k y => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
        change dec hN (y : ring hN) = DirectSum.of _ k y
        rw [dec_eq hN _ {k} (fun j hj => by
          by_contra h'
          exact (mem_support_iff.1 hj) (y.2 j (by simpa using h')))]
        rw [Finset.sum_singleton]
        congr 1
        exact Subtype.ext (comp_of_mem hN y.2)) }

section Frac


variable (F) in
def cL : F →+* FractionRing F[X] := (algebraMap F[X] (FractionRing F[X])).comp C

theorem cL_injective : Function.Injective (cL F) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp C_injective

def toL (hN : GradedFam c₀ N) : ring hN →+* FractionRing F[X] :=
  (algebraMap F[X] (FractionRing F[X])).comp (ring hN).subtype

theorem toL_injective (hN : GradedFam c₀ N) : Function.Injective (toL hN) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp Subtype.val_injective

variable (hN : GradedFam c₀ N) (P : Ideal (ring hN)) [P.IsPrime]

def liftAt : Localization.AtPrime P →+* FractionRing F[X] :=
  IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := toL hN) fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (toL_injective hN)).2 fun h => s.2 (h ▸ P.zero_mem))

def valL : AtPrime (piece hN) P →+* FractionRing F[X] :=
  (liftAt hN P).comp (algebraMap (AtPrime (piece hN) P) (Localization.AtPrime P))

theorem valL_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    valL hN P (mk g) = cL F (((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg) := by
  have hnum := (mem_piece_iff hN).1 g.num.2
  have hden := (mem_piece_iff hN).1 g.den.2
  have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
    intro h0
    apply g.den_mem
    have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
    rw [this]; exact P.zero_mem
  change liftAt hN P (mk g).val = _
  rw [val_mk, Localization.mk_eq_mk', liftAt, IsLocalization.lift_mk'_spec]
  change algebraMap F[X] _ ((g.num : ring hN) : F[X]) =
    algebraMap F[X] _ ((g.den : ring hN) : F[X]) * algebraMap F[X] _ (C _)
  rw [← map_mul]
  congr 1
  rw [hnum, hden, coeff_monomial_same, coeff_monomial_same, monomial_mul_C, mul_div_cancel₀ _ hs]


variable (F) in
def eqR : F ≃+* (cL F).range :=
  RingEquiv.ofBijective (cL F).rangeRestrict
    ⟨fun a b h => cL_injective (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

def valR : AtPrime (piece hN) P →+* (cL F).range :=
  (valL hN P).codRestrict (cL F).range fun y => by
    obtain ⟨g, rfl⟩ := mk_surjective y
    exact ⟨_, (valL_mk hN P g).symm⟩

def psiAt : AtPrime (piece hN) P →+* F := (eqR F).symm.toRingHom.comp (valR hN P)

theorem cL_psiAt (y : AtPrime (piece hN) P) : cL F (psiAt hN P y) = valL hN P y :=
  congrArg Subtype.val ((eqR F).apply_symm_apply (valR hN P y))

theorem psiAt_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    psiAt hN P (mk g) = ((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg :=
  cL_injective (by rw [cL_psiAt, valL_mk])

end Frac

section Scheme

variable (hN : GradedFam c₀ N)

instance isPrime_point (x : Proj (piece hN)) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def gen {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : Proj (piece hN) :=
  ⟨⊥, Ideal.isPrime_bot, fun h => hel_ne_zero hN hb h0 (by
    have : hel hN k b hb ∈ HomogeneousIdeal.irrelevant (piece hN) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (piece hN) (hel_mem hN k b hb) (by omega)]
    exact h this)⟩

theorem isIntegral {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : IsIntegral (Proj (piece hN)) := by
  have hred : IsReduced (Proj (piece hN)) := by
    have (x : Proj (piece hN)) : _root_.IsReduced ((Proj (piece hN)).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum (piece hN) := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime (piece hN) x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' (piece hN) x') (Proj.stalkIso' (piece hN) x').injective
    exact isReduced_of_isReduced_stalk _
  have hcl : closure ({gen hN hk hb h0} : Set (ProjectiveSpectrum (piece hN))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure (piece hN) (gen hN hk hb h0) y).1 (by
      show (⊥ : HomogeneousIdeal (piece hN)) ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum (piece hN)) := by
    refine (irreducibleSpace_def _).2 ?_
    rw [Set.top_eq_univ, ← hcl]
    exact (isIrreducible_singleton (x := gen hN hk hb h0)).closure
  have : IrreducibleSpace (Proj (piece hN)) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def toZero : R →+* piece hN 0 where
  toFun r := ⟨⟨C (c₀ r), by
      have : c₀ r * 1 ∈ N 0 := hN.smul 0 r 1 hN.one
      rw [mul_one] at this
      exact monomial_mem hN (k := 0) this⟩, by
    intro j hj; simp [coeff_C, hj]⟩
  map_one' := by ext1; ext1; simp
  map_mul' a b := by ext1; ext1; simp
  map_zero' := by ext1; ext1; simp
  map_add' a b := by ext1; ext1; simp

def Dp (k : ℕ) (b : F) : (Proj (piece hN)).Opens := by
  classical exact if hb : b ∈ N k then Proj.basicOpen (piece hN) (hel hN k b hb) else ⊥

theorem Dp_of_mem {k : ℕ} {b : F} (hb : b ∈ N k) : Dp hN k b = Proj.basicOpen (piece hN) (hel hN k b hb) := by
  rw [Dp, dite_eq_left hb]

def psi [IsIntegral (Proj (piece hN))] : (Proj (piece hN)).functionField →+* F :=
  (psiAt hN _).comp (Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))).toRingHom

theorem psi_algebraMap [IsIntegral (Proj (piece hN))] (x : Proj (piece hN)) (w : (Proj (piece hN)).presheaf.stalk x) :
    psi hN (algebraMap _ _ w) = psiAt hN _ (Proj.stalkIso' (piece hN) x w) := by
  obtain ⟨g, hg⟩ := mk_surjective (Proj.stalkIso' (piece hN) x w)
  have hw : w = (Proj.stalkIso' (piece hN) x).symm (mk g) :=
    ((Proj.stalkIso' (piece hN) x).symm_apply_apply w).symm.trans (congrArg _ hg.symm)
  subst hw
  have hsp : genericPoint (Proj (piece hN)) ⤳ x := genericPoint_specializes x
  have hle : (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ _).2 (specializes_iff_mem_closure.1 hsp)
  have key : Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))
      ((Proj (piece hN)).presheaf.stalkSpecializes hsp ((Proj.stalkIso' (piece hN) x).symm (mk g))) =
      mk (⟨g.deg, g.num, g.den, fun hy => g.den_mem (hle hy)⟩ :
        NumDenSameDeg (piece hN) (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl) := by
    erw [Proj.stalkIso'_symm_mk, TopCat.Presheaf.germ_stalkSpecializes_apply, Proj.stalkIso'_germ]
    rfl
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.stalkSpecializes hsp _)) = _
  rw [key, RingEquiv.apply_symm_apply, psiAt_mk, psiAt_mk]

end Scheme

end GlobalTheory.Desc.GrSpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctions

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GrSpec

open Polynomial HomogeneousLocalization

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)

theorem coe_hel_pow {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) :
    ((hel hN k b hb ^ n : ring hN) : F[X]) = monomial (k * n) (b ^ n) := by
  rw [SubmonoidClass.coe_pow, coe_hel, monomial_pow]

theorem hel_pow_mem {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : hel hN k b hb ^ n ∈ piece hN (k * n) := by
  have := SetLike.pow_mem_graded n (hel_mem hN k b hb)
  rwa [smul_eq_mul, mul_comm] at this

theorem isUnit_mk_iff (P : Ideal (ring hN)) [P.IsPrime] (g : NumDenSameDeg (piece hN) P.primeCompl) :
    IsUnit (mk g : AtPrime (piece hN) P) ↔ (g.num : ring hN) ∉ P := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem affine {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) : IsAffineOpen (Dp hN k b) := by
  rw [Dp_of_mem hN hb]
  exact Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)

theorem cover (z : Proj (piece hN)) : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp hN k b := by
  classical
  obtain ⟨y, hy, hyz⟩ := Set.not_subset.1 z.not_irrelevant_le
  have : ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal := by
    by_contra hc
    push_neg at hc
    apply hyz
    rw [← DirectSum.sum_support_decompose (piece hN) y]
    exact Ideal.sum_mem _ fun j _ => hc j
  obtain ⟨j, hj⟩ := this
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hj
    have : (DirectSum.decompose (piece hN) y 0 : ring hN) = 0 := by
      rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy
    rw [this]; exact zero_mem _
  set c := DirectSum.decompose (piece hN) y j
  have hb : ((c : ring hN) : F[X]).coeff j ∈ N j := (c : ring hN).2 j
  refine ⟨j, by omega, _, hb, ?_⟩
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen]
  have : hel hN j _ hb = (c : ring hN) := Subtype.ext ((mem_piece_iff hN).1 c.2).symm
  rw [this]; exact hj

theorem ideal_gen [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) :
    (genericPoint (Proj (piece hN))).asHomogeneousIdeal = ⊥ :=
  le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2
    (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))

theorem genMem [IsIntegral (Proj (piece hN))] (h : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) {k : ℕ} {b : F} (hb : b ∈ N k) :
    genericPoint (Proj (piece hN)) ∈ Dp hN k b ↔ b ≠ 0 := by
  obtain ⟨k', hk', b', hb', h0'⟩ := h
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']
  change ¬ (hel hN k b hb = 0) ↔ _
  rw [not_iff_not, Subtype.ext_iff]
  simp

theorem hel_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k} (n : ℕ)
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : hel hN k b hb ^ n ∉ z.asHomogeneousIdeal.toIdeal :=
  fun h => hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

theorem ne_zero_of_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k}
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : b ≠ 0 := by
  rintro rfl
  apply hz
  have : hel hN k 0 hb = 0 := Subtype.ext (by simp)
  rw [this]; exact zero_mem _

theorem mem [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (z : Proj (piece hN))
    (hz : z ∈ Dp hN k b) {l : ℕ} {a : F} (ha : a ∈ N l) :
    z ∈ Dp hN l a ↔ ∃ v, UnitAt z v ∧ psi hN v = a ^ k / b ^ l := by
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen] at hz
  rw [Dp_of_mem hN ha, Proj.mem_basicOpen]
  have hfz := hel_notMem hN l hz
  have hb0 := ne_zero_of_notMem hN hz
  constructor
  · intro hg
    let nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl :=
      ⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩
    refine ⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩
    · exact ((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm
    · refine (psi_algebraMap hN z _).trans ?_
      erw [RingEquiv.apply_symm_apply]
      rw [psiAt_mk]
      simp only [nd, coe_hel_pow, coeff_monomial, Finsupp.single_apply, mul_comm k l, ↓reduceIte]
  · rintro ⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg
    rw [psi_algebraMap] at hv
    obtain ⟨g, hg'⟩ := mk_surjective (Proj.stalkIso' (piece hN) z w)
    rw [← hg', psiAt_mk] at hv
    have hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal) := by
      rw [hg']; exact hwu.map (Proj.stalkIso' (piece hN) z)
    rw [isUnit_mk_iff] at hu
    have hnum := (mem_piece_iff hN).1 g.num.2
    have hden := (mem_piece_iff hN).1 g.den.2
    have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
      intro h0
      apply g.den_mem
      have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
      rw [this]; exact zero_mem _
    have key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN) := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial,
        monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]
      congr 1
      rw [div_eq_div_iff hs (pow_ne_zero _ hb0)] at hv
      exact hv
    have : (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal := by
      rw [key]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
    · exact hu h
    · exact hfz h

def fracAt {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F} (ha : a ∈ N (k * m)) (x : Proj (piece hN))
    (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) : NumDenSameDeg (piece hN) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨k * m, ⟨hel hN (k * m) a ha, hel_mem hN _ _ ha⟩, ⟨_, hel_pow_mem hN hb m⟩, hel_notMem hN m hx⟩

theorem psi_fracAt [IsIntegral (Proj (piece hN))] {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F}
    (ha : a ∈ N (k * m)) (x : Proj (piece hN)) (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) :
    psi hN (algebraMap ((Proj (piece hN)).presheaf.stalk x) _
      ((Proj.stalkIso' (piece hN) x).symm (mk (fracAt hN hb m ha x hx)))) = a / b ^ m := by
  refine (psi_algebraMap hN x _).trans ?_
  erw [RingEquiv.apply_symm_apply]
  rw [psiAt_mk]
  simp only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, Finsupp.single_eq_same]

theorem ringChar [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (hb0 : b ≠ 0) (u : F) :
    (∃ v, (∀ z ∈ Dp hN k b, RegAt z v) ∧ psi hN v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m := by
  have h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0 := ⟨k, hk, b, hb, hb0⟩
  have hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b := (genMem hN h1 hb).2 hb0
  rw [Dp_of_mem hN hb] at hgen ⊢
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := exists_fnOf_eq hgen hv
    obtain ⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by
      refine ⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩
      rw [← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]
      exact (Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s
    obtain ⟨nd, rfl⟩ := mk_surjective y
    obtain ⟨m, hm⟩ := nd.den_mem
    have hdeg : nd.deg = k * m := by
      have hne : (nd.den : ring hN) ≠ 0 := by
        rw [← hm]; exact pow_ne_zero _ (hel_ne_zero hN hb hb0)
      exact DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne
    refine ⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩
    change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen
      (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _
    erw [Proj.stalkIso'_germ]
    have key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤
        (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl),
        psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) =
          ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg := by
      intro h
      exact psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩
    refine (key _).trans ?_
    rw [← hm, coe_hel_pow, coeff_monomial]
    have he : (Finsupp.single (k * m) (b ^ m)) nd.deg = b ^ m := by
      rw [hdeg, Finsupp.single_eq_same]
    rw [he]
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans
      (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩

def gR : CommRingCat.of R ⟶ Γ(Proj (piece hN), ⊤) :=
  CommRingCat.ofHom ((fromZeroRingHom (piece hN) _).comp (toZero hN)) ≫ Proj.awayToSection (piece hN) 1 ≫
    (Proj (piece hN)).presheaf.map (homOfLE (Proj.basicOpen_one (piece hN)).ge).op

def pstr : Proj (piece hN) ⟶ Sp R := (Proj (piece hN)).toSpecΓ ≫ Spec.map (gR hN)

theorem sep : IsSeparated (pstr hN) := inferInstance

theorem const [IsIntegral (Proj (piece hN))] : (psi hN).comp (cst (pstr hN)) = c₀ := by
  ext r
  have hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1 := by
    rw [Proj.basicOpen_one]; trivial
  have e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN := by
    rw [pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  change psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r
  rw [e0]
  change psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge
    (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r
  rw [fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg
      (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _
  erw [Proj.stalkIso'_germ]
  refine (psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_
  · exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)
  · simp [toZero]

end GlobalTheory.Desc.GrSpec

namespace GlobalTheory.Desc

theorem exists_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F),
    GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R)
      (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  intro R F _ _ _ c₀ N hN h
  obtain ⟨k₀, hk₀, b₀, hb₀, h₀⟩ := h
  haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀
  refine ⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩
  exact
    { sep := GrSpec.sep hN
      const := GrSpec.const hN
      affine := fun k hk b hb => GrSpec.affine hN hk hb
      cover := GrSpec.cover hN
      gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb
      ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u
      mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }

end GlobalTheory.Desc
end
end
end
