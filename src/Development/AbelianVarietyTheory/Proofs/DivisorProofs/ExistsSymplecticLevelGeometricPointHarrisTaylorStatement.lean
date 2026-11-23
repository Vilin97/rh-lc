module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGeometricFibre
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternating

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add (f := _), Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternatingStatement

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lattice_map_mod_of_perfect_alternating : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  first | (exact @GlobalTheory.exists_lattice_map_mod_of_perfect) | (exact GlobalTheory.exists_lattice_map_mod_of_perfect) | (intros; apply GlobalTheory.exists_lattice_map_mod_of_perfect  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CycLift

open Polynomial

theorem exists_injective_hom {n : ℕ} (hn : n ≠ 0) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    {u : V} (hu : IsPrimitiveRoot u n) (hnV : IsUnit (n : V)) :
    ∃ f : cycAway n →+* V, Function.Injective f ∧ f (zetaAway n) = u := by
  have hp := Nat.pos_of_ne_zero hn
  let L := FractionRing V
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  haveI : CharZero L := charZero_of_injective_algebraMap hinj
  have hz : IsPrimitiveRoot (zetaAway n : ℂ) n := Complex.isPrimitiveRoot_exp n hn
  have hi : IsIntegral ℚ (zetaAway n : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway n : ℂ)}
  have hle : cycAway n ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K n)
  have huL : IsPrimitiveRoot (algebraMap V L u) n := hu.map_of_injective hinj
  have hr : algebraMap V L u ∈ (minpoly ℚ (zetaAway n : ℂ)).aroots L := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact huL.isRoot_cyclotomic hp
  let g : K →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨_, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway n : ℂ)) = algebraMap V L u :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨_, hr⟩
  let f₀ : cycAway n →+* L := g.toRingHom.comp (Subring.inclusion hle)
  have hf₀ : Function.Injective f₀ := g.toRingHom.injective.comp (Subring.inclusion_injective hle)
  have hζ : f₀ (zetaAway n) = algebraMap V L u := hg
  have hmem : ∀ x, f₀ x ∈ (algebraMap V L).range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨u, hζ.symm⟩
      · refine ⟨↑hnV.unit⁻¹, ?_⟩
        have e : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have e₁ := congrArg f₀ e
        rw [map_mul, map_natCast, map_one] at e₁
        have e₂ : (n : L) * algebraMap V L ↑hnV.unit⁻¹ = 1 := by
          rw [← map_natCast (algebraMap V L) n, ← map_mul, hnV.mul_val_inv, map_one]
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e₂) (e₂.trans e₁.symm)
    | zero => exact Set.mem_of_eq_of_mem (map_zero f₀) (zero_mem _)
    | one => exact Set.mem_of_eq_of_mem (map_one f₀) (one_mem _)
    | add x y hx hy ihx ihy => exact (map_add f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f₀ ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  let e := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ y, algebraMap V L (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨e.symm.toRingHom.comp (f₀.codRestrict _ hmem),
    e.symm.injective.comp (fun a b h => hf₀ (congrArg Subtype.val h)), hinj ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  exact hζ

end GlobalTheory.CycLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRoot

section

@[expose] public section

open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRootStatement

section

@[expose] public section

open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
  ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  first | (exact @GlobalTheory.CycLift.exists_hom_to_field) | (exact GlobalTheory.CycLift.exists_hom_to_field) | (intros; apply GlobalTheory.CycLift.exists_hom_to_field  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylor

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem exists_sympCond_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  intro p _ D R _ b N M e hM3 hModd hMp hMe hperf S t o K _ _ x
  have hM0 : 0 < M := by omega
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, x ≫ t = spMap β :=
    ⟨(Spec.preimage (x ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I, -⟩ := o.geom K x β hβ
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨L, hLker, hLonto, hLω⟩ := GlobalTheory.T.exists_lattice_map_mod_of_perfect_alternating D.La D.EF D.alt D.nondeg e M hperf hMe
  have hMK : IsUnit (M : K) := by simpa using (b.unit M hMp).map β
  have hprim : IsPrimitiveRoot ((I.ζ M : Kˣ) : K) M :=
    IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim M hM0 hMp)
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot M (by omega) K _ hprim hMK
  refine ⟨spMap β₀, fun a => I.ev M (L a), fun a c => by show I.ev M (L (a + c)) = I.ev M (L a) * I.ev M (L c); rw [map_add (f := _), I.add],
    fun a => (I.onto M hM0 hMp _).2 ⟨L a, rfl⟩, ?_⟩
  intro k _ _ x' β' z hx' hz
  obtain ⟨φ, rfl⟩ : ∃ φ : K →+* k, x' = spMap φ := ⟨(Spec.preimage x').hom, (Spec.map_preimage _).symm⟩
  have hβ' : β' = φ.comp β₀ := by
    have e2 : CommRingCat.ofHom β' = CommRingCat.ofHom (φ.comp β₀) :=
      Spec.map_injective (hx'.symm.trans (by simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]))
    exact congrArg CommRingCat.Hom.hom e2
  subst hβ'
  have hz' : z = Units.map φ.toMonoidHom (I.ζ M) := Units.ext (by simpa [hβ₀] using hz)
  subst hz'
  obtain ⟨β'', hβ''⟩ : ∃ β'' : R →+* k, (spMap φ ≫ x) ≫ t = spMap β'' :=
    ⟨(Spec.preimage ((spMap φ ≫ x) ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I', -⟩ := o.geom k (spMap φ ≫ x) β'' hβ''
  let h : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  have : Epi h.left := GlobalTheory.UPel.GeometricLevelExistence.epi_spMap_field φ
  have : Epi h := Over.epi_of_epi_left h
  change (∀ a, h ≫ I.ev M (L a) = 1 ↔ _) ∧ (∀ g : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ o.A, g ^ M = 1 →
      ∃ a, h ≫ I.ev M (L a) = g) ∧ ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        (h ≫ I.ev M (L a)) (h ≫ I.ev M (L c)) (unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)))
  have hPa : ∀ a b, h ≫ I.ev M (a + b) = (h ≫ I.ev M a) * (h ≫ I.ev M b) := fun a b => by
    rw [I.add, MonObj.comp_mul]
  have hP : ∀ a, h ≫ I.ev M a = 1 ↔ ∃ b, a = M • b := fun a => by
    rw [← I.ker M hM0 hMp a]
    constructor
    · intro e
      rw [← cancel_epi h, e, MonObj.comp_one]
    · intro e
      rw [e, MonObj.comp_one]
  have hQ : ∀ a, I'.ev M a = 1 ↔ ∃ b, a = M • b := I'.ker M hM0 hMp
  have hPQ : ∀ a, ∃ c, h ≫ I.ev M a = I'.ev M c := fun a => by
    have e : (h ≫ I.ev M a) ^ M = 1 := by
      rw [← MonObj.comp_pow, (I.onto M hM0 hMp (I.ev M a)).2 ⟨a, rfl⟩, MonObj.comp_one]
    obtain ⟨c, hc⟩ := (I'.onto M hM0 hMp _).1 e
    exact ⟨c, hc.symm⟩
  refine ⟨fun a => (hP (L a)).trans (hLker a), fun g hg => ?_, fun a c => ?_⟩
  · obtain ⟨c, rfl⟩ := (I'.onto M hM0 hMp g).1 hg
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UPel.GeometricLevelExistence.exists_eq_of_count M hM0 _ _ hPa (I'.add M) hP hQ hPQ c
    obtain ⟨a, y, rfl⟩ := hLonto x₀
    refine ⟨a, ?_⟩
    rw [← hx₀, hPa, (hP _).2 ⟨y, rfl⟩, _root_.mul_one]
  · have H := CommPairing.weilIs_pull globalFns_holds o.ab (LB.isLB_pull o.isLB _) h (I.isom M hM0 hMp (L a) (L c))
    have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn (I.ζ M ^ (2 * D.EF (L a) (L c)))) =
        unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)) := by
      obtain ⟨k₀, hk₀⟩ := hLω a c
      have hζM : I.ζ M ^ (M : ℤ) = 1 := by
        rw [zpow_natCast]
        exact (I.ζ_prim M hM0 hMp).pow_eq_one
      have hK : I.ζ M ^ (2 * D.EF (L a) (L c)) = I.ζ M ^ (2 * omegaStd a c) := by
        rw [hk₀, show (2 : ℤ) * (omegaStd a c + M * k₀) = 2 * omegaStd a c + M * (2 * k₀) by ring, zpow_add,
          zpow_mul (I.ζ M) (M : ℤ), hζM, one_zpow, _root_.mul_one]
      rw [hK, ← map_zpow]
      exact GlobalTheory.UPel.GeometricLevelExistence.unitOn_pull_spMap φ _
    rw [e] at H
    exact H

end GlobalTheory.HTSympCover
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  first | (exact @GlobalTheory.HTSympCover.exists_sympCond_geom) | (exact GlobalTheory.HTSympCover.exists_sympCond_geom) | (intros; apply GlobalTheory.HTSympCover.exists_sympCond_geom  <;> assumption)
end
end
